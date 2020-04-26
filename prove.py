from functools import wraps
from typing import *
import enum

from prop import Prop, PropKind
from pretty import *
from util import indent, find, iweave, icross


"""

This module is the most difficult module of the entire project.
It handles proving propositions, assuming that they are, in fact, valid.
(If they're not, the algorithm will run forever without terminating)

Before getting into the algorithm itself, let's just discuss how
we represent the proofs.

We'll begin with the proposition

  [(a -> b) & (b -> c)] -> (a -> c)

Our end goal will be to create a Fitch-style proof of this, which will
look along the lines of:

  | 1. (a -> b) & (b -> c)   [assumption]
  |---
  | | 2. a                   [assumption]
  | |---
  | | 3. a -> b              [&E:1]
  | | 4. b                   [->E:3,2]
  | | 5. b -> c              [&E:1]
  | | 6. c                   [->E:5,4]
  | 7. a -> c                [->I:2-6]
  8. [(a -> b) & (b -> c)]
       -> (a -> c)           [->I:1-7]

The final output won't look /exactly/ like this, but it will be close.

Anyway, that's our /final/ goal. First we need to lay down some
some foundations. In particular, we need to discuss how we'll be
representing proofs. For the majority of the program, the way
we represent proofs will NOT be akin to a Fitch-style proof.

Instead, it will be more like a tree. A proof of something will
be represented as an application of one of the logical rules; each
application will be encoded as the rule being applied along with the propositions
that the rule is applied to (and, recursively, their proofs, as well).

For example, if we assume Q, then a proof of Q & (Q | S) would look like:

  prove <Q & (Q | S)> via or-intro:
    prove <Q> via reiteration
    prove <Q | S> via and-intro:
      prove <Q> via reiteration
      prove <S> via reiteration

Note that all leaf nodes must be reiteration nodes.

We'll also need to be able to assume things, for instance to be able
to do proof-by-contradiction. We'll allow rules to assume propositions,
and will write the assumption right before the rule.
A proof of ~Q -> (Q -> S) would look like the following,
where the # sign denotes bottom:

  prove <~Q -> (Q -> S)> via implies-intro:
    assuming <~Q>, prove <Q -> S> via implies-intro:
      assuming <Q>, prove <S> via not-elim:
        prove <~~S> via bottom-elim:
          assuming <~S>, prove <#> via bottom-intro:
            prove <Q> via reiteration
            prove <~Q> via reiteration

this tree corresponds to the following Fitch-style proof:

  | 1. ~Q             [assumption]
  |---
  | | 2. Q            [assumption]
  | |---
  | | | 3. ~S         [assumption]
  | | |---
  | | | 4. #          [#I:1,2]
  | | 5. ~~S          [~I:3-4]
  | | 6. S            [~E:5]
  | 7. Q -> S         [->I:2-6]
  8. ~Q -> (Q -> S)   [->I:1-7]

Note that the two read very differently. Where the Fitch-style proof
kind of /builds up/ to its conclusion, the tree structure on the
other hand kind of /decomposes/ its conclusion. The Fitch-style proof
starts with what's known and repeatedly builds consequences
until we reach our goal. In the tree structure, we start with
our goal and recursively prove it using logical rules to break
it down into simpler statements.
If you're used to Fitch-style proofs, the tree structure may feel
like it's "inside out".

"""


class ProofRule(enum.Enum):
  REITERATION   = 'reiteration'

  OR_INTRO      = 'or-intro'
  OR_ELIM       = 'or-elim'
  AND_INTRO     = 'and-intro'
  AND_ELIM      = 'and-elim'
  NOT_INTRO     = 'not-intro'
  NOT_ELIM      = 'not-elim'
  BOTTOM_INTRO  = 'bottom-intro'
  BOTTOM_ELIM   = 'bottom-elim'
  IMPLIES_INTRO = 'implies-intro'
  IMPLIES_ELIM  = 'implies-elim'
  IFF_INTRO     = 'iff-intro'
  IFF_ELIM      = 'iff-elim'

  ASSUMPTION    = 'assumption'

  def __str__(self):
    return self.value

  @property
  def pretty(self):
    return {
      ProofRule.REITERATION   : 're',
      ProofRule.OR_INTRO      : pretty_OR + 'I',
      ProofRule.OR_ELIM       : pretty_OR + 'E',
      ProofRule.AND_INTRO     : pretty_AND + 'I',
      ProofRule.AND_ELIM      : pretty_AND + 'E',
      ProofRule.NOT_INTRO     : pretty_NOT + 'I',
      ProofRule.NOT_ELIM      : pretty_NOT + 'E',
      ProofRule.BOTTOM_INTRO  : pretty_BOTTOM + 'I',
      ProofRule.BOTTOM_ELIM   : pretty_BOTTOM + 'E',
      ProofRule.IMPLIES_INTRO : pretty_IMPLIES + 'I',
      ProofRule.IMPLIES_ELIM  : pretty_IMPLIES + 'E',
      ProofRule.IFF_INTRO     : pretty_IFF + 'I',
      ProofRule.IFF_ELIM      : pretty_IFF + 'E',
      ProofRule.ASSUMPTION    : 'as',
    }[self]


class Proof:

  """

  Represents a node in the proof tree. For instance, the tree

    assuming <S>, prove <Q | S> via disjunction-intro:
      observe <Q>
      observe <S>

  is reified as

    observe_Q_proof = Proof(
      claim = Prop(PropKind.NAME, 'Q'),
      rule = ProofRule.REITERATION,
    )

    observe_S_proof = Proof(
      claim = Prop(PropKind.NAME, 'S'),
      rule = ProofRule.REITERATION,
    )

    root_proof = Proof(
      assumption = Prop(PropKind.NAME, 'S'),
      subproofs = [
        observe_Q_proof,
        observe_S_proof,
      ],
      claim = parse('Q | S'),  # don't have to make the Prop manually
      rule = ProofRule.OR_INTRO,
    )

  """

  def __init__(
      self: 'Proof',
      *,
      assumption: Prop = None,
      subproofs: List['Proof'] = [],
      claim: Prop,
      rule: ProofRule,
    ) -> 'Proof':

    self.assumption = assumption
    self.subproofs = subproofs
    self.claim = claim
    self.rule = rule

  def __eq__(self, other):
    return (type(self) == type(other)
      and self.assumption == other.assumption
      and self.subproofs == other.subproofs
      and self.claim == other.claim
      and self.rule == other.rule)

  def __repr__(self):
    return f'<Proof of {self.claim}>'

  @property
  def pretty(self):
    stub = f"prove <{self.claim}> via {self.rule}"

    if self.assumption:
      stub = f'assuming <{self.assumption}>, ' + stub

    if not self.subproofs:
      return stub
    else:
      text = stub + ':\n'
      for subproof in self.subproofs:
        text += indent(subproof.pretty, '  ') + '\n'
      return text

  @staticmethod
  def reiteration(prop):
    return Proof(
      claim = prop,
      rule = ProofRule.REITERATION,
    )

  @staticmethod
  def wrap(proof, *, assumption):
    return Proof(
      assumption = assumption,
      subproofs  = proof.subproofs,
      claim      = proof.claim,
      rule       = proof.rule,
    )

def find_proofs(
  prop: Prop,
  assumptions: List[Prop],
):

  yield None

  yield from iweave(
    REITERATION   (prop, assumptions),
    AND_INTRO     (prop, assumptions),
    AND_ELIM      (prop, assumptions),
    OR_INTRO      (prop, assumptions),
    OR_ELIM       (prop, assumptions),
    IMPLIES_INTRO (prop, assumptions),
    IMPLIES_ELIM  (prop, assumptions),
    IFF_INTRO     (prop, assumptions),
    IFF_ELIM      (prop, assumptions),
    BOTTOM_INTRO  (prop, assumptions),
    NOT_INTRO     (prop, assumptions),
    NOT_ELIM      (prop, assumptions),
  )

def requires_kind(kind):
  def decorator(function):
    @wraps(function)
    def wrapper(prop, assumptions):
      if prop.kind != kind:
        yield from ()
      else:
        yield from function(prop, assumptions)
    return wrapper
  return decorator

def REITERATION(prop, assumptions):
  for known in assumptions:
    if known == prop:
      yield Proof(
        subproofs = [],
        claim     = prop,
        rule      = ProofRule.REITERATION,
      )

@requires_kind(PropKind.AND)
def AND_INTRO(prop, assumptions):
  left_proofs = find_proofs(prop.left, assumptions)
  right_proofs = find_proofs(prop.right, assumptions)
  for left_proof, right_proof in icross(left_proofs, right_proofs):
    if None in [left_proof, right_proof]:
      yield None
    else:
      yield Proof(
        subproofs = [left_proof, right_proof],
        claim     = prop,
        rule      = ProofRule.AND_INTRO,
      )

# TODO
def AND_ELIM(prop, assumptions):
  and_props = (prop for prop in assumptions if prop.kind == PropKind.AND)
  is_sufficient = lambda and_prop: prop in [and_prop.left, and_prop.right]
  sufficients = filter(is_sufficient, and_props)
  for suff in sufficients:
    suff_proof = Proof.reiteration(suff)
    yield Proof(
      subproofs = [suff_proof],
      claim = prop,
      rule = ProofRule.AND_INTRO,
    )

@requires_kind(PropKind.OR)
def OR_INTRO(prop, assumptions):
  left_proofs = find_proofs(prop.left, assumptions)
  right_proofs = find_proofs(prop.right, assumptions)
  for proof in iweave(left_proofs, right_proofs):
    if proof is None:
      yield None
    else:
      yield Proof(
        subproofs = [proof],
        claim = prop,
        rule = ProofRule.OR_INTRO,
      )

# TODO
def OR_ELIM(prop, assumptions):
  yield from ()

@requires_kind(PropKind.IMPLIES)
def IMPLIES_INTRO(prop, assumptions):
  antecedent = prop.left
  consequent = prop.right
  inner_assumptions = assumptions + [antecedent]
  consequent_proofs = find_proofs(consequent, inner_assumptions)
  for consequent_proof in consequent_proofs:
    if consequent_proof is None:
      yield None
    else:
      block = Proof.wrap(consequent_proof, assumption=antecedent)
      yield Proof(
        subproofs       = [block],
        claim   = prop,
        rule = ProofRule.IMPLIES_INTRO,
      )

# TODO
def IMPLIES_ELIM(prop, assumptions):
  implies_props = (prop for prop in assumptions if prop.kind == PropKind.IMPLIES)
  implies_this = (implies_prop for implies_prop in implies_props if implies_prop.right == prop)
  for implies_prop in implies_this:
    implies_proof = Proof.reiteration(implies_prop)
    antecedent_proofs = find_proofs(implies_prop.left, assumptions)
    for antecedent_proof in antecedent_proofs:
      if antecedent_proof is None:
        yield None
      else:
        yield Proof(
          subproofs = [implies_proof, antecedent_proof],
          claim     = prop,
          rule      = ProofRule.IMPLIES_ELIM,
        )

@requires_kind(PropKind.IFF)
def IFF_INTRO(prop, assumptions):
  ltr_prop = Prop(PropKind.IMPLIES, prop.left, prop.right)
  ltr_proofs = find_proofs(ltr_prop, assumptions)
  rtl_prop = Prop(PropKind.IMPLIES, prop.right, prop.left)
  rtl_proofs = find_proofs(rtl_prop, assumptions)
  for ltr_proof, rtl_proof in icross(ltr_proofs, rtl_proofs):
    if None in [ltr_proof, rtl_proof]:
      yield None
    else:
      yield Proof(
        subproofs       = [ltr_proof, rtl_proof],
        claim   = prop,
        rule = ProofRule.IFF_INTRO,
      )

# TODO
def IFF_ELIM(prop, assumptions):
  iff_props = filter(lambda p: p.kind == PropKind.IFF, assumptions)
  has_this = filter(lambda p: prop in [p.left, p.right], iff_props)

  for iff_prop in has_this:
    iff_proof = Proof.reiteration(iff_prop)
    need_to_prove = p.left if prop == p.right else p.right
    proofs = find_proofs(iff_prop.right, assumptions)
    for proof in proofs:
      if proof is None:
        yield None
      else:
        yield Proof(
          subproofs = [iff_proof, proof],
          claim     = prop,
          rule      = ProofRule.IFF_ELIM,
        )

# TODO
@requires_kind(PropKind.BOTTOM)
def BOTTOM_INTRO(bottom, assumptions):
  for prop in assumptions:
    prop_proof = Proof.reiteration(prop)
    if prop.kind == PropKind.NOT:
      unwrapped_prop = prop.contained
      unwrapped_proofs = find_proofs(unwrapped_prop, assumptions)
      for unwrapped_proof in unwrapped_proofs:
        if unwrapped_proof is None:
          yield None
        else:
          yield Proof(
            subproofs = [unwrapped_proof, prop_proof],
            claim     = bottom,
            rule      = ProofRule.BOTTOM_INTRO,
          )

    else:
      negated_prop = Prop(PropKind.NOT, prop)
      negated_prop_proofs = find_proofs(negated_prop, assumptions)
      for negated_prop_proof in negated_prop_proofs:
        if negated_prop_proof is None:
          yield None
        else:
          yield Proof(
            subproofs = [prop_proof, negated_prop_proof],
            claim     = bottom,
            rule      = ProofRule.BOTTOM_INTRO,
          )

@requires_kind(PropKind.NOT)
def NOT_INTRO(prop, assumptions):
  unwrapped_prop = prop.contained
  bottom_prop = Prop(PropKind.BOTTOM)
  bottom_proofs = find_proofs(bottom_prop, assumptions + [unwrapped_prop])
  for bottom_proof in bottom_proofs:
    if bottom_proof is None:
      yield None
    else:
      block = Proof.wrap(bottom_proof, assumption=unwrapped_prop)
      yield Proof(
        subproofs       = [block],
        claim   = prop,
        rule = ProofRule.NOT_INTRO,
      )

def NOT_ELIM(prop, assumptions):
  double_negated = Prop(PropKind.NOT, Prop(PropKind.NOT, prop))
  double_negated_proofs = find_proofs(double_negated, assumptions)
  for double_negated_proof in double_negated_proofs:
    if double_negated_proof is None:
      yield None
    else:
      yield Proof([double_negated_proof], prop, ProofRule.NOT_ELIM)


# == # == # == #


def prove_proposition(prop):
  proofs = find_proofs(prop, [])
  valid = (proof for proof in proofs if proof is not None)
  return next(valid)
