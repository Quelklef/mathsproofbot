from functools import wraps
from typing import *
import enum

from prop import Prop, PropKind
from pretty import *
from util import indent, find, share


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
    text = f"prove <{self.claim}> via {self.rule}"
    if self.assumption:
      text = f'assuming <{self.assumption}>, ' + text
    if self.subproofs:
      text += ':\n'
      subtext = '\n'.join(subproof.pretty for subproof in self.subproofs)
      text += indent(subtext, '|   ')
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

def find_proof(
  prop: Prop,
  assumptions: List[Prop],
  size: int,
):
  # TODO: the output of the following reveals that this doesn't
  #       seem to actaully be breadth-first
  # print('\t'.join([str(asm) for asm in assumptions]))
  # input()

  if size <= 0:
    return None

  searchers = (
    REITERATION,
    AND_INTRO,
    AND_ELIM,
    OR_INTRO,
    OR_ELIM,
    IMPLIES_INTRO,
    IMPLIES_ELIM,
    IFF_INTRO,
    IFF_ELIM,
    BOTTOM_INTRO,
    NOT_INTRO,
    NOT_ELIM,
  )

  for searcher in searchers:
    result = searcher(prop, assumptions, size)
    if result is not None:
      return result

def requires_kind(kind):
  def decorator(function):
    @wraps(function)
    def wrapper(prop, assumptions, size):
      if prop.kind != kind:
        return None
      else:
        return function(prop, assumptions, size)
    return wrapper
  return decorator

def REITERATION(prop, assumptions, size):

  if size != 1:
    return None

  for known in assumptions:
    if known == prop:
      return Proof(
        subproofs = [],
        claim     = prop,
        rule      = ProofRule.REITERATION,
      )

@requires_kind(PropKind.AND)
def AND_INTRO(prop, assumptions, size):

  if size < 3:
    return None

  for lsize, rsize in share(size - 1, 2):
    left_proof = find_proof(prop.left, assumptions, lsize)
    right_proof = find_proof(prop.right, assumptions, rsize)

  if None in [left_proof, right_proof]:
    return None

  return Proof(
    subproofs = [left_proof, right_proof],
    claim     = prop,
    rule      = ProofRule.AND_INTRO,
  )

# TODO
def AND_ELIM(prop, assumptions, size):

  if size != 1:
    return None

  and_props = (prop for prop in assumptions if prop.kind == PropKind.AND)
  is_sufficient = lambda and_prop: prop in [and_prop.left, and_prop.right]
  sufficients = filter(is_sufficient, and_props)
  for suff in sufficients:
    suff_proof = Proof.reiteration(suff)
    return Proof(
      subproofs = [suff_proof],
      claim = prop,
      rule = ProofRule.AND_ELIM,
    )

@requires_kind(PropKind.OR)
def OR_INTRO(prop, assumptions, size):

  if size < 3:
    return None

  for lsize, rsize in share(size - 1, 2):
    left_proof = find_proof(prop.left, assumptions, lsize)
    right_proof = find_proof(prop.right, assumptions, rsize)

    if [left_proof, right_proof] == [None, None]:
      return None

    proof = next(proof for proof in (left_proof, right_proof) if proof is not None)

    return Proof(
      subproofs = [proof],
      claim = prop,
      rule = ProofRule.OR_INTRO,
    )

# TODO
def OR_ELIM(prop, assumptions, size):

  if size < 3:
    return None

  or_props = (prop for prop in assumptions if prop.kind == PropKind.OR)

  for or_prop in or_props:

    left_implies_this = Prop(PropKind.IMPLIES, or_prop.left, prop)
    right_implies_this = Prop(PropKind.IMPLIES, or_prop.right, prop)

    for lit_size, rit_size in share(size - 2, 2):
      lit_proof = find_proof(left_implies_this, assumptions, lit_size)
      rit_proof = find_proof(right_implies_this, assumptions, rit_size)

      if None not in [lit_proof, rit_proof]:
        return Proof(
          subproofs = [lit_proof, rit_proof],
          claim     = prop,
          rule      = ProofRule.OR_ELIM,
        )

@requires_kind(PropKind.IMPLIES)
def IMPLIES_INTRO(prop, assumptions, size):

  if size < 3:
    return None

  inner_proof = find_proof(prop.right, assumptions + [prop.left], size - 2)

  if inner_proof is not None:
    return Proof(
      subproofs = [Proof.wrap(inner_proof, assumption=prop.left)],
      claim     = prop,
      rule      = ProofRule.IMPLIES_INTRO,
    )

# TODO
def IMPLIES_ELIM(prop, assumptions, size):

  if size < 3:
    return None

  implies_props = (prop for prop in assumptions if prop.kind == PropKind.IMPLIES)
  implies_this = (implies_prop for implies_prop in implies_props if implies_prop.right == prop)
  for implies_prop in implies_this:
    implies_proof = Proof.reiteration(implies_prop)
    antecedent_proof = find_proof(implies_prop.left, assumptions, size - 2)
    if antecedent_proof is not None:
      return Proof(
        subproofs = [implies_proof, antecedent_proof],
        claim     = prop,
        rule      = ProofRule.IMPLIES_ELIM,
      )

@requires_kind(PropKind.IFF)
def IFF_INTRO(prop, assumptions, size):

  if size < 3:
    return None

  ltr_prop = Prop(PropKind.IMPLIES, prop.left, prop.right)
  rtl_prop = Prop(PropKind.IMPLIES, prop.right, prop.left)

  for ltr_size, rtl_size in share(size - 1, 2):
    ltr_proof = find_proof(ltr_prop, assumptions, ltr_size)
    rtl_proof = find_proof(rtl_prop, assumptions, rtl_size)
    if None not in [ltr_proof, rtl_proof]:
      return Proof(
        subproofs = [ltr_proof, rtl_proof],
        claim     = prop,
        rule      = ProofRule.IFF_INTRO,
      )

# TODO
def IFF_ELIM(prop, assumptions, size):

  if size < 3:
    return None

  iff_props = filter(lambda p: p.kind == PropKind.IFF, assumptions)
  has_this = filter(lambda p: prop in [p.left, p.right], iff_props)
  for iff_prop in has_this:
    iff_proof = Proof.reiteration(iff_prop)
    need_to_prove = iff_prop.left if prop == iff_prop.right else iff_prop.right
    proof = find_proof(iff_prop.right, assumptions, size - 2)
    if proof is not None:
      return Proof(
        subproofs = [iff_proof, proof],
        claim     = prop,
        rule      = ProofRule.IFF_ELIM,
      )

# TODO
@requires_kind(PropKind.BOTTOM)
def BOTTOM_INTRO(bottom, assumptions, size):

  if size < 3:
    return None

  for prop in assumptions:
    prop_proof = Proof.reiteration(prop)
    if prop.kind == PropKind.NOT:
      unwrapped_prop = prop.contained
      unwrapped_proof = find_proof(unwrapped_prop, assumptions, size - 2)
      if unwrapped_proof is not None:
        return Proof(
          subproofs = [unwrapped_proof, prop_proof],
          claim     = bottom,
          rule      = ProofRule.BOTTOM_INTRO,
        )

    else:
      negated_prop = Prop(PropKind.NOT, prop)
      negated_prop_proof = find_proof(negated_prop, assumptions, size - 2)
      if negated_prop_proof is not None:
        return Proof(
          subproofs = [prop_proof, negated_prop_proof],
          claim     = bottom,
          rule      = ProofRule.BOTTOM_INTRO,
        )

@requires_kind(PropKind.NOT)
def NOT_INTRO(prop, assumptions, size):

  if size < 3:
    return None

  unwrapped_prop = prop.contained
  bottom_prop = Prop(PropKind.BOTTOM)
  bottom_proof = find_proof(bottom_prop, assumptions + [unwrapped_prop], size - 2)
  if bottom_proof is not None:
    subproof = Proof.wrap(bottom_proof, assumption=unwrapped_prop)
    return Proof(
      subproofs = [subproof],
      claim     = prop,
      rule      = ProofRule.NOT_INTRO,
    )

def NOT_ELIM(prop, assumptions, size):

  if size < 2:
    return None

  double_negated = Prop(PropKind.NOT, Prop(PropKind.NOT, prop))
  double_negated_proof = find_proof(double_negated, assumptions, size - 1)
  if double_negated_proof is not None:
    return Proof(
      subproofs = [double_negated_proof],
      claim     = prop,
      rule      = ProofRule.NOT_ELIM,
    )


# == # == # == #


def prove_proposition(prop):
  size = 1
  while True:
    proof = find_proof(prop, [], size)
    if proof is not None:
      return proof
    size += 1
