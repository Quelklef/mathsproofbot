from functools import wraps
from typing import *
import enum

from prop import Prop, PropKind
from pretty import *
from util import indent, find, share, other


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

  prove <Q & (Q | S)> via and-intro:
    prove <Q> via reiteration
    prove <Q | S> via or-intro:
      prove <Q> via reiteration

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


class ProofKind(enum.Enum):
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
      ProofKind.REITERATION   : 're',
      ProofKind.OR_INTRO      : pretty_OR + 'I',
      ProofKind.OR_ELIM       : pretty_OR + 'E',
      ProofKind.AND_INTRO     : pretty_AND + 'I',
      ProofKind.AND_ELIM      : pretty_AND + 'E',
      ProofKind.NOT_INTRO     : pretty_NOT + 'I',
      ProofKind.NOT_ELIM      : pretty_NOT + 'E',
      ProofKind.BOTTOM_INTRO  : pretty_BOTTOM + 'I',
      ProofKind.BOTTOM_ELIM   : pretty_BOTTOM + 'E',
      ProofKind.IMPLIES_INTRO : pretty_IMPLIES + 'I',
      ProofKind.IMPLIES_ELIM  : pretty_IMPLIES + 'E',
      ProofKind.IFF_INTRO     : pretty_IFF + 'I',
      ProofKind.IFF_ELIM      : pretty_IFF + 'E',
      ProofKind.ASSUMPTION    : 'as',
    }[self]


class Proof:

  """

  Represents a node in the proof tree. For instance, the tree

    assuming <S>, prove <Q | S> via disjunction-intro:
      prove <Q> via reiteration
      prove <S> via reiteration

  is reified as

    observe_Q_proof = Proof(
      claim = Prop(PropKind.NAME, 'Q'),
      kind = ProofKind.REITERATION,
    )

    observe_S_proof = Proof(
      claim = Prop(PropKind.NAME, 'S'),
      kind = ProofKind.REITERATION,
    )

    root_proof = Proof(
      assumption = Prop(PropKind.NAME, 'S'),
      subproofs = [
        observe_Q_proof,
        observe_S_proof,
      ],
      claim = parse('Q | S'),  # don't have to make the Prop manually
      kind = ProofKind.OR_INTRO,
    )

  """

  def __init__(
      self: 'Proof',
      *,
      assumption: Prop = None,
      subproofs: List['Proof'] = [],
      claim: Prop,
      kind: ProofKind,
    ) -> 'Proof':

    self.assumption = assumption
    self.subproofs = subproofs
    self.claim = claim
    self.kind = kind

  def __eq__(self, other):
    return (type(self) == type(other)
      and self.assumption == other.assumption
      and self.subproofs == other.subproofs
      and self.claim == other.claim
      and self.kind == other.kind)

  def __repr__(self):
    return f'<Proof of {self.claim}>'

  @property
  def pretty(self):
    text = f"prove <{self.claim}> via {self.kind}"
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
      kind = ProofKind.REITERATION,
    )

def find_proof(
  prop: Prop,
  assumptions: List[Prop],
  size: int,
  *,
  assuming: Optional[Prop] = None,
) -> Proof:

  """

  Search for a proof of the given proposition with the given size.
  If no proof of the given size [1] exists, returns None.

  - The 'prop' argument is the goal we're trying to prove.

  - The 'size' argument is the target size of the proof.

  - The 'assumptions' argument is a list of propositions which is what
    we have assumed in the proof up to now.

    So let's say we're part way through a proof, like this:

      prove <A -> (A & (A | A))> via implies-intro:
        assuming <A>, prove <A & (A | A)> via and-intro:
          prove <A> via reiteration
          prove <A | A> via ?? (WE ARE HERE)

    then what we have already assumed is <A>, so the 'assumptions'
    argument should be the list [Proof(ProofKind.NAME, 'A')].

 - The 'assuming' argument is similar to 'assumptions' but subtly
   different. If 'assuming' is not None, then it represents an
   assumption we're making ON the proof we're searching for.

   So if we're earlier on the same proof, say, here:

      prove <A -> (A & (A | A))> via implies-intro:
        assuming <A>, prove <A & (A | A)> via ?? (WE ARE HERE)

   then we would have that 'assumptions' is an empty list
   but 'assuming' is the proposition Proof(ProofKind.NAME, 'A')

  [1] The "size" of a proof is defined to be

    [number of rules] + [number of assumptions]

  Thus the size of e.g.

    assuming <Q>, prove <Q | Q> via disjunction-intro:
      prove <Q> via reiteration
      prove <Q> via reiteration

  is 5:
    +1 for "assuming <Q>"
    +1 for disjunction-intro
    +2 for 2x reiteration

  """

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

  if assuming:
    for searcher in searchers:
      proof = searcher(prop, assumptions + [assuming], size)
      if proof is not None:
        proof.assumption = assuming
        return proof

  else:
    for searcher in searchers:
      proof = searcher(prop, assumptions, size)
      if proof is not None:
        return proof

"""

Our proof-searching functions each look for a proof of
the given proposition that uses a particular kind. So
the function AND_ELIM will try to prove our proposition
by using an and-elim kind.

For instance, say we're trying to prove <Q | S>. If we
ask AND_ELIM to prove this, then it will try to prove it
using an and-elim, which it will to by first trying to
prove something of the form <[subproposition] & (Q | S)>;
if it is able to prove something of this form, then it will
return the proof

  prove <Q | S> via and-elim:
    prove <[subproposition] & (Q | S)> via [rule]:
      [subproofs]

Each function is expected to return a Proof object if it
is able to find a proof; otherwise, it will return None.

"""

def REITERATION(prop, assumptions, size):
  """
  Proofs of the form

    prove <[prop]> via reiteration

  """

  if size != 1:
    return None

  for known in assumptions:
    if known == prop:
      return Proof(
        subproofs = [],
        claim     = prop,
        kind      = ProofKind.REITERATION,
      )

"""

INTRO rules

All INTRO rules share some similarities.

1) For one, they will only work to prove propositions of a
certain kind: and-intro can only prove conjunctions; or-intro
can only prove disjunctions, etc.

2) Additionally, they all have minimum size constraints.
What I mean by this is that if we want to use, say, or-intro
to prove something, then we know that the resultant proof
will be of the form

  prove [proposition] via or-intro:
    prove [subproposition_1] via [rule_1]:
      ...
    prove [subproposition_2] via [rule_2]:
      ...

Note that the '...' does not designate a necessary existence of
grandchildren proofs. If the subproofs are reiterations,
then there will be no granchildren proofs.

The smallest possible proof that this can produce will come
about if both subproofs are reiterations. This looks like:

  prove [proposition] via or-intro:
    prove [subproposition_1] via reiteration
    prove [subproposition_2] via reiteration

This proof has a size of 3.

Thus, we know that an application of or-intro will ALWAYS produce
a proof with size 3 or greater. Thus, if OR_INTRO is called with
a size less than 3, we can immediately return None.

In general, all INTRO rules will have a minimum size due to
their form.

"""

def proofify(proof_kind: ProofKind):
  def decorator(function):

    @wraps(function)
    def wrapper(goal, assumption, size):
      subproofs = function(goal, assumption, size)

      if subproofs is None:
        return None

      return Proof(
        subproofs = subproofs,
        claim     = goal,
        kind      = proof_kind,
      )

    return wrapper
  return decorator

def min_size(min_size: int):
  def decorator(function):

    @wraps(function)
    def wrapper(goal, assumptions, size):
      if size < min_size:
        return None
      return function(goal, assumptions, size)

    return wrapper
  return decorator

def exact_size(required_size: int):
  def decorator(function):

    @wraps(function)
    def wrapper(goal, assumptions, size):
      if size != required_size:
        return None
      return function(goal, assumptions, size)

    return wrapper
  return decorator

def prop_kind(prop_kind: PropKind):
  def decorator(function):

    @wraps(function)
    def wrapper(goal, assumptions, size):
      if goal.kind != prop_kind:
        return None
      return function(goal, assumptions, size)

    return wrapper
  return decorator

@min_size(3)
@proofify(ProofKind.AND_INTRO)
@prop_kind(PropKind.AND)
def AND_INTRO(goal, assumptions, size):
  """
  Proofs of the form

    prove <[left] & [right]> via and-intro:
      prove <[left]> via [rule]: ...
      prove <[right]> via [rule]: ...

  """

  for lsize, rsize in share(size - 1, 2):
    lproof = find_proof(goal.left, assumptions, lsize)
    rproof = find_proof(goal.right, assumptions, rsize)

    subproofs = [lproof, rproof]
    if None not in subproofs:
      return subproofs

@min_size(2)
@proofify(ProofKind.OR_INTRO)
@prop_kind(PropKind.OR)
def OR_INTRO(goal, assumptions, size):
  """
  Proofs of the form

    prove <[left] | [right]> via or-intro:
      prove <[left]> via [rule]: ...

  or of the form

    prove <[left] | [right]> via or-intro:
      prove <[right]> via [rule]: ...

  """

  for lsize, rsize in share(size - 1, 2):
    lproof = find_proof(goal.left, assumptions, lsize)
    rproof = find_proof(goal.right, assumptions, rsize)
    if lproof is not None: return [lproof]
    if rproof is not None: return [rproof]

@min_size(3)
@proofify(ProofKind.IMPLIES_INTRO)
@prop_kind(PropKind.IMPLIES)
def IMPLIES_INTRO(goal, assumptions, size):
  """
  Proofs of the form

    prove <[left] -> [right]> via implies-intro:
      assuming <[left]>, prove <[right]> via [rule]: ...

  """
  subproof = find_proof(goal.right, assumptions, size - 2, assuming=goal.left)
  if subproof is not None:
    return [subproof]

@min_size(5)
@proofify(ProofKind.IFF_INTRO)
@prop_kind(PropKind.IFF)
def IFF_INTRO(goal, assumptions, size):
  """
  Proofs of the form

    prove <[left] <-> [right]> via iff-intro:
      assuming <[left]>, prove <[right]> via [rule]: ...
      assuming <[right]>, prove <[left]> via [rule]: ...

  """
  for ltr_size, rtl_size in share(size - 1, 2):
    ltr_subproof = find_proof(goal.right, assumptions, ltr_size, assuming=goal.left)
    rtl_subproof = find_proof(goal.left, assumptions, rtl_size, assuming=goal.right)
    subproofs = [ltr_subproof, rtl_subproof]
    if None not in subproofs:
      return subproofs

@min_size(3)
@proofify(ProofKind.NOT_INTRO)
@prop_kind(PropKind.NOT)
def NOT_INTRO(goal, assumptions, size):
  """
  Proofs of the form

    prove <~[prop]> via not-intro:
      assuming <[prop]>, prove <#> via [rule]: ...

  """
  unwrapped_goal = goal.contained
  subproof = find_proof(Prop(PropKind.BOTTOM), assumptions, size - 2, assuming=unwrapped_goal)
  if subproof is not None:
    return [subproof]

"""

All following proof generators, both INTRO and ELIM rules,
are tricky in a particular aspect, which is that they all,
in a sense, include a wild card.

Take bottom-intro, for example. With a not-intro, what we
had to generate was clear. If we're tring to generate
the proof

  prove <~A> via not-intro:
    assuming <A>, prove <#> via [rule]: ...

then we need to generate <#>, after assuming <A>.

However, it's not so clear with e.g. bottom-intro. This
is because bottom-intro works on two propositions of
the form <[prop]> and <~[prop]>, where [prop] can be
ANYTHING, no matter how large or small. This is what
I mean by 'wildcard'. ELIM rules share a similar issue:
if I want to prove <A> via an implies-elim, then I
need a statement of the form <[prop] -> A> and one
of the form <[prop]> where [prop] can be ANYTHING.

The way we deal with this is to /only/ fill in [prop]
with propositions in the passed-down 'assumptions'
value, i.e., propositions that we have assumed within
a parent proof.

So, for instance, if we're part way through a proof like so:

  prove <A -> (B -> A)> via implies-intro:
    assuming <A>, prove <B -> A> via implies-intro:
      assuming <B>, prove <A> via not-elim:
        prove <~~A> via not-intro:
          assuming <~A>, prove <#> via ?? (WE ARE HERE)

Now we want to generate a bottom. A bottom can be generated
from any statement and its negation. However, we will only
try those statements which have been assumed, namely,

  <A>, <B>, and <~A>


I don't think doing this sacrifices program correctness.

To see why, consuder the case of proving something via an or-elim.
A proof of <A> via an or-elim looks like the following:

  prove <A> via or-elim:
    prove <B | C> via [rule]: ...
    assuming <B>, prove <A> via [rule]: ...    (1)
    assuming <C>, prove <A> via [rule]: ...    (2)

If <B | C> came from an assumption, this is all fine. I will
now try to argue that if <B | C> /didn't/ come from an assumption,
then doing an or-elim is redundant, in the sense that there's
an easier way to prove <A> with a different rule. Establishing
that justifies the use of my heuristic: if doing or-elim on
non-assumed propositions is redundant, then we don't have to do so.

So I have to argue that if <B | C> didn't come from an assumption,
then doing an or-elim is redundant. Start by assuming that <B | C>
didn't come from an assumption. That means that we proved it somehow,
meaning that we either proved <B> or proved <C>. But note that,
in doing the or-elim, we have to show that <B> entails <A> and that
<C> entails <A>. (See lines annotated (1) and (2), respectively.)
Thus, if we've proven <B> or <C>, then we can use that in conjunction
with either (1) or (2) to prove <A> /directly/ without the need
for or-elim.

Thus or-elim on a non-assumed proposition is redundant and may be
skipped in computation.

I conject that similar reasoning holds for the other rules with
wildcards.

And a conjecture is good enough for me, since I don't want to do
~8 more proofs.

"""

@min_size(3)
@proofify(ProofKind.BOTTOM_INTRO)
@prop_kind(PropKind.BOTTOM)
def BOTTOM_INTRO(goal, assumptions, size):
  """
  Proofs of the form

    prove <#> via bottom-intro:
      prove <[prop]> via [rule]: ...
      prove <~[prop]> via [rule]: ...

  """

  for prop in assumptions:
    prop_proof = Proof.reiteration(prop)

    if (prop.kind == PropKind.AND
        and (prop.left == Prop(PropKind.NOT, prop.right)
             or Prop(PropKind.NOT, prop.left) == prop.right)):
      lproof = find_proof(prop.left, assumptions, size - 2)
      rproof = find_proof(prop.right, assumptions, size - 2)
      return [lproof, rproof]

    if prop.kind == PropKind.NOT:
      unwrapped = prop.contained
      unwrapped_proof = find_proof(unwrapped, assumptions, size - 2)
      if unwrapped_proof is not None:
        return [unwrapped_proof, prop_proof]

    else:
      negated = Prop(PropKind.NOT, prop)
      negated_proof = find_proof(negated, assumptions, size - 2)
      if negated_proof is not None:
        return [prop_proof, negated_proof]

"""

ELIM rules

"""


def kinded(assumptions, asn_kind):
  return [
    asn for asn in assumptions
    if asn.kind == asn_kind
  ]


@exact_size(1)
@proofify(ProofKind.AND_ELIM)
def AND_ELIM(goal, assumptions, size):
  """
  Proofs of the form

    prove <[goal]> via and-elim:
      prove <[prop] & [goal]> via [rule]: ...

  """
  for asn in kinded(assumptions, PropKind.AND):
    if goal in [asn.left, asn.right]:
      asn_proof = Proof.reiteration(asn)
      return [asn_proof]

@min_size(5)
@proofify(ProofKind.OR_ELIM)
def OR_ELIM(goal, assumptions, size):
  """
  Proofs of the form

    prove <[goal]> via or-elim:
      prove <[left] | [right]> via [rule]: ...
      assuming <[left]>, prove <[goal]> via [rule]: ...
      assuming <[right]> prove <[goal]> via [rule]: ...

  """
  for asn in kinded(assumptions, PropKind.OR):
    asn_proof = Proof.reiteration(asn)
    for lsize, rsize in share(size - 4, 2):
      lproof = find_proof(goal, assumptions, lsize, assuming=asn.left)
      rproof = find_proof(goal, assumptions, rsize, assuming=asn.right)
      if lproof is not None and rproof is not None:
        return [asn_proof, lproof, rproof]

@min_size(3)
@proofify(ProofKind.IMPLIES_ELIM)
def IMPLIES_ELIM(goal, assumptions, size):
  """
  Proofs of the form

    prove <[goal]> via implies-elim:
      prove <[left] -> [goal]> via [rule]: ...
      prove <[left]> via [rule]: ...

  """
  for asn in kinded(assumptions, PropKind.IMPLIES):
    if asn.right == goal:
      asn_proof = Proof.reiteration(asn)
      left_proof = find_proof(asn.left, assumptions, size - 2)
      if left_proof is not None:
        return [asn_proof, left_proof]

@min_size(3)
@proofify(ProofKind.IFF_ELIM)
def IFF_ELIM(goal, assumptions, size):
  """
  Proofs of the form

    prove <[goal]> via iff-elim:
      prove <[left] <-> [goal]> via [rule]: ...
      prove <[left]> via [rule]: ...

  or of the form

    prove <[goal]> via iff-elim:
      prove <[goal] <-> [right]> via [rule]: ...
      prove <[right]> via [rule]: ...

  """
  for asn in kinded(assumptions, PropKind.IFF):
    has_goal = goal in [asn.left, asn.right]
    if has_goal:
      asn_proof = Proof.reiteration(asn)
      other_side = other(goal, [asn.left, asn.right])
      other_proof = find_proof(other_side, assumptions, size - 2)
      if other_proof is not None:
        return [asn_proof, other_proof]

@min_size(2)
@proofify(ProofKind.NOT_ELIM)
def NOT_ELIM(prop, assumptions, size):
  """
  Proofs of the form

    prove <[goal]> via not-elim:
      prove <~~[goal]> via [rule]: ...

  """
  notnot = Prop(PropKind.NOT, Prop(PropKind.NOT, prop))
  notnot_proof = find_proof(notnot, assumptions, size - 1)
  if notnot_proof is not None:
    return [notnot_proof]


# == # == # == #


def prove_proposition(prop):

  size = 1

  while True:

    proof = find_proof(prop, [], size)
    if proof is not None:
      return proof

    size += 1
