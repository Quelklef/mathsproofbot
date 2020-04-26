
from proposition import Proposition
from functools import wraps
from typing import *
from pretty import *

pretty_INTRO = 'I'
pretty_ELIM  = 'E'

def indent(text, indentation='. '):
  return '\n'.join(indentation + line for line in text.split('\n'))

class Derivation:
  def __init__(self, parents, proposition, justification):
    self.parents = parents
    self.proposition = proposition
    self.justification = justification

  def __eq__(self, other):
    return (type(self) == type(other)
      and self.parents == other.parents
      and self.proposition == other.proposition
      and self.justification == other.justification)

  def __repr__(self):
    return f'<Derivation of {self.proposition}>'

  @property
  def long_form(self):
    text = ''
    for parent in self.parents:
      text += parent.long_form + '\n'
    text += f"{self.proposition} [{self.justification}]"
    return text

class Block:
  def __init__(self, assumption: Proposition, body: Derivation):
    self.assumption = assumption
    self.body = body

  def __eq__(self, other):
    return (type(self) == type(other)
      and self.assumption == other.assumption
      and self.body == other.body)

  def __repr__(self):
    return f'<Block taking {self.assumption} to {self.body.proposition}>'

  @property
  def long_form(self):
    return indent(f'assume {self.assumption}\n{self.body.long_form}', '|   ')

def weave(*iterators):
  # weave( ABC, def, 12 ) --> A d 1 B e 2 C f
  exhausted = [False] * len(iterators)
  while not all(exhausted):
    for idx, iterator in enumerate(iterators):
      if exhausted[idx]:
        continue
      try:
        val = next(iterator)
        yield val
      except StopIteration:
        exhausted[idx] = True

def cross(itX, itY):
  # cross( ABC, DEF )
  # iterates from
  #      A  B  C
  #   D  x  x  x
  #   E  x  x  x
  #   F  x  x  x
  # in the order AD, BD, AE, CD, BE, AF, ...

  xs = []
  ys = []

  while True:
    xs.append(next(itX))
    ys.append(next(itY))

    size = len(xs)
    (x, y) = (size - 1, 0)
    while x >= 0:
      yield (xs[x], ys[y])
      x -= 1
      y += 1

def find_proofs(
  prop: Proposition,
  assumptions: List[Proposition],
):

  yield None

  yield from weave(
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

def prove_proposition(prop):
  proofs = find_proofs(prop, [])
  valid = (proof for proof in proofs if proof is not None)
  return next(valid)

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
      yield Derivation(
        parents       = [],
        proposition   = prop,
        justification = 'RE',
      )

@requires_kind(Proposition.kind_AND)
def AND_INTRO(prop, assumptions):
  left_proofs = find_proofs(prop.left, assumptions)
  right_proofs = find_proofs(prop.right, assumptions)
  for left_proof, right_proof in cross(left_proofs, right_proofs):
    if None in [left_proof, right_proof]:
      yield None
    else:
      yield Derivation(
        parents       = [left_proof, right_proof],
        proposition   = prop,
        justification = pretty_AND + pretty_INTRO,
      )

# TODO
# same here
def AND_ELIM(prop, assumptions):
  and_props = (prop for prop in assumptions if prop.kind == Proposition.kind_AND)
  is_sufficient = lambda and_prop: prop in [and_prop.left, and_prop.right]
  sufficients = filter(is_sufficient, and_props)
  for suff in sufficients:
    yield Derivation(
      parents = [],
      proposition = prop,
      justification = pretty_AND + pretty_INTRO,
    )

@requires_kind(Proposition.kind_OR)
def OR_INTRO(prop, assumptions):
  left_proofs = find_proofs(prop.left, assumptions)
  right_proofs = find_proofs(prop.right, assumptions)
  for proof in weave(left_proofs, right_proofs):
    if proof is None:
      yield None
    else:
      yield Derivation([proof], prop, pretty_OR + pretty_INTRO)

# TODO
def OR_ELIM(prop, assumptions):
  yield from ()

@requires_kind(Proposition.kind_IMPLIES)
def IMPLIES_INTRO(prop, assumptions):
  antecedent = prop.left
  consequent = prop.right
  inner_assumptions = assumptions + [antecedent]
  consequent_proofs = find_proofs(consequent, inner_assumptions)
  for consequent_proof in consequent_proofs:
    if consequent_proof is None:
      yield None
    else:
      block = Block(
        assumption = antecedent,
        body = consequent_proof,
      )
      yield Derivation(
        parents       = [block],
        proposition   = prop,
        justification = pretty_IMPLIES + pretty_INTRO,
      )

# TODO
# TODO: this will not put the implication as a parent, meaning it won't be in the ouput
def IMPLIES_ELIM(prop, assumptions):
  implies_props = (prop for prop in assumptions if prop.kind == Proposition.kind_IMPLIES)
  implies_this = (implies_prop for implies_prop in implies_props if implies_prop.right == prop)
  for implies_prop in implies_this:
    antecedent_proofs = find_proofs(implies_prop.left, assumptions)
    for antecedent_proof in antecedent_proofs:
      if antecedent_proof is None:
        yield None
      else:
        yield Derivation(
          parents       = [antecedent_proof],
          proposition   = prop,
          justification = pretty_IMPLIES + pretty_ELIM,
        )

@requires_kind(Proposition.kind_IFF)
def IFF_INTRO(prop, assumptions):
  ltr_prop = Proposition(Proposition.kind_IMPLIES, prop.left, prop.right)
  ltr_proofs = find_proofs(ltr_prop, assumptions)
  rtl_prop = Proposition(Proposition.kind_IMPLIES, prop.right, prop.left)
  rtl_proofs = find_proofs(rtl_prop, assumptions)
  for ltr_proof, rtl_proof in cross(ltr_proofs, rtl_proofs):
    if None in [ltr_proof, rtl_proof]:
      yield None
    else:
      yield Derivation(
        parents       = [ltr_proof, rtl_proof],
        proposition   = prop,
        justification = pretty_IFF + pretty_INTRO,
      )

# TODO
# same here
def IFF_ELIM(prop, assumptions):
  iff_props = filter(lambda p: p.kind == Proposition.kind_IFF, assumptions)
  left_is_this = filter(lambda p: p.left == prop, iff_props)
  right_is_this = filter(lambda p: p.right == prop, iff_props)

  for iff_prop in left_is_this:
    right_proofs = find_proofs(iff_prop.right, assumptions)
    for right_proof in right_proofs:
      if right_proof is None:
        yield None
      else:
        yield Derivation(
          parents       = [right_proof],
          proposition   = prop,
          justification = pretty_IFF + pretty_ELIM,
        )

  for iff_prop in right_is_this:
    left_proofs = find_proofs(iff_prop.left, assumptions)
    for left_proof in left_proofs:
      if left_proof is None:
        yield None
      else:
        yield Derivation(
          parents       = [left_proof],
          proposition   = prop,
          justification = pretty_IFF + pretty_ELIM,
        )

# TODO
# same here
@requires_kind(Proposition.kind_BOTTOM)
def BOTTOM_INTRO(bottom, assumptions):
  for prop in assumptions:

    if prop.kind == Proposition.kind_NOT:
      unwrapped_prop = prop.contained
      unwrapped_proofs = find_proofs(unwrapped_prop, assumptions)
      for unwrapped_proof in unwrapped_proofs:
        if unwrapped_proof is None:
          yield None
        else:
          yield Derivation(
            parents       = [unwrapped_proof],
            proposition   = bottom,
            justification = pretty_BOTTOM + pretty_INTRO,
          )

    else:
      negated_prop = Proposition(Proposition.kind_NOT, prop)
      negated_prop_proofs = find_proofs(negated_prop, assumptions)
      for negated_prop_proof in negated_prop_proofs:
        if negated_prop_proof is None:
          yield None
        else:
          yield Derivation(
            parents       = [negated_prop_proof],
            proposition   = bottom,
            justification = pretty_BOTTOM + pretty_INTRO,
          )

@requires_kind(Proposition.kind_NOT)
def NOT_INTRO(prop, assumptions):
  unwrapped_prop = prop.contained
  bottom_prop = Proposition(Proposition.kind_BOTTOM)
  bottom_proofs = find_proofs(bottom_prop, assumptions + [unwrapped_prop])
  for bottom_proof in bottom_proofs:
    if bottom_proof is None:
      yield None
    else:
      block = Block(unwrapped_prop, bottom_proof)
      yield Derivation(
        parents       = [block],
        proposition   = prop,
        justification = pretty_NOT + pretty_INTRO,
      )

def NOT_ELIM(prop, assumptions):
  double_negated = Proposition(Proposition.kind_NOT, Proposition(Proposition.kind_NOT, prop))
  double_negated_proofs = find_proofs(double_negated, assumptions)
  for double_negated_proof in double_negated_proofs:
    if double_negated_proof is None:
      yield None
    else:
      yield Derivation([double_negated_proof], prop, pretty_NOT + pretty_ELIM)


# == Pretty printing == #

def find(predicate, li):
  for x in li:
    if predicate(x):
      return x

Proof = Union[Derivation, Block]

def arrange(
  proof: Proof,
  context: List[Proof],
):

  statements = []

  if isinstance(proof, Derivation):
    for parent_idx, parent in enumerate(proof.parents):

      if isinstance(parent, Derivation):
        existing = find(
          lambda statement:
            isinstance(statement, Derivation)
            and statement.proposition == parent.proposition,
          context + statements
        )

        already_proven = existing is not None

        if already_proven:
          proof.parents[parent_idx] = existing
        else:
          statements.extend(arrange(parent, context + statements))

      elif isinstance(parent, Block):
        existing = find(
          lambda statement:
            isinstance(statement, Block)
            and statement.assumption == parent.assumption
            and statement.body.proposition == parent.body.proposition,
          context + statements,
        )

        already_proven = existing is not None

        if already_proven:
          proof.parents[parent_idx] = existing
        else:
          statements.append(arrange(parent, context + statements))

    statements.append(proof)

  elif isinstance(proof, Block):
    assumption_as_derivation = Derivation([], proof.assumption, 'assumption')
    statements.append(assumption_as_derivation)
    statements.extend(arrange(proof.body, context + statements))

  return statements

def assign_line_numbers(arranged):
  lineno = 1
  def do_assign(statements):
    nonlocal lineno
    for statement in statements:
      if isinstance(statement, list):
        do_assign(statement)
      else:
        statement.line_number = lineno
        lineno += 1
  do_assign(arranged)

def location(proof: Proof):
  if isinstance(proof, Derivation):
    return str(proof.line_number)
  elif isinstance(proof, Block):
    return f'-{proof.body.line_number}'
  else:
    assert False, (type(proof), proof)

def pretty_print(proof: Proof) -> str:

  statements = arrange(proof, [])
  assign_line_numbers(statements)

  def print_item(item):
    if isinstance(item, Derivation):
      parent_locations = [location(parent) for parent in item.parents]
      parent_loc_str = ','.join(parent_locations)
      if parent_loc_str != '': parent_loc_str = f'({parent_loc_str})'
      return f'{item.line_number}. {item.proposition} by {item.justification}{parent_loc_str}'
    elif isinstance(item, list):
      return indent('\n'.join(map(print_item, item)), '│ ')

  return '\n'.join(map(print_item, statements))



# == Top-level API == #

from parse import parse

def prove(string):
  prop = parse(string)
  proof = prove_proposition(prop)
  printed = pretty_print(proof)
  return printed

if __name__ == '__main__':

  string = '((a>b)&(b>a))>(a=b)'
  print(f'string: {string}\n')

  proposition = parse(string)
  print(f'proposition: {proposition}\n')

  proof = prove_proposition(proposition)
  print(f'proof:\n{proof.long_form}\n')

  pretty = pretty_print(proof)
  print(f'pretty:\n{pretty}')

