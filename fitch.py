from typing import *
from prove import Proof, ProofRule
from prop import Prop, PropKind
from util import indent

"""

This module handles transforming proofs from the tree format
into a Fitch-style format, and then pretty-printing those proofs.

"""

Line = Union['Stmt', 'Block']

class Stmt:
  """
  Represents a single statement in a Fitch-style proof.
  """

  def __init__(
    self: 'Stmt',
    prereqs: List[Line],
    claim: Prop,
    rule: ProofRule,
    lineno: int,
  ) -> 'Line':

    self.prereqs = prereqs
    self.claim = claim
    self.rule = rule
    self.lineno = lineno

  def __str__(self):
    return f'Stmt({self.claim}, {self.rule})'

  @property
  def span(self):
    return str(self.lineno)

  @property
  def pretty(self):
    if self.prereqs:
      pretty_prereqs = ':' + ','.join(pr.span for pr in self.prereqs)
    else:
      pretty_prereqs = ''
    return f'{self.lineno}. {self.claim}  [{self.rule.pretty}{pretty_prereqs}]'

class Block:
  """
  Represents an indented block in a Fich-style proof, which
  consists of an assumption and multiple lines which make up
  its body.
  """

  def __init__(
    self: 'Block',
    assumption: Optional[Stmt],
    lines: List[Line],
    lineno: int,
  ) -> 'Block':

    self.assumption = assumption
    self.lines = lines

    # Line number of the assumption
    self.lineno = lineno

  def __str__(self):
    text = '\n'.join([
      'assuming ' + str(self.assumption) if self.assumption else 'no assumption',
      *map(str, self.lines),
    ])
    return indent(text, '| ')

  @property
  def stmt_count(self):
    count = 0
    count += 1  # for assumption
    for line in self.lines:
      if isinstance(line, Stmt):
        count += 1
      elif isinstance(line, Block):
        count += line.stmt_count
    return count

  @property
  def span(self):
    lo = self.lineno

    hi = self
    while isinstance(hi, Block):
      hi = hi.lines[-1]
    hi = hi.lineno

    return f'{lo}-{hi}'

  @property
  def pretty(self):

    pretty_header = \
      f'{self.lineno}. {self.assumption}   [as]' \
        if self.assumption else f'{self.lineno}.'

    pretty_lines = [
      ' ' + line.pretty if isinstance(line, Stmt) else line.pretty
      for line in self.lines
    ]

    text = '\n'.join([
      ' ' + pretty_header,
      '───',
      *pretty_lines,
    ])
    return indent(text, '│')

def arrange(proof: Proof) -> Block:
  """

  The goal of this function is twofold: first, this function takes
  us towards a Fitch-style representation of the given proof; second,
  this function helps eliminate repetition.

  Consider the following proof of A -> ((A | B) & (A | B))

    prove <A -> ((A | B) & (A | B))> via implies-intro:
      assuming <A>, prove <(A | B) & (A | B)> via and-intro:
        prove <A | B> via or-intro:
          prove <A> via reiteration
        prove <A | B> via or-intro:
          prove <A> via reiteration

  with the associated Fitch-style proof

    | 1. A            [assumption]
    |---
    | 2. A | B        [|I:1]
    3. A -> (A | B)   [->I:1-2]

  This function will build the Fitch-style version of the given proof
  and return it.

  Note that there is repeition that appears in the input tree proof
  but is not present in the output. In particular, the proof that
  "<A> entails <A | B>" is present twice. This fuction will detect such
  redundancies and account for them by never proving something twice within
  the output.

  """

  return arrange_aux(proof, [], 1)

def arrange_aux(proof: Proof, parent_context: List[Line], lineno: int) -> Block:
  """
  Same as arrange, but with an extra argument for recursion.
  This argument keeps track of what statements are within a parent scope
  but accessible to us right now
  """

  lines: List[Line] = []

  assumption_lineno = lineno
  lineno += 1

  def context(): return parent_context + lines

  prereqs = []
  for subproof_idx, subproof in enumerate(proof.subproofs):

    # Don't bother to include reiterations
    if subproof.rule == ProofRule.REITERATION:
      continue

    # Remove redundancies
    already_proven = any(
      isinstance(line, Stmt) and line.claim == subproof.claim
      for line in lines
    )
    if already_proven:
      continue

    if not subproof.assumption:
      block = arrange_aux(subproof, context(), lineno)
      lineno += block.stmt_count
      lines.extend(block.lines)
      prereqs.extend(block.lines)
    else:
      block = arrange_aux(subproof, context(), lineno)
      lineno += block.stmt_count
      lines.append(block)
      prereqs.append(block)

  stmt = Stmt(
    prereqs = prereqs,
    claim = proof.claim,
    rule = proof.rule,
    lineno = lineno,
  )
  lines.append(stmt)
  lineno += 1

  return Block(
    # keep in mind that proof.assumption may be None here
    assumption = proof.assumption,
    lines = lines,
    lineno = assumption_lineno,
  )

def pretty_print(proof: Proof) -> str:
  block = arrange(proof)
  return block.pretty



