from typing import *
from prove import Proof, ProofRule
from prop import Prop, PropKind
from util import indent, find

"""

This module handles transforming proofs from the tree format
into a Fitch-style format, and then pretty-printing those proofs.

"""

Line = Union['Stmt', 'Bunch', 'Block']

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
  def stmt_count(self):
    return 1

  @property
  def span(self):
    return str(self.lineno)

  @property
  def pretty(self):
    if not self.claim:
      return f'{self.lineno}.'
    if self.prereqs:
      pretty_prereqs = ':' + ','.join(pr.span for pr in self.prereqs)
    else:
      pretty_prereqs = ''
    return f'{self.lineno}. {self.claim}  [{self.rule.pretty}{pretty_prereqs}]'

class Bunch:
  """
  Represents many lines grouped together in a Fitch-style proof.
  Crucially, a Bunch does NOT have an assoicated assumption.
  The primary role of a Bunch is to serve as the top-level container
  in a Fitch-style proof, since Fitch-style proofs don't start with
  assumptions.
  """

  def __init__(
    self: 'Bunch',
    body: List[Line],
  ) -> 'Bunch':

    self.body = body

  def __str__(self):
    return '\n'.join(str(line) for line in self.body)

  @property
  def stmt_count(self):
    return sum(line.stmt_count for line in self.body)

  @property
  def pretty(self):
    return '\n'.join(line.pretty for line in self.body)

class Block:
  """
  Represents an indented block in a Fitch-style proof, which
  consists of an assumption and multiple lines which make up
  its body.
  """

  def __init__(
    self: 'Block',
    assumption: Optional[Stmt],
    body: List[Line],
  ) -> 'Block':

    self.assumption = assumption
    self.body = body

  def __str__(self):
    text = '\n'.join([
      'assuming ' + str(self.assumption) if self.assumption else 'no assumption',
      *map(str, self.body),
    ])
    return indent(text, '| ')

  @property
  def stmt_count(self):
    count = 1  # for assumption
    count += sum(line.stmt_count for line in self.body)
    return count

  @property
  def span(self):
    lo = self.assumption.lineno

    hi = self
    while isinstance(hi, Block):
      hi = hi.body[-1]
    hi = hi.lineno

    return f'{lo}-{hi}'

  @property
  def pretty(self):

    pretty_body = '\n'.join(
      ' ' + line.pretty if isinstance(line, Stmt) else line.pretty
      for line in self.body
    )

    bar = '│'

    text = '\n'.join([
      indent(f' {self.assumption.pretty}', bar),
      '├───',
      indent(pretty_body, bar),
    ])
    return text

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

def arrange_aux(proof: Proof, parent_context: List[Line], lineno: int) -> Union[Bunch, Block]:
  """
  Same as arrange, but with an extra argument for recursion.
  This argument keeps track of what statements are within a parent scope
  but accessible to us right now
  """

  def use_lineno():
    nonlocal lineno
    no = lineno
    lineno += 1
    return no

  if proof.assumption is not None:
    block_assumption = Stmt(
      prereqs = [],
      claim = proof.assumption,
      rule = ProofRule.ASSUMPTION,
      lineno = use_lineno(),
    )

    lines: List[Line] = [block_assumption]

  else:
    lines: List[Line] = []

  def context(): return parent_context + lines

  prereqs = []
  for subproof in proof.subproofs:

    # Remove redundancies
    # Note that the context we search does NOT include the context
    # of the subproof itself (i.e. if it has an assumption), meaning
    # that e.g. subproofs of the form "assuming X prove X" will
    # remain in their full form and not be reduced..
    # This actually happens to be desirable, since it's more
    # aesthetic to show something like "assuming X prove X" as
    #   | x
    #   |---
    #   | x
    # and not just as
    #   | x
    #   |---
    # with no body
    existing_line = find(
      lambda line: isinstance(line, Stmt) and line.claim == subproof.claim,
      context()
    )
    already_proven = existing_line is not None
    if already_proven:
      prereqs.append(existing_line)
      continue

    if not subproof.assumption:
      bunch = arrange_aux(subproof, context(), lineno)
      lineno += bunch.stmt_count
      lines.extend(bunch.body)
      # append the last line since that's the one corresponding to the subproof claim
      prereqs.append(bunch.body[-1])
    else:
      block = arrange_aux(subproof, context(), lineno)
      lineno += block.stmt_count
      lines.append(block)
      prereqs.append(block)

  stmt = Stmt(
    prereqs = prereqs,
    claim = proof.claim,
    rule = proof.rule,
    lineno = use_lineno(),
  )
  lines.append(stmt)

  if proof.assumption is None:
    return Bunch(lines)
  else:
    return Block(
      assumption = block_assumption,
      body = lines[1:],  # remove assumption back out
    )

def pretty_print(proof: Proof) -> str:
  fitch = arrange(proof)
  return fitch.pretty



