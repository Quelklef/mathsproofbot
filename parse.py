from proposition import Proposition
from pretty import *

OPEN_chars    = [pretty_OPEN, '[', '{']
CLOSE_chars   = [pretty_CLOSE, ']', '}']
IMPLIES_chars = [pretty_IMPLIES, '>']
IFF_chars     = [pretty_IFF, '=']
OR_chars      = [pretty_OR, '|']
AND_chars     = [pretty_AND, '&', '^', '.']
NOT_chars     = [pretty_NOT, '~', '-', '!']
BOTTOM_chars  = [pretty_BOTTOM]

BINOPS_chars = [
  *IMPLIES_chars,
  *IFF_chars,
  *OR_chars,
  *AND_chars,
]

def parse(string):
  """
  Parse a syntactically valid proposition.
  If the proposition is not syntactically valid,
  behaviour is undefined.
  """
  node, string = parse_top(string)
  assert string == '', string
  return node

def parse_top(string):

  # Attempt to parse a binary operator

  left, string = parse_simple(string)

  if len(string) == 0 or string[0] not in BINOPS_chars:
    return left, string

  op = string[0]
  string = string[1:]
  right, string = parse_top(string)

  if op in IMPLIES_chars: kind = Proposition.kind_IMPLIES
  if op in IFF_chars    : kind = Proposition.kind_IFF
  if op in OR_chars     : kind = Proposition.kind_OR
  if op in AND_chars    : kind = Proposition.kind_AND

  node = Proposition(kind, left, right)

  return (node, string)

def parse_simple(string):
  # parse anything but a binary operator

  if string[0] in OPEN_chars:
    node, string = parse_top(string[1:])
    assert string[0] in CLOSE_chars, string
    string = string[1:]
    return (node, string)

  elif string[0] in NOT_chars:
    child, string = parse_top(string[1:])
    node = Proposition(Proposition.kind_NOT, child)
    return (node, string)

  else:
    node = Proposition(Proposition.kind_IDENT, string[0])
    return (node, string[1:])



