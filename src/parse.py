from prop import Prop, PropKind
from pretty import *

OPEN_chars    = [pretty_OPEN, '[', '{']
CLOSE_chars   = [pretty_CLOSE, ']', '}']
IMPLIES_chars = [pretty_IMPLIES, '>']
IFF_chars     = [pretty_IFF, '=']
OR_chars      = [pretty_OR, '|']
AND_chars     = [pretty_AND, '&', '^', '.']
NOT_chars     = [pretty_NOT, '~', '-', '!']
BOTTOM_chars  = [pretty_BOTTOM, '_']

BINOPS_chars = [
  *IMPLIES_chars,
  *IFF_chars,
  *OR_chars,
  *AND_chars,
]

def parse(string):
  """
  Parse a proposition, returning a Prop object.
  """
  no_spaces = ''.join(c for c in string if c != ' ')
  node, leftover = parse_top(no_spaces)
  if leftover != '':
    raise ValueError(f"Unexpected leftover: '{leftover}'")
  return node

def binop_kind(op):
  """
  Given a binary operator, e.g. '>', return its kind as a PropKind value
  """
  if op in IMPLIES_chars: return PropKind.IMPLIES
  elif op in IFF_chars  : return PropKind.IFF
  elif op in OR_chars   : return PropKind.OR
  elif op in AND_chars  : return PropKind.AND
  else: raise ValueError(f"Unrecognized operator '{op}'")

def parse_top(rest):
  """
  Top-level parsing function.
  Takes a string and returns a tuple (prop, rest)
  where `prop` is a parsed proposition and `rest`
  is the remaining input.
  """

  # We start assuming that we're parsing a
  # binary operator, ...

  left, rest = parse_simple(rest)

  # ... but then return early if we decide
  # that it actually wasn't a binary operator application
  if len(rest) == 0 or rest[0] not in BINOPS_chars:
    return left, rest

  op = rest[0]
  rest = rest[1:]
  right, rest = parse_top(rest)

  node = Prop(binop_kind(op), left, right)
  return (node, rest)

def parse_simple(rest):
  """
  Attempt to parse anything besides a binary oeprator
  """

  if rest[0] in OPEN_chars:
    node, rest = parse_top(rest[1:])
    if rest[0] not in CLOSE_chars:
      raise ValueError('Unclosed brace')
    rest = rest[1:]
    return (node, rest)

  elif rest[0] in NOT_chars:
    child, rest = parse_simple(rest[1:])
    node = Prop(PropKind.NOT, child)
    return (node, rest)

  elif rest[0] in BOTTOM_chars:
    node = Prop(PropKind.BOTTOM)
    return (node, rest[1:])

  else:
    node = Prop(PropKind.NAME, rest[0])
    return (node, rest[1:])

if __name__ == '__main__':

  import test

  class Tests(test.Tests):

    def test_1(self):

      expected = \
        Prop(PropKind.AND,
          Prop(PropKind.NOT,
            Prop(PropKind.NAME, 'a')),
          Prop(PropKind.NAME,  'b'))

      actual = parse('-a.b')

      self.assertEq(expected, actual)

  Tests().go()
