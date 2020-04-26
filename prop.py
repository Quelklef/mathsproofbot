from pretty import *
from typing import *
import enum

class PropKind(enum.Enum):
  IMPLIES = 'implies'
  IFF     = 'iff'
  OR      = 'or'
  AND     = 'and'
  NOT     = 'not'
  BOTTOM  = 'bottom'

  NAME    = 'name'


class Prop:

  """

  Represents a propositional/0th-order mathematical proposition.
  This class contains no functionality; it is 100% a data class.

  Instances are created with a type, as well as 0 or more
  children, which are expected to also be instances of Prop.

  An example to represent the proposition 'a implies b' is:
  >>> A = Prop(PropKind.NAME, 'A')
  >>> B = Prop(PropKind.NAME, 'B')
  >>> implication = Prop(PropKind.IMPLIES, A, B)

  If the proposition is a binary op, its children may be accessed
  with the use of .left and .right:
  >>> assert implication.left == A
  >>> assert implication.right == B

  If it's a unary op, its child may be accessed via .contained:
  >>> not_A = Prop(Propkind.NOT, A)
  >>> assert not_A.contained == A

  """


  def __init__(self, kind, *args):
    self.kind = kind
    self.args = args

  # convenience .left and .right for binary ops
  @property
  def left(self): return self.args[0]
  @property
  def right(self): return self.args[1]

  # convenience .contained for unary ops
  @property
  def contained(self): return self.args[0]

  def __eq__(self, other):
    return (type(self) == type(other)
      and self.kind == other.kind
      and self.args == other.args)

  @property
  def sigil(self):
    return {
      PropKind.IMPLIES: pretty_IMPLIES,
      PropKind.IFF    : pretty_IFF,
      PropKind.OR     : pretty_OR,
      PropKind.AND    : pretty_AND,
      PropKind.NOT    : pretty_NOT,
      PropKind.BOTTOM : pretty_BOTTOM,
    }[self.kind]

  def prettify(self, *, is_root):
    if self.kind == PropKind.BOTTOM:
      return pretty_BOTTOM
    elif self.kind == PropKind.NAME:
      return self.contained
    elif len(self.args) == 1:
      pretty_contained = self.contained.prettify(is_root=False)
      return f'{self.sigil}{pretty_contained}'
    elif len(self.args) == 2:
      pretty_left = self.left.prettify(is_root=False)
      pretty_right = self.right.prettify(is_root=False)
      text = f'{pretty_left} {self.sigil} {pretty_right}'
      if not is_root:
        text = f'({text})'
      return text

  def __str__(self):
    return self.prettify(is_root=True)

if __name__ == '__main__':

  import test

  class Tests(test.Tests):

    def test_1(self):

      prop = \
        Prop(PropKind.NOT,
          Prop(PropKind.AND,
            Prop(PropKind.NOT,
              Prop(PropKind.NAME, 'a')),
            Prop(PropKind.NAME,  'a')))

      expected = f"{pretty_NOT}({pretty_NOT}a {pretty_AND} a)"
      actual = str(prop)

      self.assertEq(expected, actual)

  Tests().go()
