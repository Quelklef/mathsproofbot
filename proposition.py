from pretty import *

class Proposition:
  
  kind_IMPLIES = 'implies'
  kind_IFF     = 'iff'
  kind_OR      = 'or'
  kind_AND     = 'and'
  kind_NOT     = 'not'
  kind_BOTTOM  = 'bottom'

  kind_IDENT   = 'ident'

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

  @property
  def sigil(self):
    return {
      Proposition.kind_IMPLIES: pretty_IMPLIES,
      Proposition.kind_IFF    : pretty_IFF,
      Proposition.kind_OR     : pretty_OR,
      Proposition.kind_AND    : pretty_AND,
      Proposition.kind_NOT    : pretty_NOT,
      Proposition.kind_BOTTOM : pretty_BOTTOM,
    }[self.kind]

  def prettify(self, *, is_root):
    if self.kind == Proposition.kind_BOTTOM:
      return pretty_BOTTOM
    elif self.kind == Proposition.kind_IDENT:
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

  def __repr__(self):
    return  f'|{self}|'

  def __eq__(self, other):
    return (type(self) == type(other)
      and self.kind == other.kind
      and self.args == other.args)


