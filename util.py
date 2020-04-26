
def indent(text, indentation='. '):
  """
  Indent a block of text
  """
  return '\n'.join(indentation + line for line in text.split('\n'))

def find(predicate, it):
  """
  Find an item in an iterable that matches a predicate
  """
  for x in it:
    if predicate(x):
      return x

def iweave(*iterators):
  # iweave( ABC, def, 12 ) --> A d 1 B e 2 C f
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

def icross(itX, itY):
  # icross( ABC, DEF )
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
