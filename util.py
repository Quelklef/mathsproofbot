
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

def share(n, k):
  """
  Return all the different ways to split a number N
  between K different groups.

  share(4, 2) --> (1, 3), (2, 2), (3, 1)
  """
  if k == 1:
    yield (n,)
    return
  for x in range(1, n):
    for sub in share(n - x, k - 1):
      yield (x, *sub)

def other(x, ab):
  """
    other(1, [1, 2]) = 2
    other(2, [1, 2]) = 1
  """
  a, b = ab
  if x == a: return b
  if x == b: return a
  assert False, (x, ab)

def union(sets):
  result = set()
  for set_ in sets:
    result |= set_
  return result
