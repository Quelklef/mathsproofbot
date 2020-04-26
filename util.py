
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
