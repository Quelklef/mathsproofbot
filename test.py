
class Tests:

  def assertEq(self, expected, actual):
    if expected != actual:
      raise AssertionError(f"Expeected:\n\t{expected}\nBut got:\n\t{actual}")

  def go(self):
    test_names = [
      key for key in type(self).__dict__
      if key.startswith('test')
    ]

    for name in test_names:
      getattr(self, name)()
