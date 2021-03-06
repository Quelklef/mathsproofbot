from parse import parse
from prove import prove_proposition
from fitch import arrange


def prove(string):
  proposition = parse(string)
  # vvv If we've reached proposition size 30, there's probably a bug, so give up
  proof = prove_proposition(proposition, max_size=25)
  if proof is None:
    return None
  fitch = arrange(proof)
  pretty = fitch.pretty
  return pretty


if __name__ == '__main__':

  string = '-(a>-a)'
  print(f'string: {string}\n')

  proposition = parse(string)
  print(f'proposition: {proposition}\n')

  proof = prove_proposition(proposition)
  print(f'proof:\n{proof.pretty}\n')

  fitch = arrange(proof)
  print(f'fitch:\n{fitch}\n')

  pretty = fitch.pretty
  print(f'pretty:\n{pretty}\n')


