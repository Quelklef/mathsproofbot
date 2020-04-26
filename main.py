from parse import parse
from prove import prove_proposition
from fitch import arrange

string = '(a>--a)'
print(f'string: {string}\n')

proposition = parse(string)
print(f'proposition: {proposition}\n')

proof = prove_proposition(proposition)
print(f'proof:\n{proof.long_form}\n')

block = arrange(proof)
print(f'block:\n{block}\n')

pretty = block.pretty
print(f'pretty:\n{pretty}\n')


