from parse import parse
from prove import prove_proposition
from fitch import arrange

string = '(a⇾¬¬¬¬(¬b∨a))'
print(f'string: {string}\n')

proposition = parse(string)
print(f'proposition: {proposition}\n')

proof = prove_proposition(proposition)
print(f'proof:\n{proof.pretty}\n')

fitch = arrange(proof)
print(f'fitch:\n{fitch}\n')

pretty = fitch.pretty
print(f'pretty:\n{pretty}\n')


