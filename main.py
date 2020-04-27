from parse import parse
from prove import prove_proposition
from fitch import pretty_print

string = '(a⇾¬¬¬¬(¬b⇾a))'
print(f'string: {string}\n')

proposition = parse(string)
print(f'proposition: {proposition}\n')

proof = prove_proposition(proposition)
print(f'proof:\n{proof.pretty}\n')

pretty = pretty_print(proof)
print(f'pretty:\n{pretty}\n')


