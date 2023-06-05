from a18z.injector import Injector
from a18z.legacy import verify
from slither import Slither

Injector('contracts/A.sol')

slith = Slither('contracts/A.sol.sol')
for contract in slith.contracts:
    for function in contract.functions:
        print(f'> {function.name}')
        r = verify(function)
        print(f'* {r}')
        # verifier.verify_function(function)
        # verifier.precondition(function)
        # verifier.postcondition(function)
        # verifier.prepcondition(function)