from a18z.injector import Injector
from a18z.legacy import verify
from a18z.post import postcondition
from a18z.pre import precondition
from a18z.post_true import postruecondition
from a18z.pre_true import pretruecondition
from slither import Slither

Injector('contracts/A.sol')

slith = Slither('contracts/A.sol.sol')
for contract in slith.contracts:
    for function in contract.functions:
        # print(f'verify > {function.name} is {verify(function)}')
        # print(f'post > {function.name} is {postcondition(function)}')
        # print(f'posttrue > {function.name} is {postruecondition(function)}')
        # print(f'pre> {function.name} is {precondition(function)}')
        print(f'pretrue> {function.name} is {pretruecondition(function)}')