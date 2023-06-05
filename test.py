from slither.slithir.operations import InternalCall
from a18z.injector import Injector
from a18z.legacy import verify
from a18z.post import postcondition
from a18z.pre import precondition
from a18z.postt import posttcondition
from a18z.pret import pretcondition
from a18z.prep import prepcondition
from slither import Slither

Injector('contracts/A.sol')

slith = Slither('contracts/A.sol.sol')
for contract in slith.contracts:
    for function in contract.functions:
        # print(f'verify> {function.name} is {verify(function)}')
        # print(f'post> {function.name} is {postcondition(function)}')
        # print(f'post> {function.name} is {postcondition(function)}')
        # print(f'pre> {function.name} is {precondition(function)}')
        # print(f'pret> {function.name} is {pretcondition(function)}')
        for node in function.nodes:
            for ir in node.irs:
                if isinstance(ir, InternalCall):
                    print(f'prep> {ir.function}:{function} is {prepcondition(function, ir)}')