from slither.slithir.operations import InternalCall
from a18z import (
    Injector,
    verify,
    precondition,
    postcondition,
    prepcondition
)
from slither import Slither

Injector('contracts/A.sol')

slith = Slither('contracts/A.sol.sol')
for contract in slith.contracts:
    for function in contract.functions:
        if function.contract == contract:
            print(f'ver> {function.name} is {verify(function)}')
            print(f'pre> {function.name} is {precondition(function)}')
            print(f'pos> {function.name} is {postcondition(function)}')
            for node in function.nodes:
                for ir in node.irs:
                    if isinstance(ir, InternalCall):
                        print(f'pep> {ir.function}:{function} is {prepcondition(function, ir)}')