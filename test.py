from slither.slithir.operations import InternalCall
from a18z import (
    Injector,
    verify,
    precondition,
    postcondition,
    prepcondition,
)
from slither import Slither

Injector('contracts/A.sol')

slith = Slither('contracts/A.sol.sol')
for contract in slith.contracts:
    for function in contract.functions:
        if function.contract == contract and function.is_implemented:
            print(f'func> {function.name}')
            print(f'ver> {verify(function)}')
            print(f'pre> {precondition(function)}')
            print(f'pos> {postcondition(function)}')
            for node in function.nodes:
                for ir in node.irs:
                    if isinstance(ir, InternalCall):
                        if not ir.is_modifier_call:
                            print(f'pep> {ir.function}:{function} is {prepcondition(function, ir)}')