from a18z import Verifier, Injector

Injector('contracts/A.sol')

verifier = Verifier('contracts/A.sol.sol')
for contract in verifier._slither.contracts:
    for function in contract.functions:
        # verifier.verify_function(function)
        verifier.revamp_precondition(function)