from a18z import Verifier

verifier = Verifier('contracts/A.sol')
for contract in verifier._slither.contracts:
    for function in contract.functions:
        verifier.verify_function(function)
        break