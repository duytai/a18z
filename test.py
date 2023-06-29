from a18z import inject, fix, test

inject('contracts/A.sol')
fix('contracts/A.sol.sol')
# test('contracts/A.sol.sol')