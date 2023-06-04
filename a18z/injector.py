import re
from slither import Slither
from slither.core.solidity_types.elementary_type import ElementaryType, Uint

A17Z_EXT    = r'.sol'
KW_FUNCTION = r'function'
RE_ENSURES  = r'\s*\/\/\/\s*ensures\s*\(([^,]*),(.+)\)'
RE_FUNCTION = r'\s*function'
RE_OLD_ARG  = r'old\s*\(\s*([^)]*)\s*\)'
RE_OLD_TAR  = r'old_\1'

class Injector:
    def __init__(self, file: str) -> None:
        self._invariants = {}
        self._patches = {}
        self._slither = Slither(file)
        self.parse_specification()
        self.build_patch()
        self.apply_patch()

    def parse_specification(self) -> None:
        for path, code in self._slither.source_code.items():
            offset, invariants = 0, []
            for line in code.splitlines():
                # Check if the line contains the pattern for 'ensures(x, y)'
                if re.search(RE_ENSURES, line):
                    pre, post = re.search(RE_ENSURES, line).groups()
                    post = re.sub(RE_OLD_ARG, RE_OLD_TAR, post)
                    # Append the matches to the invariants list
                    invariants.append((pre, post))
                # The ensures(x, y) belongs to the current function
                if re.search(RE_FUNCTION, line):
                    loc = offset + line.find(KW_FUNCTION)
                    self._invariants[(path, loc)] = invariants[::] or [('1==1', '1==0')]
                    invariants.clear()
                # Update the offset based on the length of the current line
                offset += len(line) + 1

    def build_patch_for_variable(self) -> None:
        for contract in self._slither.contracts:
            path = contract.source_mapping.filename.absolute
            code = self._slither.source_code[path]
            loc = contract.source_mapping.start
            # Find the start location of the contract body
            start = loc + code[loc:].find('{') + 1
            payload = ''
            for variable in contract.variables:
                if variable.contract == contract:
                    payload += f'{variable.type} old_{variable.name};'
            # Update the patches dictionary for the current path
            x = self._patches.get(path, {})
            x.update({start: payload})
            self._patches[path] = x

    def build_patch_for_function(self) -> None:
        for contract in self._slither.contracts:
            for function in contract.functions:
                if function.contract == contract and function.is_implemented:
                    payload = ''
                    path = function.source_mapping.filename.absolute
                    code = self._slither.source_code[path]
                    loc = function.source_mapping.start
                    # Get invariants for the current path and location
                    invariants = self._invariants.get((path, loc), [])
                    # Concatenate invariants to form the payload
                    for invariant in invariants:
                        payload = f'(bool __v1, bool __v2)=({",".join(invariant)});'
                    # Add require to parameters
                    for variable in function.parameters:
                        if isinstance(variable.type, ElementaryType):
                            if variable.type.name in Uint:
                                payload += f'require({variable.name} >= 0);'
                    # Find the start location of the function body
                    start = loc + code[loc:].find('{') + 1
                    # Update the patches dictionary for the current path
                    x = self._patches.get(path, {})
                    x.update({start: payload})
                    self._patches[path] = x

    def build_patch(self) -> None:
        self.build_patch_for_variable()
        self.build_patch_for_function()

    def apply_patch(self) -> None:
        for path, x in self._patches.items():
            code = self._slither.source_code[path]
            offset = 0
            for loc in sorted(x.keys()):
                payload = x[loc]
                # Insert the payload at the specified location in the code
                code = code[:loc + offset] + payload + code[loc + offset:]
                offset += len(payload)
                # Write the modified code to a file
                with open(path + A17Z_EXT, 'w') as file:
                    file.write(code)