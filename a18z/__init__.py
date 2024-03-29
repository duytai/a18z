from .injector import Injector
from .legacy import verify, collect, LegacyQuery
from .post import postcondition
from .pre import precondition
from .prep import prepcondition
from .fix import fix, rq1, rq2

def inject(file):
    ij = Injector(file)
    ij.parse_specification()
    ij.build_patch_for_variable()
    ij.build_patch_for_function()
    ij.apply_patch()