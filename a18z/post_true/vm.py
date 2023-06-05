import z3
from ..post import PostVM

class PostTrueVM(PostVM):
    def set_precondition(self, value):
        self._precondition = z3.BoolVal(True)