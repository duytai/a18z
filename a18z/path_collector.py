from slither.core.cfg.node import (Node, NodeType)
from slither.slithir.variables.temporary import TemporaryVariable
from slither.slithir.operations import Unary, UnaryType, Condition

class PathCollector:
    def __init__(self):
        self._paths = []

    @property
    def paths(self):
        return self._paths

    def collect_paths(self, node: Node, curr=[]):
        for ir in node.irs:
            curr.append(ir)
        if not node.sons:
            self._paths.append(curr[:])
            return
        if node.type == NodeType.IF:
            self.collect_paths(node.son_true, curr[:])
            if node.son_false is not None:
                assert isinstance(curr[-1], Condition)
                # Replace true_condition with false_condition
                true_cond = curr.pop()
                false_cond = Unary(
                    TemporaryVariable(node),
                    true_cond.value,
                    UnaryType.BANG
                )
                curr.append(false_cond)
                false_cond = Condition(false_cond.lvalue)
                curr.append(false_cond)
                self.collect_paths(node.son_false, curr[:])
            return
        for node in node.sons:
            self.collect_paths(node, curr[:])