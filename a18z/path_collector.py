from slither.core.cfg.node import (Node, NodeType)
from slither.slithir.variables.temporary import TemporaryVariable
from slither.slithir.operations import Unary, Condition
from slither.core.expressions.unary_operation import UnaryOperationType

class PathCollector:
    def __init__(self):
        self._paths = []

    @property
    def paths(self):
        return self._paths

    def collect_paths(self, node: Node, curr=[]):
        types = [
            NodeType.ENTRYPOINT,
            NodeType.ENDIF,
            NodeType.VARIABLE,
            NodeType.EXPRESSION,
            NodeType.RETURN,
        ]
        if node.type in types:
            for ir in node.irs:
                curr.append(ir)
        elif node.type == NodeType.IF:
            for ir in node.irs:
                curr.append(ir)
            self.collect_paths(node.son_true, curr[:])
            if node.son_false is not None:
                assert isinstance(curr[-1], Condition)
                true_cond = curr.pop()
                false_cond = Unary(
                    TemporaryVariable(node),
                    true_cond.value,
                    UnaryOperationType.BANG
                )
                curr.append(false_cond)
                false_cond = Condition(false_cond.lvalue)
                curr.append(false_cond)
                self.collect_paths(node.son_false, curr[:])
            return
        elif node.type == NodeType.THROW:
            return
        else: raise ValueError(node.type)
        if not node.sons:
            self._paths.append(curr[:])
        for node in node.sons:
            self.collect_paths(node, curr[:])