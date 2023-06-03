from slither.core.cfg.node import (Node, NodeType)

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
            if node.son_true is not None:
                self.collect_paths(node.son_false, curr[:])
            return
        for node in node.sons:
            self.collect_paths(node, curr[:])