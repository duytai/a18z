from .task import Task

class FixChain:
    def __init__(self) -> None:
        self._tasks = []

    def add_task(self, t: Task):
        self._tasks.append(t)

    def run_chain(self, state):
        for task in self._tasks:
            task.execute(state)
