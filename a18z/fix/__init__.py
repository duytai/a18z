from .chain import FixChain
from .state import State
from .task import (
    EnumerateFunction,
    BuildCallGraph,
    BuildInternalCall,
    FixFunction,
)

def fix(file):
    state = State(file)
    chain = FixChain()
    tasks = [
        EnumerateFunction(),
        BuildCallGraph(),
        BuildInternalCall(),
        FixFunction(),
    ]
    for task in tasks:
        chain.add_task(task)
    chain.run_chain(state)