from .chain import FixChain
from .state import State
from .task import (
    EnumerateFunction,
    BuildCallGraph,
    BuildInternalCall,
    FixFunction,
    EvaluateInference,
)

def fix(file):
    state = State(file)
    chain = FixChain()
    tasks = [
        EnumerateFunction(),
        BuildCallGraph(),
        BuildInternalCall(),
        FixFunction()
    ]
    for task in tasks:
        chain.add_task(task)
    chain.run_chain(state)

def rq1(file):
    state = State(file)
    chain = FixChain()
    tasks = [
        EnumerateFunction(),
        EvaluateInference(),
    ]
    for task in tasks:
        chain.add_task(task)
    chain.run_chain(state)