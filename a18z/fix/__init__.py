from .chain import FixChain
from .state import State
from .task import (
    EnumerateFunction,
    BuildCallGraph,
    FixFunction,
    EvaluateInference,
    EvaluateCallsite,
    BuildCluster,
    TestFunction,
)

def test(file):
    state = State(file)
    chain = FixChain()
    tasks = [
        EnumerateFunction(),
        TestFunction(),
    ]
    for task in tasks:
        chain.add_task(task)
    chain.run_chain(state)

def fix(file):
    state = State(file)
    chain = FixChain()
    tasks = [
        EnumerateFunction(),
        BuildCallGraph(),
        BuildCluster(),
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

def rq2(file):
    state = State(file)
    chain = FixChain()
    tasks = [
        EnumerateFunction(),
        EvaluateCallsite()
    ]
    for task in tasks:
        chain.add_task(task)
    chain.run_chain(state)