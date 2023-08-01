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
    RQ3,
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

def rq3(file):
    state = State(file)
    chain = FixChain()
    tasks = [
        EnumerateFunction(),
        BuildCallGraph(),
        RQ3(),
    ]
    for task in tasks:
        chain.add_task(task)
    chain.run_chain(state)

def rq1(file):
    state = State(file)
    chain = FixChain()
    tasks = [
        EnumerateFunction(),
        BuildCallGraph(),
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
        BuildCallGraph(),
        EvaluateCallsite()
    ]
    for task in tasks:
        chain.add_task(task)
    chain.run_chain(state)