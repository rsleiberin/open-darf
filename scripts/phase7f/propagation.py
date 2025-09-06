#!/usr/bin/env python3
from __future__ import annotations
from collections import deque
from dataclasses import dataclass
from typing import Dict, Tuple, Callable, Iterable, List, Any
import random, time, json, os, statistics, math, glob

Constraint = Callable[[Any, Any], bool]
Arc = Tuple[str, str]

def revise(domains: Dict[str, List[Any]], xi: str, xj: str, c: Constraint) -> bool:
    """Remove values from D(xi) that have no support in D(xj) under constraint c."""
    removed = False
    new_dom = []
    for vi in domains[xi]:
        if any(c(vi, vj) for vj in domains[xj]):
            new_dom.append(vi)
        else:
            removed = True
    if removed:
        domains[xi] = new_dom
    return removed

def ac3(variables: Iterable[str], domains: Dict[str, List[Any]], constraints: Dict[Arc, Constraint]) -> Tuple[bool, int]:
    """AC-3 algorithm; returns (consistent, revision_count)."""
    q = deque(constraints.keys())
    revisions = 0
    vars_set = set(variables)
    while q:
        xi, xj = q.popleft()
        if revise(domains, xi, xj, constraints[(xi, xj)]):
            revisions += 1
            if len(domains[xi]) == 0:
                return False, revisions
            for xk in vars_set:
                if xk != xi and (xk, xi) in constraints:
                    q.append((xk, xi))
    return True, revisions

def make_random_csp(n_vars=40, domain_size=5, density=0.12, seed=0):
    random.seed(seed)
    variables = [f"X{i}" for i in range(n_vars)]
    domains = {v: list(range(domain_size)) for v in variables}
    constraints: Dict[Arc, Constraint] = {}
    # mix of not-equal and <= constraints for variety
    for i in range(n_vars):
        for j in range(n_vars):
            if i == j: 
                continue
            if random.random() < density:
                t = random.random()
                if t < 0.5:
                    constraints[(variables[i], variables[j])] = lambda a,b: a != b
                else:
                    constraints[(variables[i], variables[j])] = lambda a,b: a <= b or a == b
    return variables, domains, constraints

def bench(iterations=100, **csp_kwargs):
    times = []
    consistent_count = 0
    revisions_total = 0
    for k in range(iterations):
        variables, domains, constraints = make_random_csp(seed=k, **csp_kwargs)
        t0 = time.perf_counter()
        ok, revisions = ac3(variables, domains, constraints)
        dt = (time.perf_counter() - t0) * 1000.0  # ms
        times.append(dt)
        if ok: 
            consistent_count += 1
        revisions_total += revisions
    p50 = statistics.median(times)
    p95 = sorted(times)[max(0, math.ceil(0.95*len(times))-1)]
    return {
        "iterations": iterations,
        "p50_ms": p50,
        "p95_ms": p95,
        "max_ms": max(times),
        "min_ms": min(times),
        "consistent_runs": consistent_count,
        "revisions_total": revisions_total
    }

def write_bench_receipt(outdir: str, summary: dict):
    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, "summary.json")
    with open(path, "w") as f:
        json.dump(summary, f, indent=2)
    print(path, end="")

if __name__ == "__main__":
    # quick CLI for local bench
    ts = time.strftime("%Y%m%d-%H%M%S", time.gmtime())
    outdir = f"var/receipts/phase7f/propagation_perf/{ts}"
    result = bench(iterations=120, n_vars=42, domain_size=6, density=0.15)
    write_bench_receipt(outdir, {
        "phase": "7F",
        "mode": "propagation_bench",
        "generated_at_utc": ts,
        "params": {"iterations": 120, "n_vars": 42, "domain_size": 6, "density": 0.15},
        "summary": result
    })
