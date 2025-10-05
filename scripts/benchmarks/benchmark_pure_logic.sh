#!/usr/bin/env bash
set -euo pipefail
ITERATIONS=${1:-10000}
WARMUP=$((ITERATIONS / 10))
echo "=== Pure Constitutional Logic Microbenchmark ===" >&2
echo "Iterations: $ITERATIONS (warmup: $WARMUP)" >&2
python3 -c "
import time
import statistics
import sys

def constitutional_decision(context, rule_data):
    if rule_data['requires_review_for_irreversible'] and context['irreversible'] and not context['has_review']:
        return ('DENY', 'irreversible_action_without_required_review')
    elif not context['irreversible']:
        return ('ALLOW', 'reversible_action_permitted')
    return ('INDETERMINATE', 'insufficient_data')

rule_cache = {'R0': {'requires_review_for_irreversible': True, 'priority': 1}}
contexts = [
    {'irreversible': True, 'has_review': False},
    {'irreversible': False, 'has_review': False},
    {'irreversible': True, 'has_review': True}
]

iterations = $ITERATIONS
warmup = $WARMUP

for _ in range(warmup):
    for ctx in contexts:
        constitutional_decision(ctx, rule_cache['R0'])

times_ns = []
for _ in range(iterations):
    for ctx in contexts:
        start = time.perf_counter_ns()
        result = constitutional_decision(ctx, rule_cache['R0'])
        end = time.perf_counter_ns()
        times_ns.append(end - start)

times_ns.sort()
p50 = times_ns[len(times_ns) // 2]
p95 = times_ns[int(len(times_ns) * 0.95)]
p99 = times_ns[int(len(times_ns) * 0.99)]
mean_val = statistics.mean(times_ns)
min_val = min(times_ns)
max_val = max(times_ns)
p50_us = p50 / 1000
p50_ms = p50 / 1_000_000

print('{')
print('  \"measurement_layer\": \"pure_logic\",')
print(f'  \"iterations\": {iterations * 3},')
print(f'  \"warmup_iterations\": {warmup * 3},')
print('  \"nanoseconds\": {')
print(f'    \"p50\": {p50},')
print(f'    \"p95\": {p95},')
print(f'    \"p99\": {p99},')
print(f'    \"mean\": {int(mean_val)},')
print(f'    \"min\": {min_val},')
print(f'    \"max\": {max_val}')
print('  },')
print('  \"microseconds\": {')
print(f'    \"p50\": {p50_us:.6f},')
print(f'    \"p95\": {p95/1000:.6f},')
print(f'    \"p99\": {p99/1000:.6f}')
print('  },')
print('  \"milliseconds\": {')
print(f'    \"p50\": {p50_ms:.9f},')
print(f'    \"p95\": {p95/1_000_000:.9f},')
print(f'    \"p99\": {p99/1_000_000:.9f}')
print('  },')
print('  \"methodology\": \"In-memory decision logic with pre-loaded rules\",')
print('  \"excludes\": [\"file_io\", \"database_queries\", \"network_calls\", \"docker_overhead\"],')
print('  \"claim\": \"Pure computational overhead of constitutional decision logic\"')
print('}')
"
