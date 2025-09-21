# Validation Guide

## Quick Validation

Run complete validation suite:
~~~bash
./validate
~~~

## What Gets Validated

- Constitutional constraint enforcement (sub-millisecond overhead)
- Database integrity and performance
- Evidence generation and cryptographic signing
- Cross-platform compatibility

## Understanding Results

Validation generates evidence packages in timestamped directories containing:
- Performance metrics and timing data
- System configuration snapshots  
- Cryptographic proofs of constraint satisfaction
- Academic-suitable documentation

## Success Criteria

- All services start and respond to health checks
- Constitutional constraints validate within timeout
- Evidence packages generate with valid signatures
- No security violations detected
