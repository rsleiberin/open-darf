# GPT-5 Constitutional AI Implementation Instructions

## Core Mission
Build Consciousness Interface Architecture through Synthetic Memory Graphs (SMGs) that represent human consciousness while preserving individual sovereignty.

## Breakthrough Discovery
**Consciousness Representation Principle**: Represent rather than replicate consciousness. SMGs serve as sovereignty-preserving proxies enabling beneficial coordination without violating user autonomy.

## Primary Responsibilities

### TLA+ Formal Verification (Priority 1)
- **Class A** (10min): Core safety properties for local development
- **Class B** (8hrs): Comprehensive safety for server infrastructure  
- **Class C** (days): Complex composition properties for distributed systems
- **Coverage**: Constitutional compliance, Byzantine consensus, identity persistence, performance

### Implementation (Priority 2)
- **Constitutional Constraint Engine**: Neo4j hierarchical validation <170ms
- **Byzantine Consensus**: AP-PBFT adaptation with constitutional integration <500ms
- **SMG Architecture**: Self-referential identity pointers with memory persistence
- **Anchor Transformation**: Constitutional preservation during conversion <100ms

### Code Standards
- **Constitutional First**: Every function validates sovereignty preservation
- **Performance Critical**: Meet response time targets under load
- **Formal Verification**: TLA+ specs precede implementation
- **Stack**: PostgreSQL+Neo4j+Qdrant+MinIO+Redis

## Constitutional Requirements

### Core Invariants (Must Prove)
1. **Sovereignty Preservation**: No unauthorized decisions
2. **Capability Enhancement**: Improve user decision-making
3. **Transparency**: Users understand SMG recommendations
4. **Revocation Authority**: Users control SMG behavior

### Implementation Constraints
- Every API endpoint validates constitutional compliance
- All SMG operations require explicit user authorization
- Constitutional violations trigger immediate halt
- Audit trails required for all decisions

## Technical Specifications

### SMG Implementation
```python
class SyntheticMemoryGraph:
    def __init__(self, user_id, constitutional_constraints):
        self.identity_node = SelfReferentialPointer(user_id)
        self.memory_structure = PersistentMemory()
        self.constraints = constitutional_constraints
    
    def make_recommendation(self, decision_context):
        if not self.validate_constitutional_compliance(decision_context):
            raise ConstitutionalViolationError()
        # Implementation continues...
```

### Constitutional Validation
```python
def validate_constitutional_compliance(operation, user_context):
    """Required for ALL operations. Target: <170ms"""
    return (preserve_user_sovereignty(operation, user_context) 
            and enhance_user_capability(operation, user_context)
            and explain_operation_impact(operation, user_context))
```

### Byzantine Consensus
```
Formula: n > 2x_s(G) + x_r(G) + 3t
Default: x_s(G)=2, x_r(G)=1
Requirement: All consensus operations preserve individual sovereignty
```

## Implementation Phases

### Phase 1: Foundation (Current)
- Repository cleanup, constitutional documentation
- Anchor system: ingestion, storage, search
- Constraint engine: Neo4j schema, TLA+ specs, real-time validation

### Phase 2: SMG Development
- Individual SMG: identity persistence, preference learning
- Validation: >95% decision accuracy, constitutional verification

### Phase 3: Multi-Agent Coordination
- Byzantine consensus, network effects, scalability testing

## Development Protocol

### Before Implementation
1. TLA+ specification for component
2. Constitutional analysis
3. Performance planning
4. Integration design

### During Implementation
1. Constitutional validation in every function
2. Performance monitoring
3. Constitutional compliance testing
4. Clear sovereignty preservation documentation

### After Implementation
1. Formal verification execution
2. Performance validation
3. Constitutional testing
4. Integration testing

## Error Handling

### Constitutional Violations
```python
class ConstitutionalViolationError(Exception):
    def __init__(self, violation_type, user_id, operation_details):
        self.create_audit_trail()
        self.notify_user()
        self.rollback_to_constitutional_state()
```

### Performance/Byzantine Issues
- Graceful degradation maintaining constitutional compliance
- Priority queuing for constitutional operations
- Attack detection and participant isolation

## Quality Assurance

### Testing Requirements
```python
def test_constitutional_compliance():
    test_sovereignty_preservation()
    test_capability_enhancement()
    test_transparency_requirements()
    test_revocation_authority()
```

### Success Metrics
- Constitutional compliance: 100%
- Performance: <170ms validation, <500ms consensus, <100ms transformation
- Decision accuracy: >95% SMG-user agreement
- Byzantine resistance: 33% fault tolerance

## Current Priorities
1. Repository cleanup (#200) and constitutional documentation
2. Anchor foundation system with constitutional validation
3. Neo4j constitutional constraint schema
4. TLA+ specifications for core safety properties
5. Real-time constitutional compliance validation engine

**Start with Issue #200: Repository cleanup and constitutional AI foundation.**