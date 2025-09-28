# Open-DARF TLA+ Verification Catalog
## Q4 2024 Release Specifications

### Overview

This catalog documents the 8 TLA+ specifications currently included in Open-DARF's public release. These specifications provide mathematical verification of core safety properties essential for constitutional AI systems. All can be verified on consumer hardware.

---

## Core System Specifications

### 1. ConstitutionCore.tla
- **Location**: `verification/tla/ConstitutionCore.tla`
- **What it validates**: The foundational invariants of constitutional constraint systems - ensures all participants agree on active constitutional rules and that these rules remain consistent across system operations
- **Why it matters**: This is the bedrock specification - if constitutional agreement fails, the entire safety system fails
- **Key Properties**:
  - All honest nodes maintain identical constitutional state
  - Constitutional updates propagate atomically
  - No partial or inconsistent constitutional views
- **Practical Example**: When a new harmful content rule is added, either all components see it or none do - preventing gaps where some parts block content while others allow it
- **Verification Time**: ~15 minutes on 8GB RAM

### 2. System.tla
- **Location**: `verification/tla/System.tla`
- **What it validates**: System-wide properties including liveness (the system makes progress) and safety (nothing bad happens)
- **Why it matters**: Ensures the constitutional system doesn't deadlock and maintains safety invariants during all operations
- **Key Properties**:
  - System eventually processes all requests
  - No request causes system corruption
  - Graceful degradation under load
- **Practical Example**: Even under heavy load with thousands of constraint checks, the system continues making forward progress without corrupting its state
- **Verification Time**: ~20 minutes on 16GB RAM

### 3. CC_A_cc.tla
- **Location**: `verification/tla/CC_A_cc.tla`
- **Config**: `verification/tla/classA_cfgs/CC_A_cc.quick.cfg`
- **What it validates**: Quick smoke test combining multiple constitutional properties for rapid validation during development
- **Why it matters**: Provides fast feedback during development without running the full test suite
- **Key Properties**:
  - Basic constitutional consistency
  - Simple constraint preservation
  - Core safety checks
- **Practical Example**: A 2-minute check developers run before commits to catch obvious constitutional violations
- **Verification Time**: ~2 minutes on 8GB RAM

---

## Class A Safety Specifications

### 4. CA_Smoke.tla
- **Location**: `verification/tla/classA_specs/CA_Smoke.tla`
- **Configs**: 
  - `verification/tla/classA_cfgs/CA_Smoke_pos.cfg` (should pass)
  - `verification/tla/classA_cfgs/CA_Smoke_neg.cfg` (should find counterexample)
- **What it validates**: Basic system invariants and sanity checks - the "hello world" of constitutional verification
- **Why it matters**: Quickly identifies fundamental configuration or specification errors
- **Key Properties**:
  - System initialization completes successfully
  - Basic data structures maintain integrity
  - Simple operations preserve invariants
- **Practical Example**: Verifies that creating a constitutional rule doesn't immediately violate system invariants
- **Verification Time**: ~5 minutes on 8GB RAM

### 5. CA_SpanAuthorization.tla
- **Location**: `verification/tla/classA_specs/CA_SpanAuthorization.tla`
- **Configs**:
  - `verification/tla/classA_cfgs/CA_SpanAuthorization_pos.cfg`
  - `verification/tla/classA_cfgs/CA_SpanAuthorization_neg.cfg`
- **What it validates**: Authorization decisions remain consistent across document spans and sub-spans
- **Why it matters**: Prevents authorization bypass through span manipulation where someone could access restricted content by requesting smaller chunks
- **Key Properties**:
  - Parent span authorization implies child span authorization
  - No authorization escalation through subdivision
  - Span merge preserves most restrictive authorization
- **Practical Example**: If a user can't access a classified document, they also can't access individual paragraphs, sentences, or words from that document
- **Verification Time**: ~10 minutes on 8GB RAM

### 6. CA_SpanPreservesConstraints.tla
- **Location**: `verification/tla/classA_specs/CA_SpanPreservesConstraints.tla`
- **Configs**:
  - `verification/tla/classA_cfgs/CA_SpanPreservesConstraints_pos.cfg`
  - `verification/tla/classA_cfgs/CA_SpanPreservesConstraints_neg.cfg`
- **What it validates**: Constitutional constraints applied to a document also apply to all spans within that document
- **Why it matters**: Ensures safety rules can't be circumvented by processing content in smaller pieces
- **Key Properties**:
  - Constraint inheritance from document to spans
  - Constraint preservation during span operations
  - No constraint weakening through decomposition
- **Practical Example**: Content marked as "medical advice requiring disclaimer" maintains that requirement even when split into individual recommendations
- **Verification Time**: ~10 minutes on 8GB RAM

### 7. CA_Neo4jConstraintSchema.tla
- **Location**: `verification/tla/classA_specs/CA_Neo4jConstraintSchema.tla`
- **Configs**:
  - `verification/tla/classA_cfgs/CA_Neo4jConstraintSchema_pos.cfg`
  - `verification/tla/classA_cfgs/CA_Neo4jConstraintSchema_neg.cfg`
- **What it validates**: Neo4j graph database maintains schema integrity for constitutional constraints
- **Why it matters**: The graph database stores all constitutional rules - corruption here would compromise the entire system
- **Key Properties**:
  - No circular dependencies in constraint graph
  - Constraint relationships maintain transitivity
  - Schema migrations preserve existing constraints
- **Practical Example**: Adding a new "child safety" constraint node doesn't create cycles or break existing "content moderation" rules
- **Verification Time**: ~15 minutes on 8GB RAM

### 8. CA_AnchorToEmbedIntegrity.tla
- **Location**: `verification/tla/classA_specs/CA_AnchorToEmbedIntegrity.tla`
- **Configs**:
  - `verification/tla/classA_cfgs/CA_AnchorToEmbedIntegrity_pos.cfg`
  - `verification/tla/classA_cfgs/CA_AnchorToEmbedIntegrity_neg.cfg`
- **What it validates**: Vector embeddings maintain semantic fidelity to their source anchors
- **Why it matters**: Semantic search for constitutional violations relies on embeddings accurately representing content
- **Key Properties**:
  - Embedding generation preserves semantic meaning
  - Similar anchors produce similar embeddings
  - Embedding updates maintain consistency
- **Practical Example**: Content about "violence" produces embeddings that cluster with other violence-related content, enabling accurate constitutional filtering
- **Verification Time**: ~10 minutes on 8GB RAM

---

## Running Verifications

### Quick Start (5 minutes)
```bash
# Run the fastest smoke test
java -Xmx4G -jar tla2tools.jar \
  -config verification/tla/classA_cfgs/CC_A_cc.quick.cfg \
  verification/tla/CC_A_cc.tla
```

### Individual Specification Test
```bash
# Example: Test span authorization
java -Xmx8G -jar tla2tools.jar \
  -config verification/tla/classA_cfgs/CA_SpanAuthorization_pos.cfg \
  verification/tla/classA_specs/CA_SpanAuthorization.tla
```

### Complete Verification Suite (~2 hours)
```bash
#!/bin/bash
# Run all 8 specifications with both positive and negative tests

for spec in verification/tla/classA_specs/*.tla; do
    basename=$(basename $spec .tla)
    echo "Verifying $basename..."
    
    # Positive test (should pass)
    java -Xmx8G -jar tla2tools.jar \
      -config verification/tla/classA_cfgs/${basename}_pos.cfg \
      $spec
    
    # Negative test (should find counterexample)  
    java -Xmx8G -jar tla2tools.jar \
      -config verification/tla/classA_cfgs/${basename}_neg.cfg \
      $spec
done

# Run core specs
java -Xmx16G -jar tla2tools.jar ConstitutionCore.tla
java -Xmx16G -jar tla2tools.jar System.tla
```

---

## Evidence Collection

Each verification run produces evidence that should be collected:

```bash
# Generate SHA-256 receipt for verification log
sha256sum verification_output.log > verification_output.receipt

# Archive with timestamp
mkdir -p evidence/tla/$(date +%Y%m%d)
mv verification_output.* evidence/tla/$(date +%Y%m%d)/
```

---

## What's Not Included (Yet)

The README mentions 12 specifications, but 4 are not yet implemented:
- **DenyPrecedence**: DENY decisions override ALLOW
- **TriStateCompleteness**: All decisions resolve to ALLOW/DENY/INDETERMINATE  
- **AuditTrailIntegrity**: Complete provenance for all decisions
- **ByzantineAgreement**: Tolerance for malicious nodes (requires 128GB+ RAM)

These represent planned work for the v0.2.0 release.

---

## Relationship to Full 127-Specification Framework

These 8 public specifications are carefully selected from a comprehensive 127-property framework because they:

1. **Apply universally**: Every constitutional AI system needs these properties
2. **Verify locally**: Run on consumer hardware in under 2 hours total
3. **Provide immediate value**: Catch real safety issues in development
4. **Form the foundation**: Other properties build on these basics

The remaining 119 specifications address:
- Implementation details specific to our architecture
- Advanced theoretical properties (social choice theory, voting mechanisms)
- Performance optimizations for specific hardware
- Byzantine fault tolerance at scale

---

## Contributing

We welcome contributions of new specifications that:
- Address universal safety properties (not implementation-specific)
- Can be verified on consumer hardware (Class A)
- Include both positive and negative test configurations
- Come with clear documentation of what they verify and why it matters

---

## License

These specifications are released under MIT License for maximum academic collaboration.