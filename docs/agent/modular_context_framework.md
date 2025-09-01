# Modular Context Framework - Project Files Structure

## Dynamic Context Files (Update Per Session)

### Files to check each session:
1. `checklist.json` - Active task tracking
2. `handoff_latest.md` - Previous session context
3. `tech_stack.yaml` - Technology decisions
4. `current_phase.md` - Active development focus

## Migration Path to Anchor System

### Phase 1: Current File-Based (NOW)
- Project instructions: AGENT_OPERATING_CORE.md (permanent)
- Project files: Modular context files (dynamic)

### Phase 2: MinIO Blob Storage (NEXT)
- Store context blobs with SHA-256 anchors
- Version control for context evolution

### Phase 3: Neo4j Graph Integration (FUTURE)
- Checklist nodes with status tracking
- Automatic UI injection of progress bars
- Constitutional validation of task completion
