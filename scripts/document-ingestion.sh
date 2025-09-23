#!/bin/bash
set -euo pipefail

# Directories
DOCS_DIR="docs"
OUTPUT_DIR="docs/automation/ingestion_output"
LOG_FILE="${OUTPUT_DIR}/ingestion.log"

# Ensure output dir exists
mkdir -p "$OUTPUT_DIR"

echo "📂 Starting document ingestion..."
date +"%Y-%m-%d %H:%M:%S" | tee "$LOG_FILE"

# 1. Index all candidate docs
echo "🔍 Indexing documents in ${DOCS_DIR}..." | tee -a "$LOG_FILE"
find "$DOCS_DIR" \
    -type f \
    \( -iname "*.md" -o -iname "*.pdf" -o -iname "*.txt" \) \
    ! -iname "*Zone.Identifier" \
    | sort | tee "${OUTPUT_DIR}/doc_index.txt"

# 2. Summary counts
echo "📊 File type counts:" | tee -a "$LOG_FILE"
grep -E "\\.md$" "${OUTPUT_DIR}/doc_index.txt" | wc -l | xargs echo "Markdown:" | tee -a "$LOG_FILE"
grep -E "\\.pdf$" "${OUTPUT_DIR}/doc_index.txt" | wc -l | xargs echo "PDF:" | tee -a "$LOG_FILE"
grep -E "\\.txt$" "${OUTPUT_DIR}/doc_index.txt" | wc -l | xargs echo "Text:" | tee -a "$LOG_FILE"

# 3. Manual triage
echo "📝 Please review /doc_index.txt and categorize each file."
echo "Format: <category> <relative_path>   # Example: architecture docs/reference/backend_stack_overview.md" | tee -a "$LOG_FILE"

# 4. Placeholder manifest
awk "{print \"unclassified \" \$0}" "${OUTPUT_DIR}/doc_index.txt" > "${OUTPUT_DIR}/doc_manifest.tsv"
echo "✅ Manifest created at ${OUTPUT_DIR}/doc_manifest.tsv"

# 5. (Future) Hook for automatic chunking / metadata extraction
# python tools/chunk_docs.py --input "${OUTPUT_DIR}/doc_manifest.tsv"

echo "🚀 Ingestion phase complete."
