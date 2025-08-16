from __future__ import annotations
import hashlib, json, time
from dataclasses import dataclass, asdict, field
from typing import List, Optional, Dict, Any

def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

@dataclass
class Span:
    id: str
    start: int
    end: int
    # Optional locator for PDFs/HTML, etc.
    # Example: {"kind":"pdf","page":3,"rect":[x1,y1,x2,y2]} or {"kind":"html","selector":"#main p:nth-child(2)"}
    loc: Optional[Dict[str, Any]] = None
    # Per-span provenance (kept minimal): {"auth_class":"owner|trusted|untrusted","user_id":"..."}
    provenance: Dict[str, Any] = field(default_factory=dict)
    # Transformation lineage, e.g., [{"op":"chunker/linebreak-v1","parent":"sha256-..."}]
    lineage: List[Dict[str, Any]] = field(default_factory=list)

@dataclass
class ManifestV1:
    # Content-addressed span manifest
    version: str
    # {"digest":"sha256-<hex>","bytes":int,"type":"text/plain|application/pdf|..."}
    doc: Dict[str, Any]
    spans: List[Span]
    # End-to-end provenance for the manifest itself
    # {"source":"ingest","time":<unix>,"auth_class":"...","user_id":"..."}
    provenance: Dict[str, Any]

    def dumps(self) -> bytes:
        return json.dumps(asdict(self), ensure_ascii=False, separators=(",", ":")).encode("utf-8")

def build_manifest_v1(
    doc_bytes: bytes,
    doc_type: str,
    spans: List[Span],
    user_id: str,
    auth_class: str
) -> bytes:
    doc_digest = f"sha256-{sha256_hex(doc_bytes)}"
    m = ManifestV1(
        version="1",
        doc={"digest": doc_digest, "bytes": len(doc_bytes), "type": doc_type},
        spans=spans,
        provenance={"source": "ingest", "time": int(time.time()), "auth_class": auth_class, "user_id": user_id},
    )
    return m.dumps()
