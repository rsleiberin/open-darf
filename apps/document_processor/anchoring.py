import hashlib
import time
from dataclasses import dataclass
from typing import List, Dict


@dataclass
class Paragraph:
    content: str
    start_byte: int
    end_byte: int


@dataclass
class DocForAnchoring:
    doc_type: str
    content: bytes
    paragraphs: List[Paragraph]


def _sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def create_anchor_hierarchy(doc: DocForAnchoring) -> Dict[str, object]:
    """
    Returns:
      {
        "base_anchor": "sha256:<hash>:<doc_type>:<ts>",
        "paragraph_anchors": [ "...", ... ],
    }
    """
    base = f"sha256:{_sha(doc.content)}:{doc.doc_type}:{int(time.time())}"
    subs = []
    for i, p in enumerate(doc.paragraphs):
        subs.append(
            f"{base}:para_{i}:{p.start_byte}:{p.end_byte}:{_sha(p.content.encode('utf-8'))}"
        )
    return {"base_anchor": base, "paragraph_anchors": subs}
