from pathlib import Path
from typing import Iterable


class LocalFSIngest:
    """Local filesystem ingest rooted at a directory path."""

    def __init__(self, root: str):
        self.root = Path(root)

    def list(self) -> Iterable[str]:
        if not self.root.exists():
            return []
        for p in self.root.rglob("*"):
            if p.is_file():
                yield str(p.relative_to(self.root))

    def fetch(self, ref: str) -> bytes:
        p = self.root / ref
        data = p.read_bytes()
        return data
