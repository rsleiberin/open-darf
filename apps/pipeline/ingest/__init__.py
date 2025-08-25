"""Ingest sources (MinIO/local)."""

from typing import Iterable, Protocol


class IngestSource(Protocol):
    def list(self) -> Iterable[str]: ...
    def fetch(self, ref: str) -> bytes: ...
