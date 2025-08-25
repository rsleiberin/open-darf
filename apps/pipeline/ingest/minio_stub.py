"""Non-networked MinIO stub: validates configuration but does not perform I/O.

This keeps CI hermetic. A real MinIO client can replace this under a feature flag.
"""

from typing import Iterable


class MinioIngestStub:
    def __init__(self, *_, **__):
        self._objects = []  # empty by default

    def prime(self, refs_and_bytes):
        """Supply fake objects for tests: [(name, bytes), ...]."""
        self._objects = list(refs_and_bytes)

    def list(self) -> Iterable[str]:
        return [name for name, _ in self._objects]

    def fetch(self, ref: str) -> bytes:
        for name, data in self._objects:
            if name == ref:
                return data
        raise FileNotFoundError(ref)
