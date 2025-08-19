"""
Proof of concept for memory tile system
Demonstrates 72-hour TTL and hash pointers
"""

from datetime import datetime, timedelta
import hashlib
import json


class MemoryTile:
    def __init__(self, content, ttl_hours=72):
        self.timestamp = datetime.utcnow()
        self.ttl = timedelta(hours=ttl_hours)
        self.content = content
        self.content_hash = self._hash_content()
        self.summary = None

    def _hash_content(self):
        return hashlib.sha256(json.dumps(self.content).encode()).hexdigest()

    def should_summarize(self):
        return datetime.utcnow() > (self.timestamp + self.ttl)

    def summarize(self):
        # Replace raw content with summary
        self.summary = f"Summary of {len(self.content)} items"
        self.content = None
        return self.summary
