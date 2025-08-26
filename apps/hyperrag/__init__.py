"""HyperGraphRAG: minimal, service-free scaffold.

Re-exports for public API.
"""

from .model import (
    Entity as Entity,
    Span as Span,
    HyperEdge as HyperEdge,
    Fact as Fact,
    new_id as new_id,
)

__all__ = ["Entity", "Span", "HyperEdge", "Fact", "new_id"]
