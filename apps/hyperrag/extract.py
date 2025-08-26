from __future__ import annotations
import re
from typing import List
from .model import Entity, Span, new_id


class EntityExtractor:
    """Interface: implement extract(text) -> List[Entity]."""

    def extract(self, text: str) -> List[Entity]:
        raise NotImplementedError


class RegexEntityExtractor(EntityExtractor):
    """
    Extremely lightweight baseline to keep CI service-free.
    - Detects capitalized tokens or Title Case multi-words as 'Concept'.
    - Intended to be replaced by a proper NER model later.
    """

    _pat = re.compile(
        r"\b([A-Z][a-z]+(?:\s+[A-Z][a-z]+)*)\b|" r"\b([A-Z]{2,}(?:\s+[A-Z][a-z]+)*)\b"
    )

    def extract(self, text: str) -> List[Entity]:
        entities: List[Entity] = []
        for m in self._pat.finditer(text or ""):
            s, e = m.span()
            t = m.group(0)
            entities.append(
                Entity(uid=new_id("ent"), etype="Concept", name=t, span=Span(s, e, t))
            )
        # de-dup by surface form
        seen = set()
        uniq = []
        for ent in entities:
            key = (ent.etype, ent.name.lower())
            if key in seen:
                continue
            seen.add(key)
            uniq.append(ent)
        return uniq
