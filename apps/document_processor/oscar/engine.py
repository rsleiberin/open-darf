# SPDX-License-Identifier: MIT
from __future__ import annotations
from abc import ABC, abstractmethod
from typing import List
import re


class ObjectiveSubstitutionEngine(ABC):
    @abstractmethod
    def generate_alternatives(
        self, text: str, bias_type: str, num_candidates: int = 5
    ) -> List[str]: ...


class TinyObjectiveSubstitutionEngine(ObjectiveSubstitutionEngine):
    def _re_sub_map(self, text: str, mapping: dict) -> str:
        if not mapping:
            return text
        pat = re.compile(
            r"\b(" + "|".join(re.escape(k) for k in mapping.keys()) + r")\b",
            re.IGNORECASE,
        )

        def _repl(m):
            orig = m.group(0)
            val = mapping.get(orig.lower(), orig)
            if orig.isupper():
                return val.upper()
            if orig.istitle():
                return val.capitalize()
            return val

        return pat.sub(_repl, text)

    """
    Rule-based, deterministic substitutions to reduce biased phrasing while keeping meaning.
    Intentionally conservative to keep semantic drift minimal for tests/CI.
    """

    ASSERTIVE = {
        "clearly": "",
        "obviously": "",
        "undeniably": "",
    }
    SUBJECTIVE = {
        "best": "strong",
        "worst": "poor",
        "groundbreaking": "notable",
        "revolutionary": "significant",
    }
    GENDER = {
        "men": "participants",
        "women": "participants",
        "male": "participants",
        "female": "participants",
        "he": "they",
        "she": "they",
    }

    def _apply(self, text: str, bias_type: str) -> str:
        out = text
        low = out.lower()

        def repl_map(s: str, mapping: dict):
            # simple token-ish replacements preserving case where possible
            for k, v in mapping.items():
                out = []
                i = 0
                while i < len(s):
                    if s[i : i + len(k)].lower() == k:
                        # Preserve capitalization if first letter uppercase
                        if s[i : i + len(k)].istitle() and v:
                            rep = v.capitalize()
                        else:
                            rep = v
                        out.append(rep)
                        i += len(k)
                    else:
                        out.append(s[i])
                        i += 1
                s = "".join(out)
            return s

        if bias_type == "gender_bias":
            out = self._re_sub_map(out, self.GENDER)
        elif bias_type == "methodology_bias":
            # soften assertives and add a neutral clarification phrase if missing methods are implied
            out = repl_map(out, self.ASSERTIVE)
            if "no methodology" in low or "no methods" in low:
                out = out + " Further methodological details will be provided."
        elif bias_type in {"representation_bias", "outcome_bias", "citation_bias"}:
            out = repl_map(out, self.SUBJECTIVE)
            out = repl_map(out, self.ASSERTIVE)
        else:
            out = repl_map(out, self.ASSERTIVE)
        return out

    def generate_alternatives(
        self, text: str, bias_type: str, num_candidates: int = 5
    ) -> List[str]:
        base = self._apply(text, bias_type)
        # produce small variants (dedup conservatively)
        variants = {base}
        if bias_type == "gender_bias":
            variants.add(base.replace("participants participants", "participants"))
        if bias_type == "citation_bias":
            variants.add(base.replace("significant", "substantial"))
        return list(variants)[: max(1, min(5, num_candidates))]
