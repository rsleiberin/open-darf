"""Rule registry for constitutional scope decisions.

- Service-free, pure-Python.
- One global singleton (module-level helpers) for simple wiring.
- Rules are callables returning one of: "ALLOW" | "DENY" | "INDETERMINATE".
- Duplicate registrations raise; unknown lookups raise; fail-closed remains the guard's job.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Dict, Mapping


Decision = str  # "ALLOW" | "DENY" | "INDETERMINATE"
RuleFn = Callable[..., Decision]


@dataclass(frozen=True)
class Rule:
    name: str
    fn: RuleFn


class RuleRegistry:
    def __init__(self) -> None:
        self._rules: Dict[str, Rule] = {}

    def register(self, name: str, fn: RuleFn) -> None:
        if not name or not callable(fn):
            raise ValueError("Rule name and callable fn are required")
        if name in self._rules:
            raise KeyError(f"Rule '{name}' already registered")
        self._rules[name] = Rule(name=name, fn=fn)

    def get(self, name: str) -> RuleFn:
        try:
            return self._rules[name].fn
        except KeyError as e:
            raise KeyError(f"Unknown rule '{name}'") from e

    def has(self, name: str) -> bool:
        return name in self._rules

    def names(self) -> Mapping[str, str]:
        # return lightweight mapping: rule_name -> function_name
        return {n: r.fn.__name__ for n, r in self._rules.items()}


# Singleton helpers (opt-in for simple wiring)
_registry = RuleRegistry()


def register(name: str, fn: RuleFn) -> None:
    _registry.register(name, fn)


def get(name: str) -> RuleFn:
    return _registry.get(name)


def has(name: str) -> bool:
    return _registry.has(name)


def names() -> Mapping[str, str]:
    return _registry.names()


__all__ = [
    "Decision",
    "RuleFn",
    "Rule",
    "RuleRegistry",
    "register",
    "get",
    "has",
    "names",
]
