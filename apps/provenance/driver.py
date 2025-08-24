# SPDX-License-Identifier: MIT
from __future__ import annotations
import importlib
import os
from contextlib import contextmanager
from typing import Iterator, Optional, Any


def get_driver(
    uri: Optional[str] = None,
    user: Optional[str] = None,
    password: Optional[str] = None,
) -> Any:
    """
    Create a Neo4j driver using env or explicit args.
    Lazy-imports the neo4j package; raises RuntimeError on missing config/pkg.
    """
    uri = uri or os.getenv("NEO4J_URI")
    user = user or os.getenv("NEO4J_USER")
    password = password or os.getenv("NEO4J_PASSWORD")
    if not (uri and user and password):
        raise RuntimeError("Neo4j configuration missing (NEO4J_URI/USER/PASSWORD).")
    try:
        neo4j = importlib.import_module("neo4j")
    except Exception as e:
        raise RuntimeError("neo4j package not available") from e
    return neo4j.GraphDatabase.driver(uri, auth=(user, password))


@contextmanager
def session(driver: Any, database: Optional[str] = None) -> Iterator[Any]:
    s = driver.session(database=database) if database else driver.session()
    try:
        yield s
    finally:
        try:
            s.close()
        except Exception:
            pass


def apply_startup_schema(driver: Any) -> None:
    """
    Calls schema.apply_constraints(driver). Safe to call multiple times.
    """
    from .schema import apply_constraints

    apply_constraints(driver)
