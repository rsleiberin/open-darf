# SPDX-License-Identifier: MIT
import os

# Import SQLAlchemy if available; otherwise skip the whole module.
try:
    from sqlalchemy import create_engine, text  # type: ignore
except Exception:
    import pytest

    pytest.skip(
        "sqlalchemy missing; skipping Postgres connection test", allow_module_level=True
    )

DATABASE_URL = os.getenv("DATABASE_URL")


def test_postgres_connect_and_query(tmp_path):
    if not DATABASE_URL:
        import pytest

        pytest.skip("DATABASE_URL not set")
    eng = create_engine(DATABASE_URL)
    with eng.connect() as conn:
        result = conn.execute(text("SELECT 1")).scalar()
        assert result == 1
