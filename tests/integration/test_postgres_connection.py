import os
import pytest
from sqlalchemy import create_engine, text

DATABASE_URL = os.getenv("DATABASE_URL")

if not DATABASE_URL:
    pytest.skip("DATABASE_URL not set; skipping integration test", allow_module_level=True)

def test_postgres_connection():
    engine = create_engine(DATABASE_URL, echo=False, pool_pre_ping=True)
    with engine.connect() as conn:
        result = conn.execute(text("SELECT 1")).scalar()
        assert result == 1
