#!/usr/bin/env python3
"""Issue #41: Smoke-test Postgres SA engine"""

from sqlalchemy import create_engine, text, MetaData, Table, Column, Integer, String
from sqlalchemy.orm import sessionmaker

# Connection string
DATABASE_URL = "postgresql://janus:januspass@localhost:5432/janus_adr"

def test_connection() -> None:
    """Test basic PostgreSQL connection and operations"""
    print("Testing PostgreSQL connection...")
    
    # Create engine
    engine = create_engine(DATABASE_URL, echo=True)
    
    # Test 1: Basic connection
    with engine.connect() as conn:
        result = conn.execute(text("SELECT 1"))
        print(f"✓ Connection successful: {result.scalar()}")
    
    # Test 2: Create a test table
    metadata = MetaData()
    test_table = Table(
        'smoke_test',
        metadata,
        Column('id', Integer, primary_key=True),
        Column('name', String(50))
    )
    
    metadata.create_all(engine)
    print("✓ Table creation successful")
    
    # Test 3: Insert and query
    Session = sessionmaker(bind=engine)
    with Session() as session:
        session.execute(
            test_table.insert().values(name="ADR System Test")
        )
        session.commit()
        
        result = session.execute(test_table.select()).first()  # type: ignore[assignment]
        print(f"✓ Insert/Query successful: {result}")
    
    # Cleanup
    metadata.drop_all(engine)
    print("✓ Cleanup successful")
    print("\n✅ All PostgreSQL tests passed!")

if __name__ == "__main__":
    test_connection()  # type: ignore
