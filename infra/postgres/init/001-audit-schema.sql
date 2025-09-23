CREATE TABLE IF NOT EXISTS constitutional_decisions (
  id SERIAL PRIMARY KEY,
  decision_id VARCHAR(255) UNIQUE NOT NULL,
  principle_applied VARCHAR(255) NOT NULL,
  decision_outcome VARCHAR(50) NOT NULL,
  reasoning_chain TEXT,
  timestamp TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
