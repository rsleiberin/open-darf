CREATE SCHEMA IF NOT EXISTS audit;

CREATE TABLE IF NOT EXISTS audit.receipts (
  id            BIGSERIAL PRIMARY KEY,
  ts_utc        TIMESTAMPTZ NOT NULL DEFAULT now(),
  component     TEXT NOT NULL,            -- e.g., 'constitutional_engine'
  action        TEXT NOT NULL,            -- e.g., 'rule_eval'
  status        TEXT NOT NULL,            -- 'success'|'failure'
  details       JSONB,                    -- arbitrary structured details
  sha256        TEXT,                     -- optional integrity anchor
  duration_ms   INTEGER                   -- optional timing
);

CREATE TABLE IF NOT EXISTS audit.events (
  id            BIGSERIAL PRIMARY KEY,
  ts_utc        TIMESTAMPTZ NOT NULL DEFAULT now(),
  category      TEXT NOT NULL,            -- e.g., 'validation_gate'
  message       TEXT NOT NULL,
  context       JSONB
);
