CREATE CONSTRAINT unique_principle_id IF NOT EXISTS FOR (p:Principle) REQUIRE p.id IS UNIQUE;
CREATE INDEX idx_principle_type IF NOT EXISTS FOR (p:Principle) ON (p.type);
CREATE INDEX idx_constraint_key IF NOT EXISTS FOR (c:Constraint) ON (c.key);
