CREATE CONSTRAINT entity_uid IF NOT EXISTS FOR (e:Entity) REQUIRE e.uid IS UNIQUE;
CREATE CONSTRAINT hyperedge_uid IF NOT EXISTS FOR (h:HyperEdge) REQUIRE h.uid IS UNIQUE;
CREATE INDEX entity_etype IF NOT EXISTS FOR (e:Entity) ON (e.etype);
CREATE INDEX entity_name IF NOT EXISTS FOR (e:Entity) ON (e.name);
CREATE INDEX hyperedge_relation IF NOT EXISTS FOR (h:HyperEdge) ON (h.relation);
