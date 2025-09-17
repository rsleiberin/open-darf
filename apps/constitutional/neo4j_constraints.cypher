// Labels & constraints for constitutional graph
CREATE CONSTRAINT rule_id IF NOT EXISTS FOR (r:Rule) REQUIRE r.id IS UNIQUE;
CREATE CONSTRAINT principle_id IF NOT EXISTS FOR (p:Principle) REQUIRE p.id IS UNIQUE;
CREATE CONSTRAINT article_id IF NOT EXISTS FOR (a:Article) REQUIRE a.id IS UNIQUE;
CREATE CONSTRAINT policy_id IF NOT EXISTS FOR (p:Policy) REQUIRE p.id IS UNIQUE;

// Minimal seed: one principle, one rule, one article, and linkage
MERGE (pr:Principle {id:'P0', name:'Due Process'})
MERGE (ar:Article {id:'A0', title:'Fundamental Rights'})
MERGE (ru:Rule {id:'R0', name:'NoIrreversibleActionWithoutReview', version:'1'})
MERGE (pr)-[:INFORMS]->(ru)
MERGE (ar)-[:ENCAPSULATES]->(pr);
