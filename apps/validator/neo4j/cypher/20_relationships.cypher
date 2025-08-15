/* Relationship types (living docs; creation happens in code/ETL)
   :OWNS         (User)-[:OWNS]->(SMG)
   :GOVERNS      (Constraint)-[:GOVERNS]->(Operation)
   :APPLIES_TO   (Constraint)-[:APPLIES_TO]->(Decision)
   :PRODUCES     (SMG)-[:PRODUCES]->(Decision)
   :AUDITS       (Decision)-[:AUDITS]->(Operation)
*/
