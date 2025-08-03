# Issue-Label Taxonomy

| Category | Prefix | Examples |
|----------|--------|----------|
| **Type** | `type:` | `type:feature`, `type:bug` |
| **Priority** | `priority:` | `priority:high`, `priority:medium` |
| **Status** | `status:` | `status:in-progress`, `status:review`, `status:done` |
| **Area** | `area:` | `area:ui`, `area:backend`, `area:infra` |

The **Sane Label System** gives every issue exactly **one** label from each category:

* **Type** → what kind of work  
* **Priority** → urgency  
* **Status** → current workflow state (drives automations)  
* **Area** → codebase or domain slice

`./scripts/labels.sh` is the single source of truth & can be re-run at any time to sync colours/descriptions or add new labels.

* **Blocked by** – list prerequisite issues that must be resolved first (e.g. #12, #34).
