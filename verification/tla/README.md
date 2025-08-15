# TLA Verification Area (canonical)

**Active home:** `verification/tla/`  
**Runs are git-ignored** under `verification/tla/runs` (only `_reports/*.md` are tracked).

## Class A (toy) validations
Specs: `verification/tla/classA_specs/*.tla`  
Models: `verification/tla/models/classA_new/*.cfg`  
Run all: `verification/tla/scripts/run_class_a_now.sh`

- CA_ConstCompliance (bounded monotonicity)
- CA_BFT_QuorumEnum (explicit quorum-set exploration)
- CA_ExplicitAuthorization (records, derived Grants)
- CA_JoinAtMostOnce (set grows once per node)
- CA_IdentityPersistence (core fields immutable)
- CA_CapabilityEnhancement (cap sets grow monotonically)
- CA_RevocationAuthority (only admins can revoke)
