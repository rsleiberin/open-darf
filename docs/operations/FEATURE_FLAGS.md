# Feature Flags — Service-Free Discipline

Flags default OFF for CI and general test runs:
- EXTRACTOR_SCI
- EXTRACTOR_BIO
- EXTRACTOR_TEXT2NKG
- TEMPORAL_GRAPH_MODEL
- RUN_PERF

Local development:
1) Edit var/local/testing.env to set developer defaults.
2) Export env vars in your shell to temporarily override:
   export EXTRACTOR_TEXT2NKG=1

Quick status:
- tools/flags/describe_flags.sh

CI hard guard:
- tools/ci/verify_service_free.sh
  Must report all flags as 0 in CI.

Toggling (existing script):
- tools/rollback/feature_toggle.sh var/local/testing.env status|enable|disable [FLAG|all]
