# Fail-Open Guard Receipt

- {'APP_ENV': 'production', 'ENGINE_FAIL_OPEN': '1', 'effective_enabled': False, 'reason': 'fail_closed_prod_default'}
- {'APP_ENV': 'production', 'ENGINE_FAIL_OPEN': '0', 'effective_enabled': False, 'reason': 'fail_closed_prod_default'}
- {'APP_ENV': 'dev', 'ENGINE_FAIL_OPEN': '1', 'effective_enabled': True, 'reason': 'dev_override_enabled'}
- {'APP_ENV': 'dev', 'ENGINE_FAIL_OPEN': '0', 'effective_enabled': False, 'reason': 'dev_default_disabled'}
