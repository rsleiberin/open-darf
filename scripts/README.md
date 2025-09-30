# Open-DARF Scripts

This directory contains automation scripts for the Open-DARF validation infrastructure.

## Usage

From repository root:

- ./install   # Deploy infrastructure
- ./validate  # Run verification
- ./cleanup   # Remove infrastructure

Root scripts automatically delegate to appropriate implementations.

## Development

When adding new scripts:

1. Place user-facing scripts in scripts/core/
2. Place internal utilities in scripts/internal/
3. Make executable: chmod +x script_name.sh
4. Use set -euo pipefail for safety
5. Include clear error messages

## Script Conventions

- Use consistent error handling
- Provide clear status messages
- Exit with appropriate codes (0=success, 1=error)
- Include usage documentation in comments
- Follow shellcheck recommendations
