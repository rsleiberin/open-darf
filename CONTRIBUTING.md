# Contributing to Open-DARF

Thank you for your interest in contributing to Open-DARF! This project demonstrates constitutional AI through mathematical verification, and community validation is essential to its success.

## Ways to Contribute

### 1. Validation and Evidence

Run the validation suite and contribute evidence:

- ./install   # Deploy infrastructure
- ./validate  # Run TLA+ verification

Submit your results including:
- Complete evidence files (logs, receipts, status)
- System configuration details
- SHA-256 receipt verification

### 2. Documentation Improvements

Help make documentation clearer:
- Fix typos and unclear explanations
- Add examples and use cases
- Improve installation instructions
- Translate documentation

### 3. Bug Reports

Submit detailed bug reports including:
- Description of the issue
- Steps to reproduce
- Expected vs actual behavior
- System environment details
- Relevant logs

### 4. Feature Requests

Propose enhancements with:
- Clear use case description
- Expected behavior
- Potential implementation approach
- Impact on existing functionality

## Development Workflow

### Getting Started

1. Fork the repository
2. Clone your fork
3. Create branch: git checkout -b feature/your-feature-name
4. Install infrastructure: ./install
5. Verify environment: ./validate

### Making Changes

1. Write clear, professional code
2. Follow existing patterns and style
3. Test thoroughly
4. Document new features
5. Update evidence if verification changes

### Submitting Changes

Commit with clear messages following conventional commits:
- feat: New features
- fix: Bug fixes
- docs: Documentation changes
- chore: Maintenance tasks
- test: Test improvements

Push to your fork and create Pull Request with:
- Clear description of changes
- Motivation and context
- Testing performed
- Evidence updates (if applicable)

## Code Style

### Bash Scripts

- shellcheck compliant
- Use set -euo pipefail
- Clear error messages
- Professional comments

### TLA+ Specifications

- Standard PlusCal formatting
- Clear variable names
- Documented invariants
- Comprehensive configs

### Documentation

- Professional academic tone
- Clear explanations without jargon
- Evidence-based claims with links
- Proper markdown formatting

## Testing Requirements

Before submitting:

1. Run ./validate successfully
2. Verify evidence generation
3. Test on clean system if possible
4. Check documentation builds correctly

## Community Standards

- Be respectful and professional
- Focus on technical merit
- Provide constructive feedback
- Follow Code of Conduct
- Help others succeed

## Questions?

Open an issue for questions or discussion. We're here to help!

## License

By contributing, you agree that your contributions will be licensed under the MIT License.
