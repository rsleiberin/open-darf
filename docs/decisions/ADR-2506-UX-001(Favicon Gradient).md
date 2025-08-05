---
id: ADR-2506-UX-001
legacy_id: 01-favicon-gradient
type: UX
status: accepted
date: 2024-06-15
title: "Favicon SVG gradient fallback to PNG"

decision_confidence: 9
time_investment: "1_hour"
main_tradeoff: "visual_consistency vs file_size"
alternatives_rejected: ["svg_with_fallback_detection", "ico_format_only"]
reevaluate_when: "browser_svg_gradient_support_improves"

supersedes: null
superseded_by: null
linked_evidence:
  - "browser_compatibility_testing_results"

tags: ["frontend", "ui", "branding", "browser_compatibility"]
---

## Decision

Use `public/favicons/favicon-32x32.png` as the primary favicon; keep beard-logo SVG for inline HTML only.

## Context

Browsers do not consistently render gradients inside favicon SVGs. This creates an inconsistent brand experience where some users see the intended gradient design while others see a broken or simplified version.

Testing revealed that gradient SVG favicons fail to render properly in:
- Safari (all versions)
- Chrome (inconsistent behavior)
- Firefox (partial support)

## Rationale

**Visual Consistency Priority**: Brand consistency across all browsers is more important than the theoretical benefits of vector graphics for favicons.

**Technical Reality**: While SVG favicons are technically superior (scalable, smaller file size), real-world browser support for advanced SVG features in favicon context remains poor.

**Pragmatic Approach**: Using PNG for favicons while maintaining SVG for inline use gives us the best of both worlds.

## Consequences

### Positive
- Consistent branding across all browsers and platforms
- Reliable favicon display regardless of user's browser choice
- Simplified deployment (no browser detection required)

### Negative  
- Slightly larger asset size (PNG vs SVG)
- Need to maintain multiple favicon formats
- Loss of scalability benefits for high-DPI displays

### Neutral
- Standard practice adopted by most major websites
- SVG still available for inline branding elements

## Implementation Notes

- Primary favicon: `public/favicons/favicon-32x32.png`
- Backup format: `public/favicons/favicon.ico` for legacy browsers
- SVG logo retained for: headers, loading screens, inline branding
- Test across major browsers before deployment

## Success Criteria

- [ ] Favicon displays consistently across Chrome, Firefox, Safari, Edge
- [ ] No broken/blank favicon reports from users
- [ ] SVG logo continues to work for inline elements
- [ ] Asset loading performance remains acceptable

## Relationships

- **ENABLES**: Consistent branding strategy
