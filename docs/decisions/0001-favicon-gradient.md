# ADR 0001 — Favicon SVG gradients

**Status**: accepted – 2024-06-XX  
Browsers do not render gradients inside favicon SVGs; fall back to flat-colour PNG/ICO.

**Decision**  
Use `public/favicons/favicon-32x32.png` as the primary favicon; keep beard-logo SVG for inline HTML only.

**Consequences**  
• Consistent branding across browsers  
• Slightly larger asset size (PNG)  
