# Open-DARF Documentation Fence Policy

**Rule:** Do not use triple backticks inside any command heredoc.  
Use tildes for code fences instead.

## Allowed fences

~~~bash
echo "code blocks in docs use tildes"
~~~

## Disallowed (replaced automatically by sanitizer)
(Any line starting with three backticks will be converted to tildes by tools/scripts.)

## Rationale
- The OpenAI UI wraps command blocks with backticks. Nesting backticks inside causes rendering bugs.
- Tilde fences render identically on GitHub.

## Tooling
- `scripts/sanitize_markdown_fences.sh` converts ``` → ~~~ in *.md/*.mdx
- `scripts/lint_no_triple_backticks.sh` fails if any remaining backticks exist in docs or scripts.
