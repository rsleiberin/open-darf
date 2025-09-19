# Open-DARF Documentation Fence Policy

**Rule:** Do not use triple backticks inside any command heredoc.  
Use tildes for code fences instead.

## Allowed fences
~~~bash
echo "code blocks in docs use tildes"
~~~

## Disallowed
Any line starting with three backticks will be auto-converted to tildes by the sanitizer.

## Rationale
- The OpenAI UI wraps command blocks with backticks; nesting them causes rendering bugs.
- Tilde fences render fine on GitHub.

## Tooling
- `scripts/sanitize_markdown_fences.sh` converts ``` → ~~~ in *.md/*.mdx
- `scripts/lint_no_triple_backticks.sh` fails if any remaining backticks exist in docs or scripts.
