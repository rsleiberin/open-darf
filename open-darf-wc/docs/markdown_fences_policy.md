# Open-DARF Documentation Fence Policy

**Rule:** Do not use 3-backtick fences inside any command heredoc.  
Use tildes for code fences instead.

## Allowed fences
~~~bash
echo "code blocks in docs use tildes"
~~~

## Disallowed
Any line starting with a 3-backtick fence will be auto-converted to tildes by the sanitizer.

## Rationale
- The OpenAI UI wraps command blocks with backticks; nesting them causes rendering bugs.
- Tilde fences render fine on GitHub.

## Tooling
- `scripts/sanitize_markdown_fences.sh` converts 3-backtick fences to tildes in *.md/*.mdx
- `scripts/lint_no_triple_backticks.sh` fails if any 3-backtick fences exist in docs or scripts.
