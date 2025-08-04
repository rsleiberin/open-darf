<<<<<<< HEAD
<<<<<<< HEAD
#!/bin/bash
set -euo pipefail

echo "🧹 Scanning and removing .Zone.Identifier files from docs/..."

count=0

while IFS= read -r file; do
  if [[ -f "$file" ]]; then
    rm -f "$file"
    echo "🗑️ Removed: $file"
    ((count++))
  fi
done < <(find docs/ -type f -name "*.Zone.Identifier")

if [[ $count -eq 0 ]]; then
  echo "✅ No .Zone.Identifier files found."
else
  echo "✅ Deleted $count .Zone.Identifier file(s)."
fi

tree docs/
||||||| 290d2f7
=======
<<<<<<< HEAD
#!/bin/bash
set -euo pipefail

echo "🧹 Scanning and removing .Zone.Identifier files from docs/..."

count=0
while IFS= read -r file; do
  if [[ -f "$file" ]]; then
    rm -f "$file"
    echo "🗑️ Removed: $file"
    ((count++))
  fi
done < <(find docs/ -type f -name "*.Zone.Identifier")

if [[ $count -eq 0 ]]; then
  echo "✅ No .Zone.Identifier files found."
else
  echo "✅ Deleted $count .Zone.Identifier file(s)."
fi

echo
tree docs/
||||||| 290d2f7
=======
#!/bin/bash
set -euo pipefail

echo "🧹 Scanning and removing .Zone.Identifier files from docs/..."

count=0

while IFS= read -r file; do
  if [[ -f "$file" ]]; then
    rm -f "$file"
    echo "🗑️ Removed: $file"
    ((count++))
  fi
done < <(find docs/ -type f -name "*.Zone.Identifier")

if [[ $count -eq 0 ]]; then
  echo "✅ No .Zone.Identifier files found."
else
  echo "✅ Deleted $count .Zone.Identifier file(s)."
fi

tree docs/
>>>>>>> origin/fix/safety-hook
>>>>>>> merge/all-branches
||||||| 361c749
=======
#!/bin/bash
set -euo pipefail

echo "🧹 Scanning and removing .Zone.Identifier files from docs/..."

count=0
while IFS= read -r file; do
  if [[ -f "$file" ]]; then
    rm -f "$file"
    echo "🗑️ Removed: $file"
    ((count++))
  fi
done < <(find docs/ -type f -name "*.Zone.Identifier")

if [[ $count -eq 0 ]]; then
  echo "✅ No .Zone.Identifier files found."
else
  echo "✅ Deleted $count .Zone.Identifier file(s)."
fi

echo
tree docs/
>>>>>>> origin/main
