#!/usr/bin/env bash
# Checks that every keyword in lexer.rs appears in krypton.tmLanguage.json.
# Run from repo root: bash vscode-grammar/check_grammar_sync.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

LEXER="$REPO_ROOT/crates/parser/src/lexer.rs"
GRAMMAR="$SCRIPT_DIR/krypton.tmLanguage.json"

if [[ ! -f "$LEXER" ]]; then
  echo "ERROR: lexer not found at $LEXER" >&2
  exit 1
fi

if [[ ! -f "$GRAMMAR" ]]; then
  echo "ERROR: grammar not found at $GRAMMAR" >&2
  exit 1
fi

# Extract keywords from the keyword match block in lexer.rs.
# These are lines like:  "fun" => Token::Fun,
keywords=$(grep '"[a-z_]*" => Token::' "$LEXER" | sed 's/.*"\([a-z_]*\)".*/\1/' | grep -v '^_$' | sort -u)

missing=0
for kw in $keywords; do
  if ! grep -q "\\b${kw}\\b" "$GRAMMAR"; then
    echo "MISSING: keyword '$kw' from lexer.rs not found in grammar" >&2
    missing=$((missing + 1))
  fi
done

if [[ $missing -gt 0 ]]; then
  echo "FAIL: $missing keyword(s) missing from grammar" >&2
  exit 1
fi

echo "OK: all $(echo "$keywords" | wc -w | tr -d ' ') keywords present in grammar"
