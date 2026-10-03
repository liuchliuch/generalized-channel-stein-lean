#!/usr/bin/env bash
# Build the proof library, validate sources, and audit transitive axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
mode="${1:-}"
if [[ "$mode" != "" && "$mode" != "--serial" ]]; then
  echo "Usage: bash scripts/check.sh [--serial]" >&2
  exit 2
fi
python3 scripts/check_sources.py
if [[ "$mode" == "--serial" ]]; then
  # Build dependency modules in order for machines with limited memory.
  module_list="$(mktemp)"
  trap 'rm -f "$module_list"' EXIT
  python3 scripts/check_sources.py --module-order > "$module_list"
  while IFS= read -r module_name; do
    lake build "$module_name"
  done < "$module_list"
else
  lake build
fi
lake env lean scripts/audit_axioms.lean
lake env lean scripts/audit_appendix.lean
