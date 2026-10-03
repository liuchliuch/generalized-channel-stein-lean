#!/usr/bin/env bash
# Compare the reviewed statements with the implementations.
set -euo pipefail
cd "$(dirname "$0")/.."
project_dir="$PWD"
mode="${1:-}"
if [[ "$mode" != "" && "$mode" != "--local" ]]; then
  echo "Usage: bash scripts/check_comparator.sh [--local]" >&2
  exit 2
fi
python3 scripts/check_sources.py
if [[ "$mode" == "" ]] && ! command -v landrun >/dev/null 2>&1; then
  echo "Install Landrun on Linux, or use --local for trusted local sources without sandboxing." >&2
  exit 1
fi
# Keep tool builds out of the vendored source and the published file tree.
tool_dir="$project_dir/.lake/comparator"
mkdir -p "$tool_dir"
cp comparator/lakefile.toml comparator/lake-manifest.json lean-toolchain "$tool_dir/"
(cd "$tool_dir" && lake build comparator lean4export)
comparator_bin="$tool_dir/.lake/packages/Comparator/.lake/build/bin/comparator"
exporter_bin="$tool_dir/.lake/packages/lean4export/.lake/build/bin"
export PATH="$exporter_bin:$PATH"
if [[ "$mode" == "--local" ]]; then
  echo "Local Comparator mode: statement comparison, axiom audit, and kernel replay; no OS sandbox."
  runner_dir="$(mktemp -d)"
  trap 'rm -rf "$runner_dir"' EXIT
  # The pinned Comparator invokes Landrun by name. This explicitly selected
  # development runner strips its options and executes trusted local inputs.
  cat > "$runner_dir/landrun" <<'RUNNER'
#!/usr/bin/env bash
set -euo pipefail
while [[ $# -gt 0 ]]; do
  case "$1" in
    --best-effort|-ldd|-add-exec) shift ;;
    --ro|--rw|--rwx|--rox|--env) shift 2 ;;
    *) exec "$@" ;;
  esac
done
exit 2
RUNNER
  chmod +x "$runner_dir/landrun"
  export PATH="$runner_dir:$PATH"
fi
lake env "$comparator_bin" comparator/config.json
