#!/usr/bin/env bash

set -euo pipefail

# Judge Otriangle/Comparator/Solution.lean against Otriangle/Comparator/Challenge.lean using
# https://github.com/leanprover/comparator.
#
# Requires `landrun` and `lean4export` in PATH (or COMPARATOR_LANDRUN / COMPARATOR_LEAN4EXPORT),
# and the comparator binary itself, located via COMPARATOR_BIN or PATH.

cd "$(dirname "${BASH_SOURCE[0]}")/.."

CONFIG="${1:-comparator.json}"
COMPARATOR_BIN="${COMPARATOR_BIN:-$(command -v comparator || true)}"

if [[ -z "${COMPARATOR_BIN}" ]]; then
  echo "error: comparator binary not found; set COMPARATOR_BIN or put it in PATH" >&2
  exit 1
fi

for tool in landrun lean4export; do
  var="COMPARATOR_$(echo "${tool}" | tr '[:lower:]' '[:upper:]')"
  if [[ -z "${!var:-}" ]] && ! command -v "${tool}" >/dev/null; then
    echo "error: ${tool} not found in PATH; set ${var} or install it" >&2
    exit 1
  fi
done

# Build the challenge and its dependencies ahead of time. The solution is deliberately left for
# comparator to build inside the sandbox.
lake build Otriangle.Comparator.Challenge

# The systemd-run wrapper guards against a landrun sandbox escape; see comparator's README.
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c "lake env '${COMPARATOR_BIN}' '${CONFIG}'"
