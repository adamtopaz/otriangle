#!/usr/bin/env bash

set -euo pipefail

# Build the mathematical declarations and all chapters imported by the
# top-level Blueprint through Lake's dependency tracker.
lake build Otriangle.OTriangle Otriangle.Chapters.Paper Otriangle.Chapters.MonoAnabelian

# The top-level document imports both Verso and the local-field development.
# Invoke Lean directly in the Lake environment so that its large environment
# is not retained alongside Lake's build scheduler during code generation.
mkdir -p .lake/build/lib/lean/Otriangle
lake env lean Otriangle/Blueprint.lean \
  -o .lake/build/lib/lean/Otriangle/Blueprint.olean \
  -i .lake/build/lib/lean/Otriangle/Blueprint.ilean
lake env lean --run OtriangleMain.lean --output _out/site

lake exe vbp check

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
test -f _out/site/html-multi/-verso-data/blueprint-html-cache.json
