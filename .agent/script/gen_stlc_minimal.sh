#!/usr/bin/env sh
# Regenerate Lp2lc/Active/STLC_minimal from the current STLC sources.

set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

src=Lp2lc/Active/STLC
dst=Lp2lc/Active/STLC_minimal
mkdir -p "$dst/Serial"

for file in STLCDef.lean Serial/Def.lean Serial/Infra.lean Serial/Infer.lean Serial/__Eval_certifiedByInfer.lean; do
  sed \
    -e 's/«Lp2lc»\.Active\.STLC\./«Lp2lc».Active.STLC_minimal./g' \
    -e 's/Lp2lc\.Active\.STLC\./Lp2lc.Active.STLC_minimal./g' \
    -e 's/^namespace Lp2lc\.Active\.STLC$/namespace Lp2lc.Active.STLC_minimal/' \
    -e 's/^end Lp2lc\.Active\.STLC$/end Lp2lc.Active.STLC_minimal/' \
    -e 's/^end STLC$/end STLC_minimal/' \
    "$src/$file" > "$dst/$file"
done

cat > "$dst/mod.lean" <<'EOF'
import «Lp2lc».Active.STLC_minimal.STLCDef
import «Lp2lc».Active.STLC_minimal.Serial.Def
import «Lp2lc».Active.STLC_minimal.Serial.Infra
import «Lp2lc».Active.STLC_minimal.Serial.Infer
import «Lp2lc».Active.STLC_minimal.Serial.__Eval_certifiedByInfer
EOF
