#!/usr/bin/env sh
# Regenerate Lp2lc/Active/STLC_minimal from the pinned STLC sources.

set -eu

root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
cd "$root"

rev=226bedc617f1cd77f934dd60c4b6652cd940f4dc
src=Lp2lc/Active/STLC
dst=Lp2lc/Active/STLC_minimal

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
mkdir -p "$tmp/Serial"

git show "$rev:$src/STLCDef.lean" > "$tmp/STLCDef.lean"
git show "$rev:$src/Serial/Def.lean" > "$tmp/Serial/Def.lean"
git show "$rev:$src/Serial/Infra.lean" > "$tmp/Serial/Infra.lean"
git show "$rev:$src/Serial/Infer.lean" > "$tmp/Serial/Infer.lean"
git show "$rev:$src/Serial/__Eval_certifiedByInfer.lean" > "$tmp/Serial/__Eval_certifiedByInfer.lean"

# Rename the module namespace and repair internal imports.
perl -pi -e '
  s/«Lp2lc»\.Active\.STLC\./«Lp2lc».Active.STLC_minimal./g;
  s/Lp2lc\.Active\.STLC\.AST/Lp2lc.Active.STLC_minimal.AST/g;
  s/^namespace Lp2lc\.Active\.STLC$/namespace Lp2lc.Active.STLC_minimal/;
  s/^end Lp2lc\.Active\.STLC$/end Lp2lc.Active.STLC_minimal/;
  s/^end STLC$/end STLC_minimal/;
' "$tmp/STLCDef.lean" "$tmp/Serial/Def.lean" "$tmp/Serial/Infra.lean" "$tmp/Serial/Infer.lean" \
  "$tmp/Serial/__Eval_certifiedByInfer.lean"
perl -pi -e 's/Serial\.__Infer/Serial.Infer/' "$tmp/Serial/__Eval_certifiedByInfer.lean"

# The proof does not cover the `fnPrimitive` syntax, so restore its two missing cases.
python3 - "$tmp/Serial/__Eval_certifiedByInfer.lean" <<'EOF'
import sys

path = sys.argv[1]
text = open(path).read()
edits = [
    (
        """        exact ⟨bodyFuel + 1, by simp only [infer.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
    | ref carrier under =>""",
        """        exact ⟨bodyFuel + 1, by simp only [infer.eq_3, hTarget, Rec.Outcome.map]; rfl⟩
      | fnPrimitive _ _ => exact ⟨fuel + 1, by simpa only [infer.eq_6] using hInfer⟩
    | ref carrier under =>""",
    ),
    (
        """      match fnResult with
      | ⟨.mk _ (.lit _) _, _⟩ => .outOfFuel
      | ⟨.mk context (.fn annotation body) captured, fnSafe⟩ =>""",
        """      match fnResult with
      | ⟨.mk _ (.lit _) _, _⟩ => .outOfFuel
      | ⟨.mk context (.fnPrimitive tOut op) captured, fnSafe⟩ =>
        (evalInternal arg bindings fuel).flatMap (λ argResult =>
          match argResult.val.value with
          | .lit repr =>
            letI : DecidableEq Typ := λ a b => typDecidableLE a b
            match hCheck : infer (.val (op repr)) captured fuel with
            | .yield (some checked) =>
              if hSame : checked = resolveType tOut then
                .yield ⟨.mk context (op repr) captured, by
                  rintro (_ | inferFuel) typ hInfer
                  · cases hInfer
                  · obtain ⟨input, hFn, _⟩ := inferApplySuccess hInfer
                    obtain ⟨fnFuel, hFnValue⟩ := fnSafe hFn
                    cases fnFuel with
                    | zero => cases hFnValue
                    | succ fnFuel =>
                      simp only [Val.asTrm, infer.eq_6] at hFnValue
                      cases hFnValue
                      exact ⟨fuel, by rw [hSame] at hCheck; exact hCheck⟩⟩
              else .outOfFuel
            | _ => .outOfFuel
          | _ => .outOfFuel)
      | ⟨.mk context (.fn annotation body) captured, fnSafe⟩ =>""",
    ),
]
for old, new in edits:
    if text.count(old) != 1:
        raise SystemExit("generator: unexpected source shape")
    text = text.replace(old, new)
open(path, "w").write(text)
EOF

if grep -R 'Lp2lc\.Active\.STLC\.' "$tmp"/*.lean "$tmp"/Serial/*.lean; then
  echo "generator: stale STLC namespace" >&2
  exit 1
fi

mkdir -p "$dst/Serial"
rm -f "$dst/Serial/__Eval_certifiedByInfer.lean"
cp "$tmp/STLCDef.lean" "$dst/STLCDef.lean"
cp "$tmp/Serial/Def.lean" "$dst/Serial/Def.lean"
cp "$tmp/Serial/Infra.lean" "$dst/Serial/Infra.lean"
cp "$tmp/Serial/Infer.lean" "$dst/Serial/Infer.lean"
cp "$tmp/Serial/__Eval_certifiedByInfer.lean" "$dst/Serial/Eval_certifiedByInfer.lean"

cat > "$dst/mod.lean" <<'EOF'
import «Lp2lc».Active.STLC_minimal.STLCDef
import «Lp2lc».Active.STLC_minimal.Serial.Def
import «Lp2lc».Active.STLC_minimal.Serial.Infra
import «Lp2lc».Active.STLC_minimal.Serial.Infer
import «Lp2lc».Active.STLC_minimal.Serial.Eval_certifiedByInfer
EOF
