#!/usr/bin/env bash
# Reproduce the verification of JSP-000907 from a clean checkout.
set -euo pipefail

echo "== toolchain =="
lean --version
lake --version

echo "== fetching pinned dependencies (revisions come from lake-manifest.json) =="
lake exe cache get

echo "== clean build =="
rm -rf .lake/build   # mathlib artifacts live under .lake/packages and are untouched
lake build JSP907

echo "== source hygiene: no sorry / native_decide / custom axioms =="
if grep -rnE '\b(sorry|admit|native_decide|ofReduceBool|unsafe|implemented_by)\b|decide \+native|^axiom ' JSP907.lean JSP907/; then
  echo "FAIL: forbidden construct found"; exit 1
fi
echo "OK: source is clean"

echo "== axiom audit =="
lake env lean JSP907/Audit.lean 2>&1 | tee axioms.txt
if grep -E 'depends on axioms' axioms.txt | grep -vE '\[propext, Classical\.choice, Quot\.sound\]|\[propext, Quot\.sound\]'; then
  echo "FAIL: an audited declaration depends on an unexpected axiom"; rm -f axioms.txt; exit 1
fi
rm -f axioms.txt
echo "OK: every audited declaration uses at most [propext, Classical.choice, Quot.sound]"
