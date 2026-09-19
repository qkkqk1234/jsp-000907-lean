# Pre-submission audit evidence

This directory holds the pre-submission self-check required by the awards
repository, run with the bundled `lean-verify` skill's own script
(`skills/lean-verify/scripts/audit.py`, awards commit `54a55f60`).

| File | What it is |
| --- | --- |
| `targets.json` | The target manifest fed to `audit.py`. `project.root` is a placeholder; set it to an absolute path to a clean checkout before rerunning. |
| `result.json` | The script's own output for this commit, with local absolute paths replaced by `<project>` and `<audit-out>`. Nothing else was edited. |

## Reproducing it

```bash
git clone <this repository> && cd <repo> && git checkout <the commit under review>
lake exe cache get && lake build
# edit targets.json: project.root -> the absolute path of this checkout
python3 audit.py preflight audit/targets.json --out /tmp/pre
python3 audit.py run       audit/targets.json --out /tmp/run --lake "$(command -v lake)"
```

`audit.py` is not vendored here; take it from the awards repository at the
commit recorded above.

## What the result does and does not say

`exit_code: 0` means only that the listed targets passed that level of
mechanical checking and that no axioms beyond `propext`, `Classical.choice` and
`Quot.sound` were observed. The script itself records `semantic_verdict:
not_determined`: whether the formal statement really expresses the original
problem is a human judgement, argued in `STATEMENT.md` in the repository root
rather than established by this script.

The run was performed on the submitter's own machine with the pinned toolchain
and dependency manifest. It was **not** run inside an isolated container, and no
kernel replay with an external checker was performed. Maintainers' independent
verification should not be treated as a repeat of something stronger than what
is recorded here.

A line-ending note for anyone rerunning this on Windows: `audit.py` compares the
working-tree file hashes against the blobs at the commit, so a checkout made
with `core.autocrlf=true` reports `source_differs_from_commit`. Set
`core.autocrlf=false` and `core.eol=lf` before the checkout.
