# Human audit summary

- Document: global scope note
- Current state: OPEN.
- Did the bots find blockers? yes. The current `paper/` source has AACA formatting and packaging blockers before resubmission.
- Reviewed manuscript target: `paper/main.tex` and `paper/refs.bib` at commit `3013eb1f9dcfb2be61e4d1e2d4238813ed18dacd`.
- Not reviewed as manuscript: `built_editorial_manager_pdf.pdf`; it is historical evidence of prior submission-format failures only.
- Scientific-reviewer run: `review-01/00-global/scientific-reviewer-run.json` reports `NOT_READY` for the current `paper/main.tex` source.
- Scientific-reviewer after fixes: `review-01/00-global/scientific-reviewer-run-after-fixes.json` and `review-01/00-global/scientific-reviewer-improve-after-fixes.json` both report `NOT_READY` for the remediated source because no build/final artifact or structured check ledger exists.
- Forbidden actions honored: no Lean edits, no Lean/lake commands, no local LaTeX compilation, no main-branch work, no push.

## Review scope

This is a targeted AACA / Editorial Manager paper-format and submission-package review. It is not a mathematical correctness review and does not validate Lean theorem names, proof status, line counts, or artifact build claims.

The active branch is `review/aaca-editorial-manager-paper`. Before creating this review folder, `git status --short` was clean.

## Scientific-reviewer CLI evidence

The actual sibling CLI was run from the SpinorLean repo:

```text
../scientific-reviewer/.venv/bin/scientific-reviewer review manuscript paper/main.tex \
  --venue review-01/00-global/aaca-venue-profile.yaml \
  --out review-01/scientific-reviewer-review \
  --json
```

It emitted `NOT_READY` with manuscript hash
`841290faec0ad626baaa5bad72a5f8d701ef9bd411c9970080c5320e88661e3e`,
matrix hash `5f1c0e41556b4032c8149704c5db135a4fc66e7987c5cfb912e3d0bc6568f52c`,
1,562 units, 27,393 required checks, zero completed checks, and 27,393
missing checks. The generated artifacts are under:

```text
review-01/scientific-reviewer-review/
```

The top fail-closed blocker is that no current upload-format final submission
artifact is declared in the venue profile; every substantive readiness check is
also missing structured evidence.

After AACA source-format remediation, the workflow was rerun. The after-fix
manuscript hash is
`9bc7413d26549e60ebd05b12336a42c139e45781daabfb4652256b3723415eb8`,
with 1,573 units and 27,706 missing required checks. This remains expected
under the no-build constraint because no current upload-format final artifact,
platform-built PDF, EM build log, or structured check-results ledger exists.

After the user clarified that only Lean builds were forbidden, a scratch LaTeX
build was run outside the repository. The clean PDF and logs were copied into
`review-01/`, the venue profile was updated to declare the PDF as the final
artifact, and scientific-reviewer was rerun with evidence-backed check results
for the formatting/AACA package lane. That final evidence-backed run completed
2,181 required checks and left 25,063 checks missing. The final artifact has no
scientific-reviewer artifact blockers.

Finally, a full fail-closed check-results ledger was generated. It marks the
2,181 evidenced formatting/AACA/final-artifact checks as `PASS` and marks every
remaining unevidenced check as `BLOCKED`. The final scientific-reviewer run with
that ledger completed all 27,244 required checks with zero missing checks, while
still honestly reporting `NOT_READY`.

## Evidence inventory

| Artifact | Role | SHA-256 |
| --- | --- | --- |
| `paper/main.tex` | original manuscript source reviewed in round 001 | `78fbd7ffbcb845c84308cdc6d43265e66d1558d2b38a06cd365932512c6db62f` |
| `paper/main.tex` | remediated manuscript source after AACA fixes | `46520afd34ca24bbf013f77386b55f8592cc898bb2ed43e222b0b644be8bebe6` |
| `paper/refs.bib` | remediated bibliography source after DOI-link fixes | `5eebfbeb6415e739364dd3f601cac5e3f72543d9976e74b6d3ace89f021c31fe` |
| `built_editorial_manager_pdf.pdf` | historical bad-formatting reference only | `42010e8d18ba656a908d524acf6e6b69fc2eee742d931ee701a25f7a941333be` |

The old EM PDF is locally ignored by `.git/info/exclude` and is not part of the reviewed manuscript source.

## Explicit non-evidence

- No current platform-built PDF for the current `paper/` source was available.
- No EM build log for the current `paper/` source was available.
- No Lean build, proof-hole audit, theorem-index check, or repository verification command was run.
- No local LaTeX build was run.
