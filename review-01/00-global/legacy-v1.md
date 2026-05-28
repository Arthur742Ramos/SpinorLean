# Human audit summary

- Document: legacy v1/v1-like artifact index
- Current state: not applicable
- Did the bots find blockers? yes. Historical review artifacts in `review-01/` do not satisfy scientific-reviewer-v2 naming and per-file summary requirements.
- Did the bots find other valid feedback? yes. Some historical artifacts still contain superseded findings, including removed author-contribution text.
- What changed because of this? Indexed legacy artifacts as historical evidence only; they are not v2 category reports or v2 closure evidence.
- What remains unresolved? Current v2 rounds must not rely on legacy closure claims without rechecking the current manuscript hash.
- Can this category/global review close now? not applicable, because this index is not a category report.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| L-001 | blocker | Existing review artifacts predate the v2 workflow and may have stale or superseded statements. | `review-01/scientific-reviewer-*`, old `round-00*-aaca-em*.md`, and v1 global files. | Treat as historical context only. | New v2 files are created with strict v2 names and current-hash status. |
| L-002 | valid-feedback | Unsupported manuscript Author contributions prose was removed earlier and must not be revived by stale artifacts. | Commit `e7c7bf0`, current `paper/main.tex`, current extracted PDF text. | Current manuscript/PDF/README public surfaces omit Author contributions prose. | Current scan found no `Author contributions` / `All authors read and approved` hits on public surfaces. |

## Legacy artifact scope

The following paths existed before this v2 formal report run and are historical evidence, not v2 reports:

- `review-01/scientific-reviewer-review*/`
- `review-01/scientific-reviewer-improve*/`
- `review-01/check-results/`
- `review-01/09-format-build-submission/round-00*-aaca-em*.md`
- `review-01/09-format-build-submission/round-004-full-fail-closed-ledger.md`
- `review-01/02-references-urls/round-001-reference-citation-audit.md`
- `review-01/00-global/final-fail-closed-status.md`
- `review-01/00-global/scope.md`
- `review-01/00-global/policy-refs.md`
- `review-01/00-global/unverified.md`

v2 category reports produced after this index use the required filenames:

- `round-NNN-gpt.md`
- `round-NNN-opus.md`
- `round-NNN-adversarial.md`
- `reconciliation-NNN.md`
- `agree-to-reject-<finding-id>-<model-family>-round-NNN.md`

