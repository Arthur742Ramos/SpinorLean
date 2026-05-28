# Human audit summary

- Document: 02-references-urls round-001 Opus report
- Current state: OPEN
- Did the bots find blockers? yes. Opus treated inaccessible final publisher pages and missing current-hash URL-row visibility as blockers.
- Did the bots find other valid feedback? yes. Existing evidence files include row-level URL status data that should be surfaced in reconciliation.
- What changed because of this? none; report only.
- What remains unresolved? Explicit per-URL clean/limited classifications in v2 status.
- Can this category/global review close now? no, because Opus requires current-hash URL evidence to be visible in the v2 round.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C02-OPUS-001 | blocker | `MathlibCommunity2020` DOI reaches an ACM publisher page that returns HTTP 403 after redirect. | `paper/refs.bib`; HTTP evidence | Mark as limited evidence or fetch via an authorized alternative. | Header file records `302,403`. |
| C02-OPUS-002 | blocker | GitHub repository citations need explicit current-hash evidence paths. | `LeanGA`, `Mathlib` bibliography entries | Surface existing header captures in reconciliation. | Header files record HTTP 200 for both repositories. |
| C02-OPUS-003 | optional | Lounesto edition details could be expanded, but the current source is a classical background citation. | `paper/refs.bib` | No required manuscript change. | DOI and metadata evidence exist. |

## Stop-condition opinion

DO_NOT_CLOSE_UNTIL_URL_ROWS_ARE_EXPLICIT.
