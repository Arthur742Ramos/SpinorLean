# Human audit summary

- Document: 02-references-urls round-001 adversarial report
- Current state: OPEN
- Did the bots find blockers? yes. The adversarial reviewer rejected a blanket "no blockers" conclusion until URL classifications are explicit in the v2 round.
- Did the bots find other valid feedback? yes. ACM/AMS 403 responses are access limitations, not broken-citation proof.
- What changed because of this? none; report only.
- What remains unresolved? Per-URL table with status, evidence path, and clean/limited classification.
- Can this category/global review close now? no, because row-level evidence must be surfaced.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C02-ADV-001 | blocker | The GPT "no blockers" conclusion is unsupported without a per-URL classification table in the v2 report/reconciliation. | GPT report vs evidence files | Add table before closure. | Evidence exists but must be exposed. |
| C02-ADV-002 | valid-feedback | ACM and AMS 403 responses must be `limited`, not treated as broken links or clean passes. | HTTP header evidence | Preserve limited classification. | Header files show DOI redirects followed by HTTP 403. |

## Pair-conclusion audit

Every relied URL needs evidence: supported. ACM limited evidence: supported. "No blockers" at row-level: unsupported until reconciliation table is present.

## Stop-condition opinion

DO_NOT_CLOSE_YET.
