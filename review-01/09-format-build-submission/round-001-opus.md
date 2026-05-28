# Human audit summary

- Document: 09-format-build-submission round-001 Opus report
- Current state: OPEN
- Did the bots find blockers? yes. Opus found missing platform build evidence, author/title-page field gaps, and local-log warning audit requirements.
- Did the bots find other valid feedback? yes. Local build evidence is available and hashable.
- What changed because of this? none; report only.
- What remains unresolved? AACA/EM platform compile, author metadata, and local log warning classification.
- Can this category/global review close now? no, because platform build evidence is absent.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C09-OPUS-001 | blocker | Rendered PDF carries the same incomplete affiliation/corresponding-author metadata as the source. | PDF/source author block | Author/platform facts required. | Source lines show country-level addresses and no explicit corresponding author. |
| C09-OPUS-002 | blocker | No AACA/EM/SNAPP-side compile log exists. | `review-01/09-format-build-submission/build-evidence/` | Capture platform log before close. | Local artifacts are not platform logs. |
| C09-OPUS-003 | blocker | AACA overfull/underfull warning requirement needs current log inspection. | `main.log`; AACA evidence | Inspect/record local warning scan and later platform log. | Local build artifacts are hashed in evidence. |
| C09-OPUS-004 | optional | Archiving log artifacts next to extracted text is useful. | Build evidence directory | Already present for local build. | Files include `latexmk.stdout`, `main.log`, `main.bbl`, `main.blg`, and extracted text. |

## Stop-condition opinion

DO_NOT_CLOSE.
