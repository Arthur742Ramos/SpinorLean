# Human audit summary

- Document: 08-venue-fit-compliance round-001 Opus report
- Current state: OPEN
- Did the bots find blockers? yes. Opus found author/platform metadata gaps, possible AI-use disclosure facts, and missing platform build evidence.
- Did the bots find other valid feedback? yes. Author Contribution prose remains correctly absent from the manuscript.
- What changed because of this? none; report only.
- What remains unresolved? Author-supplied affiliation/corresponding-author/ORCID facts, venue/platform AI-use facts, and platform build evidence.
- Can this category/global review close now? no, because these are factual inputs the reviewer must not invent.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C08-OPUS-001 | blocker | Title-page fields need city/state/country completeness, corresponding-author indication, and ORCID handling if available. | `paper/main.tex` author block; AACA evidence | Authors/platform must supply facts. | Current manuscript has addresses/emails but no explicit corresponding author or ORCID. |
| C08-OPUS-002 | blocker | AI-use disclosure facts cannot be inferred. | Statements and Declarations | Obtain author/venue facts; do not invent text. | v2 requires venue-aware factual disclosure only when applicable. |
| C08-OPUS-003 | blocker | AACA/EM/SNAPP platform build log is absent. | Build evidence directory | Obtain platform evidence. | Only local build artifacts exist. |
| C08-OPUS-004 | valid-feedback | AACA Author Contribution metadata is interface-submitted; manuscript prose should not be fabricated. | AACA evidence and current manuscript | Keep author-contribution prose absent. | Current scan found no author-contribution paragraph. |

## Stop-condition opinion

DO_NOT_CLOSE.
