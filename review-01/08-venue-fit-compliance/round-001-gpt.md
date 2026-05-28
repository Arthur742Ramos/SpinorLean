# Human audit summary

- Document: 08-venue-fit-compliance round-001 GPT report
- Current state: OPEN
- Did the bots find blockers? yes. Author/platform factual metadata remains unresolved.
- Did the bots find other valid feedback? yes. The manuscript satisfies many AACA format basics and correctly avoids fabricated Author Contribution prose.
- What changed because of this? none; report only.
- What remains unresolved? Affiliation/corresponding-author/ORCID/platform facts and any author-supplied AI-use facts.
- Can this category/global review close now? no, because reviewer must not invent author/platform facts.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C08-GPT-001 | blocker | Title-page/platform metadata needs author/platform facts. | `paper/main.tex` author block | Authors must provide the facts; do not invent them. | Current manuscript lists addresses/emails but no explicit corresponding author or ORCID metadata. |
| C08-GPT-002 | valid-feedback | AACA basics are aligned: `birkjour`, abstract length, keywords, MSC, numbered references, declarations, and code/data availability. | `paper/main.tex`; AACA evidence file | Keep as venue-compliance support. | Local AACA evidence is HTTP 200 and records the relevant venue guidance. |
| C08-GPT-003 | valid-feedback | Author Contribution prose should not be reintroduced. | AACA evidence and manuscript declarations | Keep interface-submitted author contribution metadata out of the paper unless authors/venue require otherwise. | Current public-surface scan found no author-contribution prose. |

## Stop-condition opinion

DO_NOT_CLOSE.
