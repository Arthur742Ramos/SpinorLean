# Human audit summary

- Document: 02-references-urls status
- Current state: OPEN
- Did the bots find blockers? yes. Round 001 found that URL evidence must stay row-level and that ACM/AMS publisher landings are access-limited.
- Did the bots find other valid feedback? yes. DOI and repository URL evidence exists, and most checked URLs resolve to HTTP 200 after redirects.
- What changed because of this? Round 001 reports and reconciliation now surface per-URL clean/limited classifications.
- What remains unresolved? Limited ACM/AMS publisher responses need alternate access evidence or human disposition before category closure.
- Can this category/global review close now? no, because URL access limitations remain active under the fail-closed v2 rules.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C02-001 | blocker | Current bibliography URLs had not been v2-reviewed. | `paper/refs.bib` | Round 001 reports were produced and reconciled. | GPT, Opus, and adversarial reports exist for category 02. |
| C02-002 | blocker | ACM and AMS DOI landings returned limited publisher responses. | URL evidence headers | Remains active pending alternate access evidence or human disposition. | Reconciliation 001 records `302->403` for `Baez2002` and `MathlibCommunity2020`. |
| C02-003 | valid-feedback | Per-URL classifications must be visible, not hidden behind prose. | Opus/adversarial reports | Fixed in reconciliation 001. | The reconciliation includes a row-level URL table with evidence paths. |

category state: OPEN
latest round number: 1
active blockers: ACM/AMS limited publisher landings require alternate evidence or human disposition
fixed blockers: round-001 reports produced; per-URL table surfaced in reconciliation
rejected findings relevant to the category: none
optional preferences: none
latest GPT status: `review-01/02-references-urls/round-001-gpt.md` OPEN
latest Opus status: `review-01/02-references-urls/round-001-opus.md` OPEN
latest adversarial status: `review-01/02-references-urls/round-001-adversarial.md` OPEN
next required action: obtain alternate publisher/full-page evidence or explicit human disposition for limited ACM/AMS URL rows
stop-condition checklist: latest GPT no blockers: partial; latest Opus no blockers: no; adversarial objections resolved: no; prior blockers fixed/rejected: no; headline ledger current: not directly touched
