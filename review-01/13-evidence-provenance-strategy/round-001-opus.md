# Human audit summary

- Document: 13-evidence-provenance-strategy round-001 Opus report
- Current state: OPEN
- Did the bots find blockers? yes. Opus found missing Lean build provenance, missing remote commit attestation, limited URL classification needs, and incomplete static PASS ledger rows.
- Did the bots find other valid feedback? yes. Storing URL checks as structured evidence would improve future audits.
- What changed because of this? none; report only.
- What remains unresolved? Build evidence, remote attestation, limited URL records, and static provenance ledger completion.
- Can this category/global review close now? no, because provenance is incomplete.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C13-OPUS-001 | blocker | The Lean proof claim lacks build provenance. | Code availability and artifact paragraph | Run/archive `lake build` and verify script. | Local Lean tools unavailable. |
| C13-OPUS-002 | blocker | The paper-named source revision needs remote attestation in evidence. | Code availability statement | Store `git ls-remote` or equivalent evidence. | Local ancestor check passed, but remote attestation is not yet stored. |
| C13-OPUS-003 | blocker | ACM DOI access limitation must be classified as limited evidence. | Reference evidence | Record in category 02/13. | Header file records `302,403`. |
| C13-OPUS-004 | blocker | Static PASS rows for non-build evidence are incomplete in the headline ledger. | `00-global/headline-claim-provenance-ledger.md` | Add/update static rows later. | Ledger still has older hashes and blocked proof rows. |
| C13-OPUS-005 | optional | A structured URL-status CSV would help. | Evidence directory | Optional evidence ergonomics. | Existing JSON/header files are usable. |

## Stop-condition opinion

DO_NOT_CLOSE.
