# Human audit summary

- Document: 07-language-definitions-grammar round-001 Opus report
- Current state: OPEN
- Did the bots find blockers? yes. Opus found unresolved terminology and source-style issues beyond the later public-surface `iff` cleanup.
- Did the bots find other valid feedback? yes. The Lean-name prose is consistent with the theorem index.
- What changed because of this? none; report only.
- What remains unresolved? Weight-2/vacuum-line definition support, exact/precise wording, and `~{}` source ties.
- Can this category/global review close now? no, because Opus language blockers remain active.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C07-OPUS-001 | blocker | "weight-2" appears before a clear reader-facing definition. | `paper/main.tex` result-boundary and torus passages | Add a parenthetical definition or keep open. | Direct source scan. |
| C07-OPUS-002 | blocker | "Vacuum line" is defined in conventions but used in ways that need a clearer cross-reference. | Standing conventions and later architecture prose | Add a cross-reference or keep open. | Direct source read. |
| C07-OPUS-003 | blocker | "Exact" is used for both set equality and precise criteria, creating possible ambiguity. | Abstract, results, conclusion | Consider reserving "exact" more narrowly. | Direct source read. |
| C07-OPUS-004 | blocker | Source contains unusual `~{}` citation/reference ties. | Multiple `paper/main.tex` citations/refs | Replace with standard `~` in a later paper-fix commit if accepted. | Current scan finds many `~{}` instances. |
| C07-OPUS-005 | optional | Lean names in prose match theorem-index conventions. | Lean-name prose | No action needed. | Direct source read. |

## Stop-condition opinion

DO_NOT_CLOSE.
