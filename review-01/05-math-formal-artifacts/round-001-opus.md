# Human audit summary

- Document: 05-math-formal-artifacts round-001 Opus report
- Current state: OPEN
- Did the bots find blockers? yes. Opus found build evidence missing and several formal-artifact exposition gaps.
- Did the bots find other valid feedback? yes. The polar-form convention is understandable but could be clarified for readers using the half-polarization convention.
- What changed because of this? none; report only.
- What remains unresolved? Lean build evidence and reader-facing links between prose conventions and Mathlib declarations.
- Can this category/global review close now? no, because formal-artifact claims remain build-blocked.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C05-OPUS-001 | blocker | Exact theorem claims need Lean checking for both directions. | Results theorems and theorem index | Run and archive `lake build`. | Static name checks are not build evidence. |
| C05-OPUS-002 | blocker | The manuscript's `\Spin(V,Q)` convention should be tied explicitly to Mathlib's `spinGroup Q`. | Standing conventions | Consider a manuscript clarification in a later paper-fix commit. | Direct source read. |
| C05-OPUS-003 | blocker | Low-rank versus `two_lt_card` formal declarations need clearer paper-facing anchoring. | Square-determinant Levi proof and theorem index | Keep open until clarified or rejected with evidence. | Direct source/theorem-index comparison. |
| C05-OPUS-004 | optional | Polar-form convention could mention the twice-polarization relation. | Standing conventions | No required change in this report. | Current convention is explicit. |

## Stop-condition opinion

DO_NOT_CLOSE.
