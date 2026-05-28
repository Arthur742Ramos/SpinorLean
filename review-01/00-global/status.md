# Human audit summary

- Document: scientific-reviewer-v2 global status
- Current state: OPEN
- Did the bots find blockers? yes. Formal v2 category reports have not yet been produced for the current manuscript hash.
- Did the bots find other valid feedback? yes. Legacy v1/v1-like review files remain present and are explicitly indexed as historical, non-v2 artifacts.
- What changed because of this? Created the v2 global dashboard, current artifact inventory, and category queue.
- What remains unresolved? Category rounds 01-14, evidence-based Lean-build blocker scoping, and category-15 prerequisite closure.
- Can this category/global review close now? no, because v2 category reports and reconciliations are not complete.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| G-001 | blocker | v2 formal reports are absent for the current paper hash. | `review-01/` has no v2 `status.md` files before this scaffold. | Opened the v2 workflow and queued categories 01-14. | Current scaffold records every category as open until report rounds run. |
| G-002 | valid-feedback | Historical v1 artifacts could be mistaken for v2 outputs. | Existing `review-01/scientific-reviewer-*` and older category files. | Added `review-01/00-global/legacy-v1.md` index and treat them as historical evidence only. | v2 files use strict `status.md`, `round-NNN-gpt.md`, `round-NNN-opus.md`, `round-NNN-adversarial.md`, and `reconciliation-NNN.md` names. |
| G-003 | blocker | Lean proof/build validation is not current in this v2 round. | Prior evidence says `lake build` did not complete; current static scans are non-build evidence only. | Lean-build-dependent conclusions remain blocked until a current `lake build` or equivalent CI evidence exists. | Static file count and proof-hole token scan are recorded separately from the missing build. |

## Current target

- Repository: `Arthur742Ramos/SpinorLean`
- Branch: `review/aaca-editorial-manager-paper`
- Current commit: `8957b7b8029f86aa52a221dd385e2e3b998f6aab`
- Current manuscript path: `paper/main.tex`
- Current final submission artifact path: `review-01/final-artifacts/spinorlean-aaca.pdf`
- Current manuscript SHA-256: `9b0d789b81e610448a7d2842dd02aa30fd2c60f7f203c6277982a16ad69cd253`
- Current final PDF SHA-256: `ad60d401a20075bf87b23baf3bf7d4b8287883070f51217b1a0df5c643a0634b`
- Current extracted PDF text SHA-256: `7f497afd25fb8543f910eadd22813df663eb21679e2dd7c7ac63ba402a7e2218`
- Headline claim provenance ledger: `review-01/00-global/headline-claim-provenance-ledger.md`
- Headline ledger currentness status: seeded for current hash; proof/build-dependent rows remain blocked until Lean build evidence exists.
- Active category: v2 scaffold and evidence preparation.
- Final status: NOT_ALL_CATEGORIES_CLOSED

## Venue assumption

Target venue is Advances in Applied Clifford Algebras (AACA) via the Springer Nature / Editorial Manager submission route, per user direction and `review-01/00-global/aaca-venue-profile.yaml`; this is a manuscript compliance review, not a venue-selection/ranking run.

The AACA-specific source profile is authoritative for category 08/09 checks: `birkjour.cls`, first line `\documentclass{birkjour}`, LaTeX/AMS-LaTeX source, unmodified class file, 150-250 word abstract, 4-6 keywords, MSC codes, numbered square-bracket citations, DOI links where available, and statements/declarations/data/code availability. The current AACA page fetched at `review-01/00-global/evidence/link.springer.com-journal-6-submission-guidelines.html` returned HTTP 200 on 2026-05-28.

TeX Live 2018 compatibility is recorded only as the conservative lower-bound strategy from prior AACA/Editorial Manager discussion when no current AACA upload/build log is available. It is not recorded here as an AACA-specific compiler fact; an actual current AACA/SNAPP/EM build log supersedes it.

Author-contribution prose is not reintroduced into the manuscript. The AACA page says Author Contribution information and Competing Interest information are provided via the submission interface and only interface-submitted information is used in the final published version; the current paper keeps manuscript declarations to Funding, Competing interests, Data availability, and Code availability.

## Tooling and readability gates

- `/home/david/repos/AGENTS.md`: readable.
- `/home/david/repos/scientific-reviewer/scientific-reviewer-v2/AGENTS.md`: readable.
- `rg`: `/usr/bin/rg`.
- v2 protocol model pair selected in `review-01/00-global/model-selection.md`: GPT-5.5 and Claude Opus 4.7.
- v2 CLI note: `/usr/local/bin/scientific-reviewer` is the older v1 CLI and is not used as v2.

## Public artifact locator inventory

| Locator source | Current locator text | Current manuscript? | Public/release/reproducibility claim remains? | Disposition |
| --- | --- | --- | --- | --- |
| `paper/main.tex` artifact table | `https://github.com/Arthur742Ramos/SpinorLean` plus source revision `e7c7bf09e6c4477124e85a7d4339c0b4a97e52ca` | yes | yes | Paper-facing locator and source revision are present. Public access is not asserted beyond code availability. |
| `paper/main.tex` code availability | `https://github.com/Arthur742Ramos/SpinorLean`; source revision `e7c7bf09e6c4477124e85a7d4339c0b4a97e52ca` | yes | yes | Same locator/revision repeated in declarations. |
| `README.md` and `paper/README.md` | Repository-relative source descriptions; no substitute for the paper-facing locator. | no, README surfaces only | yes, repository is the artifact surface | Acceptable only because the manuscript itself contains the repository URL and source revision. |
| Prior v1 review artifacts | Historical AACA and scientific-reviewer paths under `review-01/`. | no | no submission-facing claim | Indexed as legacy v1/v1-like evidence in `legacy-v1.md`, not v2 closure evidence. |
| Commit `e7c7bf0` | Removed unsupported Author contributions paragraph from manuscript/PDF. | n/a | declarations remain | Not blocker laundering: current AACA evidence supports interface-submitted author-contribution metadata rather than manuscript prose. |
| Commit `8957b7b` | Cleaned public surfaces and added paper-facing SpinorLean source revision. | yes | yes | Current paper has locator plus revision; category 01/13/14 must recheck current hash. |

## Category dashboard

| Category | Did it find blockers or valid feedback yet? | Current disposition | Closed? |
| --- | --- | --- | --- |
| 01 snapshot artifacts | Pending v2 round. | OPEN; must verify manuscript/PDF/source locator/current hash and Lean-build dependency scope. | no |
| 02 references URLs | Pending v2 round. | OPEN; every relied-on URL must be opened or marked as evidence-limited. | no |
| 03 citation support | Pending v2 round. | OPEN; citation-bearing statements must be audited. | no |
| 04 factual independent verification | Pending v2 round. | OPEN; headline claims seeded in ledger but proof/build rows are not closed. | no |
| 05 math formal artifacts | Pending v2 round. | OPEN; static theorem-index/proof-hole evidence exists, full Lean build evidence is missing. | no |
| 06 overlap provenance | Pending v2 round. | OPEN; searched corpus must be explicit. | no |
| 07 language definitions grammar | Pending v2 round. | OPEN; clarity and terminology must be checked on current hash. | no |
| 08 venue fit compliance | Pending v2 round. | OPEN; AACA rules and interface-only author contribution point must be checked. | no |
| 09 format build submission | Pending v2 round. | OPEN; current local PDF build evidence exists, current AACA/EM build log does not. | no |
| 10 edit regression instructions consistency | Pending v2 round. | OPEN; commits `e7c7bf0` and `8957b7b` require current-hash regression review. | no |
| 11 claim density methodology temporal | Pending v2 round. | OPEN; numerical/static claims and Lean-build-dependent claims must be separated. | no |
| 12 contribution prior art claim strength | Pending v2 round. | OPEN; novelty boundary and headline ledger rows must be challenged. | no |
| 13 evidence provenance strategy | Pending v2 round. | OPEN; evidence freshness, hashes, and missing Lean build must be explicit. | no |
| 14 AI smell | Pending v2 round. | OPEN; public surfaces need process-language inventory on current hash. | no |
| 15 adversarial convergence | Not eligible. | BLOCKED until 01-14 are provisionally closed. | no |

## Category-15 counters

- Category-15 adversarial convergence round count: 0
- Category-15 manuscript-hash reset count: 0
- GPT+Opus pair counts by category: 0 for all categories before round 001.
- Full-review GPT+Opus pair count: 0 before round 001.
