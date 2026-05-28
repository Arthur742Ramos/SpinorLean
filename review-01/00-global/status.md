# Human audit summary

- Document: scientific-reviewer-v2 global status
- Current state: OPEN
- Did the bots find blockers? yes. Round 001 found active blockers in categories 01-13; category 14 closed only for AI-smell/process-language inventory.
- Did the bots find other valid feedback? yes. v2 reports and reconciliations now preserve current non-Lean evidence while keeping Lean/platform/author-fact gaps open.
- What changed because of this? All category 01-14 GPT, Opus, adversarial, and reconciliation reports have been produced; category 14 was closed with an explicit category-08 AI-use separation.
- What remains unresolved? Categories 01-13, category 15 convergence, Lean build evidence, AACA/EM/SNAPP platform build evidence, author/platform facts, overlap corpus, and several paper-language/provenance blockers.
- Can this category/global review close now? no, because `ALL_CATEGORIES_CLOSED` is not satisfied and category 15 is not eligible.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| G-001 | blocker | Categories 01-13 remain open after round 001. | Category statuses and reconciliations | Keep global review open. | Each open category status lists active blockers. |
| G-002 | valid-feedback | Category 14 AI-smell/process-language inventory closed. | `review-01/14-ai-smell/reconciliation-001.md` | Closed category 14 only. | GPT, Opus, and adversarial reports agree no category-14 blocker remains; category 08 remains open for AI-use facts. |
| G-003 | blocker | Lean and platform build evidence remain unavailable. | Categories 01, 04, 05, 09, 11, 12, 13 | Keep affected categories open. | Local shell has no `lake`/`lean`; no AACA/EM/SNAPP platform log is archived. |
| G-004 | blocker | Human/author/platform facts cannot be invented. | Category 08 | Keep category 08 open. | No author-supplied corresponding-author/ORCID/AI-use facts are present. |

## Current target and evidence anchors

- Repository: `Arthur742Ramos/SpinorLean`
- Branch: `review/aaca-editorial-manager-paper`
- Latest pushed report-round head before reconciliation/status edits: `6d9da78bf3baa7f91543f35c5bbb185f246a499d`
- Current manuscript path: `paper/main.tex`
- Current final submission artifact path: `review-01/final-artifacts/spinorlean-aaca.pdf`
- Current manuscript SHA-256: `0fe7d33493bdce18ad2f3678a9ca12457ab04fc5552b834a403b6f9cf858efb2`
- Current final PDF SHA-256: `3e9ecb629eacad33394b6298c85f3025942b5e92f10c82c3af794d8b71b7fe17`
- Current extracted PDF text SHA-256: `b284ecc1d136af76c2756e0b2bd80ef5a5df54f10e1e0fa638f9fd017baffb52`
- Current bibliography SHA-256: `0ee187d548c35c24e86daf45f17aff494f9e2c879848f87c681a8007c1e53949`
- Headline claim provenance ledger: `review-01/00-global/headline-claim-provenance-ledger.md`
- Headline ledger currentness status: not globally closed; proof/build rows remain blocked until Lean build evidence exists.
- Active category: 01-13 remediation; category 15 remains prerequisite-blocked.
- Final status: NOT_ALL_CATEGORIES_CLOSED

## Venue assumption

Target venue is Advances in Applied Clifford Algebras (AACA) via the Springer Nature / Editorial Manager submission route, per user direction and `review-01/00-global/aaca-venue-profile.yaml`; this is a manuscript compliance review, not a venue-selection/ranking run.

The AACA evidence supports `birkjour`, LaTeX/AMS-LaTeX source, 150-250 word abstract, 4-6 keywords, MSC codes, numbered references, DOI links where available, and statements/declarations/data/code availability. Author Contribution and Competing Interest information are provided through the submission interface; this status does not reintroduce fabricated Author Contributions prose.

TeX Live 2018 compatibility remains only a conservative lower-bound strategy from prior AACA/Editorial Manager discussion when no current AACA/SNAPP/EM upload/build log is available. An actual current platform build log supersedes it.

## Tooling and readability gates

- `/home/david/repos/AGENTS.md`: readable.
- `/home/david/repos/scientific-reviewer/scientific-reviewer-v2/AGENTS.md`: readable.
- `rg`: available.
- v2 model pair selected: GPT-5.5 and Claude Opus 4.7.
- v2 CLI note: `/usr/local/bin/scientific-reviewer` is the older v1 CLI and is not used for v2.

## Public artifact locator inventory

| Locator source | Current locator text | Current manuscript? | Public/release/reproducibility claim remains? | Disposition |
| --- | --- | --- | --- | --- |
| `paper/main.tex` artifact table | `https://github.com/Arthur742Ramos/SpinorLean` plus source revision `e7c7bf09e6c4477124e85a7d4339c0b4a97e52ca` | yes | yes | Paper-facing locator and source revision are present; build verification remains open. |
| `paper/main.tex` code availability | `https://github.com/Arthur742Ramos/SpinorLean`; source revision `e7c7bf09e6c4477124e85a7d4339c0b4a97e52ca` | yes | yes | Same locator/revision repeated in declarations. |
| `README.md` and `paper/README.md` | Repository-relative source descriptions; no substitute for paper-facing locator | no, README surfaces only | yes, repository is the artifact surface | Acceptable only because the manuscript itself contains the repository URL and source revision; README scope alignment remains category 10 work. |
| Prior v1 review artifacts | Historical AACA and scientific-reviewer paths under `review-01/` | no | no submission-facing claim | Indexed as legacy v1/v1-like evidence, not v2 closure evidence. |
| Commit `e7c7bf0` | Removed unsupported Author Contributions paragraph from manuscript/PDF | n/a | declarations remain | Not blocker laundering; AACA evidence supports interface-submitted author-contribution metadata rather than manuscript prose. |

## Category dashboard

| Category | Did it find blockers or valid feedback? | Current disposition | Closed? |
| --- | --- | --- | --- |
| 01 snapshot artifacts | yes; Lean build, submission-PDF designation, and rc1 toolchain rationale remain. | OPEN; non-Lean hashes are current but build/snapshot reproducibility remains blocked. | no |
| 02 references URLs | yes; per-URL table is surfaced, but ACM/AMS publisher landings remain access-limited. | OPEN; limited DOI rows need alternate evidence or human disposition. | no |
| 03 citation support | yes; load-bearing prior-art citation support needs stronger quote/page evidence. | OPEN; citation audit granularity is recorded but insufficient for closure. | no |
| 04 factual independent verification | yes; proof/formalization claims need current Lean build evidence. | OPEN; static facts are limited support only. | no |
| 05 math formal artifacts | yes; Lean build and exact static-scan coverage are missing. | OPEN; static theorem-index/proof-hole scans do not close proof validity. | no |
| 06 overlap provenance | yes; corpus and search transcripts are missing. | OPEN; likely comparison set is identified but unevidenced. | no |
| 07 language definitions grammar | yes; terminology/notation blockers remain despite public-surface cleanup. | OPEN; weight-2/vacuum-line, `exact`, and `~{}` issues remain. | no |
| 08 venue fit compliance | yes; author/platform facts, AI-use facts, and platform build evidence are missing. | OPEN; reviewer must not invent these facts. | no |
| 09 format build submission | yes; local build evidence exists but no platform build log exists. | OPEN; platform compiler evidence and title-page/warning classification remain. | no |
| 10 edit regression instructions consistency | yes; reader Lean instructions cannot be validated locally. | OPEN; instruction/path inventory and README scope alignment remain. | no |
| 11 claim density methodology temporal | yes; build, command transcript, temporal, and boundary checks remain. | OPEN; static numerical support is only partial. | no |
| 12 contribution prior art claim strength | yes; proof-dependent contribution claims and prior-art support remain open. | OPEN; no unsupported first-ever overclaim was found on checked surfaces. | no |
| 13 evidence provenance strategy | yes; build/provenance, sidecar/currentness, and limited URL disposition gaps remain. | OPEN; current hashes and report-head attestation are supporting evidence only. | no |
| 14 AI smell | yes; no active category-14 blocker remained, and category-08 AI-use facts were kept separate. | CLOSED by `review-01/14-ai-smell/reconciliation-001.md`. | yes |
| 15 adversarial convergence | yes; prerequisites are not met. | BLOCKED until categories 01-14 are closed. | no |

## Global active blockers

- Categories 01-13 are not closed.
- Category 15 cannot run until categories 01-14 are closed.
- Lean build evidence is unavailable locally and no equivalent CI evidence is archived.
- AACA/EM/SNAPP platform build evidence is unavailable.
- Author/platform facts and AI-use facts must come from authors/platform, not reviewer inference.
- Overlap/provenance corpus and several category-specific evidence inventories remain missing.
