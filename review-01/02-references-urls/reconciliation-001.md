# Human audit summary

- Document: 02-references-urls reconciliation 001
- Current state: OPEN
- Did the bots find blockers? yes. Opus and adversarial review required visible row-level URL classifications, and two publisher landings remain access-limited.
- Did the bots find other valid feedback? yes. Repository URLs and most DOI redirects have captured evidence and resolve cleanly.
- What changed because of this? The reconciliation records each URL row as clean, limited, or book/no-URL metadata limitation.
- What remains unresolved? Alternate evidence or human disposition for the ACM/AMS limited DOI landings.
- Can this category/global review close now? no, because fail-closed URL review cannot treat `403` publisher responses as full clean passes.

| ID | Kind | Plain-English finding | Where it was found | Fix or disposition | How the fix/disposition was verified |
| --- | --- | --- | --- | --- | --- |
| C02-R001 | blocker | Some DOI landings are access-limited. | HTTP header evidence | Keep open. | `Baez2002` and `MathlibCommunity2020` end in `403` after DOI redirects. |
| C02-R002 | valid-feedback | Most checked URLs are clean. | URL evidence files | Preserve as supporting evidence. | DOI/repository rows below show HTTP 200 final statuses where available. |
| C02-R003 | valid-feedback | Book entries without URLs are metadata limitations, not broken URLs. | `bib_inventory.json`, `reference_metadata_audit.json` | Keep as visible limitations. | The bibliography has no URL field for those book entries. |

## Reports reconciled

- GPT: `review-01/02-references-urls/round-001-gpt.md`, commit `a96b9d40a12b37458d4804d40c4e39a9cb02a41b`.
- Opus: `review-01/02-references-urls/round-001-opus.md`, commit `bb399218ee0aee7bb45f249c798a585edfb36f1f`.
- Adversarial: `review-01/02-references-urls/round-001-adversarial.md`, commit `13f96d1e0f774e60fac639002e3fd4365391f1f3`.

## URL classifications

| Entry | URL | Observed status path | Classification | Evidence |
| --- | --- | --- | --- | --- |
| LawsonMichelsohn1989 | no URL recorded | n/a | book/no-URL metadata limitation | `bib_inventory.json`, `reference_metadata_audit.json` |
| Chevalley1996 | no URL recorded | n/a | book/no-URL metadata limitation | `bib_inventory.json`, `reference_metadata_audit.json` |
| AtiyahBottShapiro1964 | `https://doi.org/10.1016/0040-9383(64)90003-5` | `302->200` | clean | `review-01/02-references-urls/evidence/http/AtiyahBottShapiro1964_https_doi.org_10.1016_0040-9383_64_90003-5.headers.txt` |
| Lounesto2001 | `https://doi.org/10.1017/CBO9780511526022` | `302->301->200` | clean | `review-01/02-references-urls/evidence/http/Lounesto2001_https_doi.org_10.1017_CBO9780511526022.headers.txt` |
| Artin1957GeometricAlgebra | no URL recorded | n/a | book/no-URL metadata limitation | `bib_inventory.json`, `reference_metadata_audit.json` |
| Baez2002 | `https://doi.org/10.1090/S0273-0979-01-00934-X` | `302->403` | limited | `review-01/02-references-urls/evidence/http/Baez2002_https_doi.org_10.1090_S0273-0979-01-00934-X.headers.txt` |
| LeanGA | `https://github.com/pygae/lean-ga` | `200` | clean | `review-01/02-references-urls/evidence/http/LeanGA_https_github.com_pygae_lean-ga.headers.txt` |
| Mathlib | `https://github.com/leanprover-community/mathlib4` | `200` | clean | `review-01/02-references-urls/evidence/http/Mathlib_https_github.com_leanprover-community_mathlib4.headers.txt` |
| Wieser2022Clifford | `https://doi.org/10.1007/s00006-021-01164-1` | `302->301->303->302->302->200` | clean | `review-01/02-references-urls/evidence/http/Wieser2022Clifford_https_doi.org_10.1007_s00006-021-01164-1.headers.txt` |
| deMouraUllrich2021 | `https://doi.org/10.1007/978-3-030-79876-5_37` | `302->301->303->302->302->200` | clean | `review-01/02-references-urls/evidence/http/deMouraUllrich2021_https_doi.org_10.1007_978-3-030-79876-5_37.headers.txt` |
| MathlibCommunity2020 | `https://doi.org/10.1145/3372885.3373824` | `302->403` | limited | `review-01/02-references-urls/evidence/http/MathlibCommunity2020_https_doi.org_10.1145_3372885.3373824.headers.txt` |

## Closure decision

Category 02 remains `OPEN`. The row table fixes the visibility objection, but the access-limited publisher rows still require alternate evidence or explicit human disposition.
