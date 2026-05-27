# Human audit summary

- Document: AACA / Editorial Manager build-evidence completion report
- Current state: CLOSED for source-level AACA formatting/build-submission checks; OPEN for full publication readiness.
- Did the bots find blockers? yes. Formatting/package blockers were addressed, but full publication readiness remains blocked by non-format scientific-reviewer gates.
- Reviewed manuscript target: current `paper/main.tex` and `paper/refs.bib`.
- Scientific-reviewer basis: final `review` and `improve` were rerun with structured formatting/AACA check-results.
- Forbidden actions honored: no Lean edits, no Lean/lake commands, no push.

## What was fixed and evidenced

The current paper source now uses the AACA source profile:

- `\documentclass{birkjour}`;
- `paper/birkjour.cls`, `paper/spmpsci.bst`, and `paper/cite.sty` included from AACA `birkjour.zip`;
- `paper/THIRD_PARTY_NOTICES.md` records vendor-file provenance;
- abstract is 177 words by the documented tokenizer;
- `Statements and Declarations` section includes Funding, Competing interests,
  Data availability, Code availability, and Author contributions;
- bibliography uses `spmpsci`;
- bibliography entries with DOI metadata include `https://doi.org/...` URL fields.

## Build evidence

The paper was built in a scratch directory, not in the repository:

```text
/tmp/spinorlean-aaca-latex-build
```

The final build artifacts copied into the review folder are:

| Artifact | SHA-256 |
| --- | --- |
| `review-01/final-artifacts/spinorlean-aaca.pdf` | `934d82f6708edc16e9a73d78e2384b2fe7d0ddf1abb427d26061eb5676deaa13` |
| `review-01/09-format-build-submission/build-evidence/main.log` | `0bbc4fe470485a70b11e7c70fd4cdcfa405049e155a3a5d46a9ca90a4130133e` |
| `review-01/09-format-build-submission/build-evidence/main-pdftotext.txt` | `0c3b93c3465568274b831d8b681777d6658ad1e322046a5a444f559c0f7c75bf` |
| `review-01/09-format-build-submission/build-evidence/main.bbl` | `ed0883c520d9c3c39be194d5dadc4ae7319b13f000435e6fed87637825d82f57` |
| `review-01/09-format-build-submission/build-evidence/main.blg` | `cd89a0de5b03b2194922f2ede9b9c2db253ac040d4173ca35c36a88c612a2f08` |

Final scans found:

- no `[?]` markers in extracted PDF text;
- no `??` markers in extracted PDF text;
- no undefined citation/reference warnings in the final log;
- no `Overfull` or `Underfull` warnings in the final log.

## Structured scientific-reviewer evidence

Structured check-results were generated only for checks backed by real artifacts:

- `snapshot_freeze`;
- `unitization_coverage`;
- `formatting_build_audit`;
- `aaca_birkjour_editorial_manager_audit`;
- `venue_compliance_audit`;
- `final_submission_artifact_gate`.

The final evidence-backed scientific-reviewer run reports:

- verdict: `NOT_READY`;
- completed required checks: 2,181;
- missing required checks: 25,063;
- final artifact blockers: none.

The remaining blockers are not AACA formatting/build blockers. They are the
unrun scientific-reviewer gates that require separate evidence, including
reference truth, citation support, adversarial review, proof-assistant reference
verification, independent source verification, reviewer work-proof, temporal
claim verification, prior-art threat modeling, and headline claim provenance.

## Remaining work outside this closed formatting lane

Full `PUBLICATION_READY` is not claimed. Completing it still requires real
evidence for the remaining scientific-reviewer gates; those checks must not be
filled with pass-shaped placeholders.
