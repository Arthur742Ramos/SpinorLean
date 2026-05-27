# Human audit summary

- Document: policy reference note
- Current state: OPEN.
- Did the bots find blockers? yes. AACA policy checks identify current-source formatting and packaging gaps.
- Reviewed manuscript target: `paper/main.tex` and `paper/refs.bib`.
- Old EM PDF usage: historical failure evidence only.

## Policy sources used

The AACA submission-guidelines page was fetched earlier in this session from:

```text
https://link.springer.com/journal/6/submission-guidelines
```

The local extracted text used for this review is:

```text
/root/.copilot/session-state/da00dae5-d2f3-45ca-bcfb-f40cb48dedcd/files/aaca-evidence/aaca-submission-guidelines.text
```

## AACA policy excerpts applied

- Source files: AACA requires all relevant editable source files at every submission and revision; incomplete editable source files can prevent review. Evidence: extracted AACA text lines 79-80.
- Abstract: AACA asks for an abstract of 150 to 250 words and no undefined abbreviations or unspecified references. Evidence: extracted AACA text lines 107-108.
- Keywords: AACA asks for 4 to 6 keywords. Evidence: extracted AACA text lines 112-113.
- Declarations: AACA asks for "Statements and Declarations" and says incomplete submissions may be returned. Evidence: extracted AACA text lines 114-118.
- LaTeX final version: AACA requires LaTeX or AMS-LaTeX for final accepted papers, provides `birkjour.cls`, says the first line should be `\documentclass{birkjour}`, and recommends not modifying the class file. Evidence: extracted AACA text lines 120-128.
- Text formatting: AACA says manuscripts should be submitted in LaTeX. Evidence: extracted AACA text line 136.
- MSC: AACA asks for appropriate MSC codes. Evidence: extracted AACA text lines 148-151.
- References: AACA asks for numbered square-bracket citations, numbered reference-list entries, and full DOI links where available. Evidence: extracted AACA text lines 153-162.
- Data Availability: original research must include a Data Availability Statement. Evidence: extracted AACA text lines 283-289.
- Declarations before references: declaration summaries should be placed in a `Declarations` section before references under headings such as `Funding` and/or `Competing interests`; other declarations include Ethics approval, Consent, Data, Material and/or Code availability, and Author contribution statements. Evidence: extracted AACA text lines 483-486.

## Submission-system uncertainty

The old PDF is an Editorial Manager / ProduXion Manager assembled PDF, but the current reviewed `paper/` source has no current EM build log. The compiler version for the current resubmission is therefore unverified. A future current-platform build log should supersede generic Springer/Aries guidance.
