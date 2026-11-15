# The mathematical specification

[`ig1-specification.pdf`](ig1-specification.pdf) is *Imaginary Geometry I: mathematical specification*, 671 pages. Its SHA-256 is `88157ccbdb236054da6e1ca562e7b6a5628d737a4b3eb621c905461f87fdb92f`. It is the document from which the formal statements of this release were drafted, audited and frozen.

The document was prepared for this formalization as an independent mathematical edition of Jason Miller and Scott Sheffield, *Imaginary geometry I: interacting SLEs*, Probability Theory and Related Fields 164 (2016), 553–705, [arXiv:1201.1496](https://arxiv.org/abs/1201.1496):
- It keeps the paper's section and theorem numbers.
- It writes out the definitions, statements and proofs in full detail, including the hypotheses on domains, force words, lifetimes, filtrations and field frames.
- It adds supplementary proofs and precise interfaces. These start on p. 446 and include the boundary-walk lemmas of Theorem 1.4.

As its first page says, the original mathematics and the retained illustrations are by Miller and Sheffield. The document asserts no Lean check itself; the Lean checks are those of this release.

## Transcription

The folder [`transcription/`](transcription/) is a page-anchored Markdown transcription of the PDF, in 14 files of 48 pages each. It was made during the formalization so that Lean comments could cite exact places. The PDF is authoritative.

The Lean source comments cite these files under their development paths: `source/spec/p001-048.md`, with anchors such as `#thm-1.1`, `<!-- page N -->` markers and line numbers `L818`. The development path `source/spec/<file>` is `transcription/<file>` here, and `source/ig1-specification.pdf` is the PDF above.

## Related documents

- [Result guide](../README.md): the formal statements, how they read the paper, and how they were checked.
- [Errata](../ERRATA.md): errors in the paper, and in this specification, found by the formalization.
- [Correspondence](../CORRESPONDENCE.md): differences between the Lean statements and the paper, theorem by theorem.
