# Public excerpt of the development rulings

The Lean comments, the guide and the records cite development rulings by number (A1–A23). This is a release-specific summary of each cited ruling, with process and
worker references omitted. The original rulings remain the development authority.

- **A10** (the author: “prove it in the format stated in the paper, no shortcuts”). Theorem 1.1 is stated as printed: U and V are domains, φ is
  a conformal bijection U → V, h is a GFF plus a continuous function on V, both sides are domain metrics with the +∞ convention, and the
  almost-sure equality holds for all u, v at once. **A10.2:** following Gwynne–Miller, a domain field is given meaning through a whole-plane
  realization, and the statement must come with a proof that the domain metric does not depend on the realization. That proof is the frozen
  theorem `domainMetric_ae_eq_of_isDomainRealization`.
- **A11, decision D3.** Lemma 2.1 is proved as printed, with a constant C = C(ξ) that does not depend on U or φ (through a normalized
  univalent family and the Koebe distortion theorem).
- **A13.** A Gwynne–Miller-form corollary follows the root proof, with its own field-class interface (the zero-boundary class, the metric as a
  function of the field). Gwynne–Miller's literal “one map for every law” form is a stronger statement that needs its own proof.
- **A14** (the author: “assume that U, V are greenian domains so that the GFF actually exists”). The root assumes that U and V are Greenian.
  The realization-independence theorem keeps its unrestricted open-set binder.
- **A15.** The author delegated the final selection of statement revision 2.2 and explicitly chose the global field class. The approved
  choices are the root in the paper's format with the literal `ξ_crit`, the existence clause inside the root, every strong metric D, and the
  connectedness hypotheses. [APPROVAL-REQUEST.md](APPROVAL-REQUEST.md) is the public extract of the request.
- **A16** (graph review). All findings of the independent global review of the source graph are accepted; the second route for
  input (I2), lower semicontinuity plus an escape barrier, is admitted. **A17.1:** that route is the one the proof uses, being logically
  prior to Pfeffer's printed route, which presupposes its conclusion.
- **A17.2, A18, A20** (seal records). At each theorem's seal, every edge of the reviewed source dependency graph between nodes of that
  theorem's proof is either used by the Lean proof at term level or covered by a written deviation record. Edges between two frozen
  definitions, which never reference each other in Lean, are judged against the frozen definitions (A17.2). A18 accepts the 12 records of
  the realization-independence seal; A20 accepts the 189 records of the Theorem 1.1 seal after three independent reviews. The guide describes
  them under “How it was checked”.
- **A20.1** (after the first key-2 audit of Theorem 1.1). That audit failed on graph consumption only: nine references of the
  graph-to-Lean map did not state their nodes' content, and on the corrected map three rows were neither consumed nor covered by a record.
  The nine references were corrected, three records were added and one record text was corrected; no frozen file, manifest entry or Lean
  declaration changed. The check then passed (241 edges consumed, 184 rows covered by records, no failure), and the auditor's re-check
  returned `VERDICT: PASS`.
- **A21** (Gwynne–Miller-form statements, after an independent statement audit). Axiom IV is stated almost surely on the field's own
  probability space; both measurable maps are tied to the domain metrics on every realization extension, which rules out trivial maps;
  in the countable form the maps are chosen once, before countable families of fields and of conformal maps; the hypotheses are on U
  only (V = φ(U) is then connected and Greenian). One map per domain valid for every field law at once stays open.
- **A22** (release decisions). Among them: the website entry moves within research.html; the pinned text extraction of the manuscript
  and a public extract of the independent source-gap audit ship with the release; the Gwynne–Miller-form corollaries ship as
  independently audited supporting theorems, not frozen and not sealed.
- **A23** (Theorem 1.1 for every ξ > 0). A probe of the compiled proof shows that the hypothesis ξ > ξ_crit is never used. The
  supporting theorem `conformal_covariance_all_xi` states Theorem 1.1 without it; it implies the frozen theorem, which stays unchanged.
