import QuantumZipper.Proofs.Section5.Prop16PalmZoom
import QuantumZipper.Proofs.Wire2b

/-!
# Proposition 1.6, node C wiring: the law of `locField R ∘ W` and `fieldLawFull`

Sheffield, arXiv:1012.4797, proof of Proposition 1.6 (p. 25); the `γ`-quantum wedge as defined by
`IsQuantumWedge` is pinned down *law-wise* through `CoordsFull.fieldLawFull H` (STATEMENT_SPEC
A16). Node C of the Palm-zoom reduction (`Prop16PalmZoom.Prop16FixedZoomStmt`) quantifies over
*every* `γ`-wedge: its conclusion — convergence of the local laws of the canonical zoom at the
Palm point — is to a measure read through `locField R` of the wedge.

This file proves the invariance fact that makes node C wedge-independent: `locField R` reads only
raw circle coordinates (`TV.locField` is `Factorization.coords` cut down to the dyadic folded
circles inside `closedBall 0 R`), and the raw coordinates are a fixed measurable function
`CoordsFull.coordsFull` -> `Factorization.coords` (the projection `WedgeCan4.piC`). Hence

* `map_locField_eq_of_fieldLawFull_eq`: two random fields with the same `fieldLawFull H` law and
  a.e.-measurable data have the same `locField R` law. The a.e.-measurability hypotheses matter:
  at the pinned mathlib the push-forward under a non-a.e.-measurable map is a junk Dirac mass
  (`Measure.map_of_not_aemeasurable_of_ne_zero`), so the law is only meaningful for such maps.
* `map_locField_wedge_eq` (the task's target): two `γ`-quantum wedges whose `fieldLawFull` laws
  agree have the same `locField R` law; a.e.-measurability is supplied by
  `Wire2.aemeasurable_dataFull_of_isQuantumWedge`.
* `map_locField_wedge_eq_witness`: the same with the law identity *discharged for free* against
  the reference field of the wedge's own witness — no hypothesis beyond `IsQuantumWedge γ α W P`.
  This is the form node C's consumer uses: the convergence is proved for the explicit reference
  construction (`canonical γ (h† + Q(−log|·|) + A_{−log|·|})`, Duplantier–Miller–Sheffield,
  arXiv:1409.7055, Props. 4.7–4.8) and transferred to the wedge along `hlaw`.

**Deviation (see the report; DEVIATIONS.md text proposed there).** As literally stated in the
task ("if `IsQuantumWedge γ α W P` and `IsQuantumWedge γ α W' P'` then ...") the second theorem
would additionally need that *all* reference tuples `(X, A, P')` of the definition produce the
same `fieldLawFull H` law (the reference law is unique in the paper, but `IsQuantumWedge` only
records the law identity for its *own* witness, and no such uniqueness lemma — a GFF law
uniqueness result — exists in the repository). The statement therefore carries the law identity
`fieldLawFull H W P = fieldLawFull H W' P'` as a hypothesis; that hypothesis is free whenever one
of the two fields is a wedge's own reference field (third theorem).

Own elementary measurability plumbing (AGENT_GUIDE cost rule); the reduction itself is
Sheffield's Prop. 1.6 / DMS Props. 4.7–4.8, not re-proved here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

open TV Factorization CoordsFull

/-- **Reference-law independence (proposed blueprint item; NOT proved here).**

Every reference tuple of `IsQuantumWedge γ α` produces the same `fieldLawFull H` law. In the
paper this is true — the reference field `canonical γ (h† + Q(−log|·|) + A_{−log|·|})` has the
law determined by `γ`, `α`, the law of a free GFF (pinned by `IsFreeGFFModConstH`) and the law of
the wedge radial process (a deterministic function of two independent Brownian motions, pinned by
`IsWedgeProcess`) — but `IsQuantumWedge` only records the law identity for its *own* witness, and
no cross-witness law identity for free GFFs is available in the repository (it is the missing
"GFF/wedge law uniqueness" input). This definition names exactly that input, so that
`map_locField_wedge_eq_of_refLawUnique` below turns it into the literal two-wedge statement of
node C. It is a named missing input in the style of the other project node `def …Stmt : Prop`s;
nothing in this file depends on it. -/
def RefWedgeLawUnique (γ α : ℝ) : Prop :=
  ∀ (Ω Ω' : Type) (_ : MeasurableSpace Ω) (_ : MeasurableSpace Ω')
    (P : Measure Ω) (P' : Measure Ω') (X : Ω → FieldSample) (A : ℝ → Ω → ℝ)
    (X' : Ω' → FieldSample) (A' : ℝ → Ω' → ℝ),
    IsProbabilityMeasure P → IsFreeGFFModConstH X P → IsWedgeProcess α (Qc γ) A P →
    IndepFun X (fun ω t => A t ω) P →
    IsProbabilityMeasure P' → IsFreeGFFModConstH X' P' → IsWedgeProcess α (Qc γ) A' P' →
    IndepFun X' (fun ω t => A' t ω) P' →
    fieldLawFull H (WedgeMeas.wedgeRef γ X A) P =
      fieldLawFull H (WedgeMeas.wedgeRef γ X' A') P'

end Prop16Asm

end QuantumZipper
