import QuantumZipper.SLE.Defs
import InteractingSLE.SLE8.Final

/-!
# Provider of `InteractingSLE.SLE8.ae_exists_continuous_trace`

Quarantined while the anchor `sle8_thm_1_1_v1` is DRAFT_SORRY: only its frozen file and audit files
may import this module. Packet PROVE-S8-FINAL.

## Proof
`InteractingSLE.SLE8.ae_exists_continuous_trace_final` (`InteractingSLE/SLE8/Final.lean`) has
exactly the anchor's statement: the assembly
`ae_exists_continuous_trace_of_corollaryOne_of_scale_count` (`Assembly.lean`) applied to [AL14]
Corollary 1 (`al14CorollaryOneStatement_holds`) and Proposition 4.1 (`scaleCount_of_lemma31` with
Lemma 3.1, `lemma31Statement_holds`).

## Binder form
All data arguments are implicit; the anchor's hypothesis `hB` is an auto-parameter
`(hB : IsBrownianReal B P := by assumption)`, so the sealed body is the bare `by exact <provider>`.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace InteractingSLE.SLE8.Provider

/-- Provider of the frozen Theorem 1.1 of the SLE₈ note
(`InteractingSLE.SLE8.ae_exists_continuous_trace`), with exactly its type (data arguments implicit,
the hypothesis an auto-parameter filled by `assumption`). -/
theorem ae_exists_continuous_trace {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P := by assumption) :
    ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ,
      TendstoLocallyUniformly
          (fun (y : ℝ) (t : ℝ≥0) =>
            QuantumZipper.fwdMapInv (QuantumZipper.drive 8 B ω) t (y * Complex.I))
          γ (𝓝[>] 0) ∧
        Continuous γ ∧ (∀ t, γ t ∈ QuantumZipper.Hbar) ∧ γ 0 = 0 ∧
        ∀ t : ℝ≥0,
          (∃ z ∈ QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t,
              connectedComponentIn (QuantumZipper.H \ γ '' Icc 0 t) z =
                QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) ∧
            ¬ Bornology.IsBounded
              (QuantumZipper.H \ QuantumZipper.fwdHull (QuantumZipper.drive 8 B ω) t) :=
  InteractingSLE.SLE8.ae_exists_continuous_trace_final hB

end InteractingSLE.SLE8.Provider
