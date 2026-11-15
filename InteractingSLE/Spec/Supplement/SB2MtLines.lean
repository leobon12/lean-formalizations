/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MtChart
import InteractingSLE.Spec.Restart.FCLocality

/-!
# The line-set inputs of SB2(2)'s kernel half from the line family

Packet PROVE-SB2-LCMEAN, round 12. The kernel half at a relative version (`Mt.hasSafeLaw_hasSafeMembers_of_stageLines`)
reads the union line sets `B t = A₁ t ∪ A₂ t` of the line family (`Ml.exists_sb2LineFamily_cf`) with locality for the
completed line filtration `Ms.lineFiltC P 𝓖 t` and a local-set mean at every time. From the line family's own
components:

* **`lineSets_inputs`**: history-avoidance locality for the completed filtration (completion by null sets,
  `Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma`) and a family of local-set means (Lemma 3.6 (iii),
  `LocalSets.isLocalSet_tfae`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mt

open LocalSets Ms

/-- **The line-set inputs of the kernel half from the line family's components**: locality of the union line sets
for the completed line filtration, and local-set means at every time. -/
theorem lineSets_inputs {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
    (hm : ∀ t, Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω))
    (hc : ∀ t ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω)))
    (hl : ∀ t, IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P)
    (hloc : ∀ t, WholeField.IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P) :
    (∀ t, WholeField.IsHistoryAvoidanceLocal (lineFiltC P 𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω)
      (WholeField.centredField h u₀) P) ∧
      ∃ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
        ∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P (g t) := by
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  refine ⟨fun t => Restart.FCPlumb.isHistoryAvoidanceLocal_aeSigma (hloc t), ?_⟩
  have hex : ∀ t, ∃ g, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂ t ω) (WholeField.centredField h u₀) P g := by
    intro t
    exact isGermConditionalLaw_iff.1
      (((isLocalSet_tfae hh0 (hm t) (Eventually.of_forall (hc t))).out 4 3).1 (hl t))
  choose g hg using hex
  exact ⟨g, hg⟩

end InteractingSLE.Theorem14.SB.Mt
