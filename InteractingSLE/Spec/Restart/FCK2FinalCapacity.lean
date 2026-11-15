/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2FinalSource

/-!
# Capacity filtration comparison from observed driver cuts

The concrete completed retained-driver filtration needs only observations of
driver coordinates on clock cuts. Safe laws in the physical time change then
pass to this completed filtration by measurable versions of events.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)
namespace InteractingSLE.Restart.FCPlumb
open DomainMarkov DomainMarkov.Aux79 DomainMarkov.K2 LocalSets
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The source's completed driver events have physical-time-change versions,
provided the retained history and all cut driver observations are observed. -/
theorem fcRetained_events_of_observed_cuts {d : PairData Ω} (hd : d.IsMeasGood)
    (W : ℝ≥0 → Ω → ℝ) (hm : ∀ q, Measurable (W q))
    {𝓖 : Filtration ℝ≥0 mΩ} {Qc : ℝ≥0 → Ω → ℝ≥0}
    (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hret : Measurable[𝓖 0] (retHist d))
    (hobs : ∀ q t, Measurable[𝓖 t] ({ω | q ≤ Qc t ω}.indicator (W q))) :
    ∀ q D, MeasurableSet[fcRetainedDriverFiltration P hd W hm q] D →
      ∃ A, MeasurableSet[timeChange 𝓖 Qc hQa q] A ∧ D =ᵐ[P] A := by
  have hWtc (q) : Measurable[timeChange 𝓖 Qc hQa q] (W q) := by
    intro A hA
    refine ⟨hm q hA, fun t => ?_⟩
    have hC : MeasurableSet[𝓖 t] {ω | q ≤ Qc t ω} :=
      measurableSet_le measurable_const (hQa t)
    have he : (W q) ⁻¹' A ∩ {ω | q ≤ Qc t ω} =
        ({ω | q ≤ Qc t ω}.indicator (W q)) ⁻¹' A ∩ {ω | q ≤ Qc t ω} := by
      ext ω
      by_cases hω : q ≤ Qc t ω <;> simp only [mem_inter_iff, mem_preimage,
        mem_ofPred_eq, indicator_apply, hω, ite_true, ite_false, and_true, and_false]
    rw [he]
    exact (hobs q t hA).inter hC
  have hraw := fcDriverFiltration_le_timeChange (retHist d) W hd.measurable_retHist hm hQa hret hWtc
  intro q D hD
  obtain ⟨A, hA, he⟩ := hD.2
  exact ⟨A, hraw q _ hA, he⟩

variable {𝓕 𝓗 : Filtration ℝ≥0 mΩ} {M : Set Ω} {U : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens}

/-- Safe Gaussian identities pass to a filtration whose events have a.s.
versions in the original filtration. -/
theorem hasSafeLaw_of_ae_event_versions {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hv : ∀ q D, MeasurableSet[𝓗 q] D → ∃ A, MeasurableSet[𝓕 q] A ∧ D =ᵐ[P] A)
    (hs : HasSafeLaw κ ρL ρR P 𝓕 M U W VL VR X) :
    HasSafeLaw κ ρL ρR P 𝓗 M U W VL VR X := by
  intro ψ q D hD hsafe
  obtain ⟨A, hA, he⟩ := hv q D hD
  have hsafeA : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ M ∧ ω ∈ avoidSet W U ψ q := by
    filter_upwards [hsafe, he] with ω hω heω hωA
    exact hω (heω.symm ▸ hωA)
  rw [setIntegral_congr_set he, setIntegral_congr_set he]
  exact hs ψ q A hA hsafeA

/-- Complement-member identities pass through the same completed event comparison. -/
theorem hasSafeMembers_of_ae_event_versions
    (hv : ∀ q D, MeasurableSet[𝓗 q] D → ∃ A, MeasurableSet[𝓕 q] A ∧ D =ᵐ[P] A)
    (hs : HasSafeMembers P 𝓕 M U W X) : HasSafeMembers P 𝓗 M U W X := by
  intro q Fb hFb D hD hsafe f Ξ
  obtain ⟨A, hA, he⟩ := hv q D hD
  have hsafeA : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ M ∧ (q : ℝ≥0∞) < U ω ∧
      Disjoint (Coupling.ballsK Fb) (QuantumZipper.fwdHull (fun s : ℝ => W s.toNNReal ω) q) := by
    filter_upwards [hsafe, he] with ω hω heω hωA
    exact hω (heω.symm ▸ hωA)
  rw [setIntegral_congr_set he, setIntegral_congr_set he]
  exact hs q Fb hFb A hA hsafeA f Ξ

section Concrete
variable {d : PairData Ω} (hd : d.IsMeasGood)
  (hm : ∀ q, Measurable (W q))
  {𝓖 : Filtration ℝ≥0 mΩ} {Qc : ℝ≥0 → Ω → ℝ≥0}
  (hQa : ∀ t, Measurable[𝓖 t] (Qc t)) (hret : Measurable[𝓖 0] (retHist d))
  (hobs : ∀ q t, Measurable[𝓖 t] ({ω | q ≤ Qc t ω}.indicator (W q)))

include hret hobs

/-- The physical time-change (S) gives (S) for the concrete source filtration
once the clock-cut observations are established. -/
theorem hasSafeLaw_fcRetained_of_observed_cuts {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hs : HasSafeLaw κ ρL ρR P (timeChange 𝓖 Qc hQa) M U W VL VR X) :
    HasSafeLaw κ ρL ρR P (fcRetainedDriverFiltration P hd W hm) M U W VL VR X :=
  hasSafeLaw_of_ae_event_versions (fcRetained_events_of_observed_cuts hd W hm hQa hret hobs) hs

/-- The physical time-change (L) gives (L) in that same concrete filtration. -/
theorem hasSafeMembers_fcRetained_of_observed_cuts
    (hs : HasSafeMembers P (timeChange 𝓖 Qc hQa) M U W X) :
    HasSafeMembers P (fcRetainedDriverFiltration P hd W hm) M U W X :=
  hasSafeMembers_of_ae_event_versions (fcRetained_events_of_observed_cuts hd W hm hQa hret hobs) hs

end Concrete

end InteractingSLE.Restart.FCPlumb
