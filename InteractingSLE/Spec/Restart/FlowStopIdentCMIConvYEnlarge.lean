/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYClosure

/-! # Measurable enlargements of Gaussian local sets -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper LQGMetric LocalSets

/-- An extensive measurable operation on sets loses no marked-avoidance
information: if its output avoids `U`, its input also avoids `U`, and the input
is then completely recorded. -/
theorem markedSigma_enlarge_le {S : Type*} (A : S → Set ℂ) {Φ : Set ℂ → Set ℂ}
    (hΦ : Measurable[hittingSigma, hittingSigma] Φ) (hext : ∀ T, T ⊆ Φ T)
    {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    markedSigma (fun ω => Φ (A ω)) U ≤ markedSigma A U := by
  have hrec : Measurable[markedSigma A U, hittingSigma] (fun ω => markedSet U (A ω)) :=
    measurable_iff_comap_le.2 le_sup_right
  have hEm := measurableSet_avoid_markedSigma A U
  have hE : MeasurableSet[markedSigma A U] {ω | Disjoint (Φ (A ω)) U} := by
    have he : {ω | Disjoint (Φ (A ω)) U} = {ω | Disjoint (A ω) U} ∩
        (fun ω => Φ (markedSet U (A ω))) ⁻¹' {T | Disjoint T U} := by
      ext ω
      by_cases ha : Disjoint (A ω) U
      · simp [markedSet, ha]
      · have hb : ¬ Disjoint (Φ (A ω)) U := fun hb => ha (hb.mono_left (hext _))
        simp [ha, hb]
    rw [he]
    exact hEm.inter ((hΦ.comp hrec) (measurableSet_avoid hU hUH))
  refine sup_le (MeasurableSpace.generateFrom_le ?_) (Measurable.comap_le ?_)
  · rintro _ rfl
    exact hE
  · refine @measurable_generateFrom S (Set ℂ) (markedSigma A U) _ _ ?_
    rintro _ ⟨V, hV, hVH, rfl⟩
    have he : (fun ω => markedSet U (Φ (A ω))) ⁻¹' {T | (T ∩ V).Nonempty} =
        {ω | Disjoint (Φ (A ω)) U} ∩
          (fun ω => Φ (markedSet U (A ω))) ⁻¹' {T | (T ∩ V).Nonempty} := by
      ext ω
      by_cases hb : Disjoint (Φ (A ω)) U
      · have ha := hb.mono_left (hext (A ω))
        simp [markedSet, ha, hb]
      · simp [markedSet, hb]
    rw [he]
    exact hE.inter ((hΦ.comp hrec) (measurableSet_hitting hV hVH))

/-- A measurable enlargement of a local set remains local, provided its values
are almost surely relatively closed subsets of the field domain. In particular,
the Gaussian part of a hull-filling argument needs no new hypothesis. -/
theorem isLocalSet_enlarge {S : Type u} [mS : MeasurableSpace S]
    {P : Measure S} [IsProbabilityMeasure P] {h : S → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : S → Set ℂ}
    (hA : Measurable[mS, hittingSigma] A) (hloc : IsLocalSet A h P)
    {Φ : Set ℂ → Set ℂ} (hΦ : Measurable[hittingSigma, hittingSigma] Φ)
    (hext : ∀ T, T ⊆ Φ T)
    (hclosed : ∀ᵐ ω ∂P, Φ (A ω) ⊆ H ∧ IsOpen (H \ Φ (A ω))) :
    IsLocalSet (fun ω => Φ (A ω)) h P := by
  apply ((isLocalSet_tfae hh (hΦ.comp hA) hclosed).out 2 4).1
  intro U G hUH hG hMD
  exact (IsLocalSet.isMarkedAvoidanceLocal hh.measurable hA hloc U G hUH hG hMD).mono
    (markedSigma_enlarge_le A hΦ hext U.isOpen hUH) le_rfl

end InteractingSLE.Restart.FlowStopIdentCMI
