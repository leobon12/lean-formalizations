/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafVersionFOptional
import InteractingSLE.Spec.Sec2.RestartMarkov

/-!
# From an ordinary closed process to the survival reader

Optional sampling and the common Borel reader are constructed here. The two
stochastic ingredients left to the application are a continuous closed
process and compatibility of its conditional expectations with the raw past.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.FlowStopIdentG

/-- A continuous adapted fixed-time closed process satisfies the closed
conditional-expectation identity at every bounded stopping time. -/
theorem ae_closed_process_at_bounded_stop
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {𝓓 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ}
    (hX : StronglyAdapted 𝓓 X) (hn : ∀ t, nullSigma P ≤ 𝓓 t)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hclosed : ∀ t, X t =ᵐ[P] P[Z | 𝓓 t])
    {T : Ω → ℝ≥0∞} (hT : IsStoppingTime 𝓓 fun ω => (T ω : WithTop ℝ≥0))
    (hbound : ∃ N : ℝ≥0, ∀ ω, T ω ≤ N) :
    P[Z | hT.measurableSpace] =ᵐ[P] fun ω => X (T ω).toNNReal ω := by
  obtain ⟨X', hXa, hXc, hXe, hXclosed⟩ := exists_continuous_closed_version hX hn hc hclosed
  have hmart : Martingale X' 𝓓 P :=
    (martingale_condExp Z 𝓓 P).congr hXa (fun t => (hXclosed t).symm)
  exact (ae_closed_martingale_at_bounded_stop hmart hXc hXclosed hT hbound).trans
    (hXe.mono fun ω hω => hω (T ω).toNNReal)

/-- If conditioning on the driving past and raw sample past agrees for the
closing variable, the process is measurable for the completed raw dyadic past. -/
theorem measurable_rawPast_process_of_condExp_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓓 : Filtration ℝ≥0 mΩ}
    {nL nR : ℕ} {Y : Ω → HistorySpace nL nR} (hY : Measurable Y)
    {X : ℝ≥0 → Ω → ℝ} {Z : Ω → ℝ} (hX : StronglyAdapted 𝓓 X)
    (hclosed : ∀ t, X t =ᵐ[P] P[Z | 𝓓 t])
    (hpast : ∀ p, P[Z | 𝓓 (dyadicTime p)] =ᵐ[P] P[Z | samplePastSigma Y (dyadicTime p)])
    (p : ℕ × ℕ) :
    Measurable[samplePastSigma Y (dyadicTime p) ⊔ nullSigma P] (X (dyadicTime p)) := by
  apply Sec2.Restart.measurable_of_ae_eq_of_null
    (sup_le (samplePastSigma_le hY _) (MeasurableSpace.generateFrom_le fun _ hs => hs.1))
    (fun A hA hA0 => (le_sup_right : nullSigma P ≤ samplePastSigma Y (dyadicTime p) ⊔ nullSigma P)
      A (MeasurableSpace.measurableSet_generateFrom ⟨hA, hA0⟩))
    ((stronglyMeasurable_condExp (μ := P) (m := samplePastSigma Y (dyadicTime p)) (f := Z)).measurable.mono
      le_sup_left le_rfl)
    ((hX (dyadicTime p)).measurable.mono (𝓓.le _) le_rfl)
    ((hclosed (dyadicTime p)).trans (hpast p)).symm

/-- The common optional survival reader is constructed from a continuous
closed process and raw-past compatibility at deterministic dyadic times. -/
theorem exists_optionalSurvivalReader_of_closed_process
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓓 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞}
    {nL nR : ℕ} {Y : Ω → HistorySpace nL nR} (hY : Measurable Y)
    {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted 𝓓 X)
    (hn : ∀ t, nullSigma P ≤ 𝓓 t)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => X t ω))
    (hclosed : ∀ t, X t =ᵐ[P] P[fun ω => survivalDiscount (V ω) | 𝓓 t])
    (hpast : ∀ p, P[fun ω => survivalDiscount (V ω) | 𝓓 (dyadicTime p)] =ᵐ[P]
      P[fun ω => survivalDiscount (V ω) | samplePastSigma Y (dyadicTime p)]) :
    ∃ M : HistorySpace nL nR → ℝ≥0 → ℝ,
      (∀ p, Measurable fun γ => M γ (dyadicTime p)) ∧ IsNonAnticipating M ∧
      (∀ᵐ ω ∂P, Continuous (M (Y ω))) ∧ IsOptionalSurvivalReader P 𝓓 V Y M := by
  obtain ⟨M, hMm, hMn, hMe⟩ := exists_historyReader_of_rawPast_process hY hc
    (measurable_rawPast_process_of_condExp_eq hY hX hclosed hpast)
    (fun p => integrable_condExp.congr (hclosed (dyadicTime p)).symm)
  refine ⟨M, fun p => hMm (dyadicTime p), hMn, ?_, ?_⟩
  · filter_upwards [hc, hMe] with ω hc he
    have hpath : M (Y ω) = fun t => X t ω := funext he
    rw [hpath]
    exact hc
  · intro T hT hbound
    exact (ae_closed_process_at_bounded_stop hX hn hc hclosed hT hbound).trans
      (hMe.mono fun ω hω => (hω (T ω).toNNReal).symm)

end InteractingSLE.WFS
