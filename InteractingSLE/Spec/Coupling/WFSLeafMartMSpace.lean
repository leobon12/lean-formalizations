/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafFullLAssembly

/-!
# The vector space of terminal variables with continuous closed means

The elementary gains of any continuous martingale belong to this space.
These are the test functions in the Douglas density argument (Revuz--Yor,
Chapter V, Theorem (4.4) and Proposition (4.5), printed p. 210).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Terminal real variables admitting an adapted continuous closed process.
This is a linear subspace of actual functions, with integrability included. -/
def continuousClosedSpace (𝓓 : Filtration ℝ≥0 mΩ) (P : Measure Ω) [IsFiniteMeasure P] :
    Submodule ℝ (Ω → ℝ) where
  carrier := {Z | Integrable Z P ∧ ∃ X : ℝ≥0 → Ω → ℝ,
    StronglyAdapted 𝓓 X ∧ (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) ∧
      ∀ t, X t =ᵐ[P] P[Z | 𝓓 t]}
  zero_mem' := by
    refine ⟨integrable_zero _ _ _, 0, stronglyAdapted_zero _ _,
      ae_of_all _ fun _ => continuous_const, fun t => ?_⟩
    simp only [condExp_zero, Pi.zero_apply, Filter.EventuallyEq.rfl]
  add_mem' := by
    rintro Z Y ⟨hZi, X, hXa, hXc, hXe⟩ ⟨hYi, M, hMa, hMc, hMe⟩
    refine ⟨hZi.add hYi, X + M, hXa.add hMa, ?_, fun t => ?_⟩
    · filter_upwards [hXc, hMc] with ω hX hM using hX.add hM
    · exact ((hXe t).add (hMe t)).trans (condExp_add hZi hYi (𝓓 t)).symm
  smul_mem' := by
    rintro c Z ⟨hZi, X, hXa, hXc, hXe⟩
    refine ⟨hZi.smul c, c • X, hXa.smul c, ?_, fun t => ?_⟩
    · exact hXc.mono fun ω hω => hω.const_smul c
    · exact ((hXe t).const_smul c).trans (condExp_smul c Z (𝓓 t)).symm

/-- Constant terminal variables have their constant closed process. -/
theorem const_mem_continuousClosedSpace (𝓓 : Filtration ℝ≥0 mΩ) (c : ℝ) :
    (fun _ : Ω => c) ∈ continuousClosedSpace 𝓓 P := by
  refine ⟨integrable_const c, fun _ _ => c, fun _ => stronglyMeasurable_const,
    ae_of_all _ fun _ => continuous_const, fun t => ?_⟩
  exact EventuallyEq.of_eq (condExp_const (𝓓.le t) c).symm

/-- Deterministic stopping gives the closed process of a martingale value. -/
theorem condExp_martingale_eq_min {𝓓 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M 𝓓 P) (t u : ℝ≥0) :
    P[M t | 𝓓 u] =ᵐ[P] M (min u t) := by
  rcases le_total u t with hut | htu
  · simpa only [min_eq_left hut] using hM.condExp_ae_eq hut
  · rw [min_eq_right htu]
    exact EventuallyEq.of_eq (condExp_of_stronglyMeasurable (𝓓.le u)
      ((hM.stronglyAdapted t).mono (𝓓.mono htu)) (hM.integrable t))

/-- A bounded predictable single-interval gain has continuous closed means.
Its process is the difference of two deterministically stopped martingales,
multiplied by the past event. The difference vanishes before the event is known. -/
theorem indicator_martingale_increment_mem_continuousClosedSpace
    {𝓓 : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓓 P)
    (hMc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[𝓓 s] A) :
    A.indicator (M t - M s) ∈ continuousClosedSpace 𝓓 P := by
  let X : ℝ≥0 → Ω → ℝ := fun u => A.indicator (M (min u t) - M (min u s))
  have hi := ((hM.integrable t).sub (hM.integrable s)).indicator (𝓓.le s _ hA)
  have hzero : P[A.indicator (M t - M s) | 𝓓 s] =ᵐ[P] 0 := by
    apply (condExp_indicator ((hM.integrable t).sub (hM.integrable s)) hA).trans
    filter_upwards [condExp_sub (hM.integrable t) (hM.integrable s) (𝓓 s),
      hM.condExp_ae_eq hst, hM.condExp_ae_eq (le_refl s)] with ω h1 h2 h3
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, Pi.sub_apply, h1, h2, h3, sub_self, Pi.zero_apply]
    · simp only [indicator_of_notMem hω, Pi.zero_apply]
  refine ⟨hi, X, ?_, ?_, fun u => ?_⟩
  · intro u
    by_cases hsu : s ≤ u
    · exact (((hM.stronglyAdapted (min u t)).mono (𝓓.mono (min_le_left u t))).sub
        ((hM.stronglyAdapted (min u s)).mono (𝓓.mono (min_le_left u s)))).indicator
          (𝓓.mono hsu _ hA)
    · have he : X u = 0 := by
        funext ω
        simp [X, min_eq_left (lt_of_not_ge hsu).le,
          min_eq_left ((lt_of_not_ge hsu).le.trans hst)]
      rw [he]
      exact stronglyMeasurable_zero
  · filter_upwards [hMc] with ω hc
    by_cases hω : ω ∈ A
    · simpa only [X, indicator_of_mem hω, Pi.sub_apply, Pi.sub_def,
        Function.comp_def, id_eq] using
        (hc.comp (continuous_id.min continuous_const)).sub
          (hc.comp (continuous_id.min continuous_const))
    · simpa only [X, indicator_of_notMem hω] using
        (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ)))
  · by_cases hsu : s ≤ u
    · apply EventuallyEq.symm
      apply (condExp_indicator ((hM.integrable t).sub (hM.integrable s))
        (𝓓.mono hsu _ hA)).trans
      filter_upwards [condExp_sub (hM.integrable t) (hM.integrable s) (𝓓 u),
        condExp_martingale_eq_min hM t u, condExp_martingale_eq_min hM s u] with ω h1 h2 h3
      by_cases hω : ω ∈ A
      · simp only [X, indicator_of_mem hω, Pi.sub_apply, h1, h2, h3]
      · simp only [X, indicator_of_notMem hω]
    · have hus : u ≤ s := (lt_of_not_ge hsu).le
      have he : P[A.indicator (M t - M s) | 𝓓 u] =ᵐ[P] 0 :=
        (condExp_condExp_of_le (𝓓.mono hus) (𝓓.le s)).symm.trans
          ((condExp_congr_ae hzero).trans (EventuallyEq.of_eq condExp_zero))
      refine (EventuallyEq.of_eq ?_).trans he.symm
      funext ω
      simp [X, min_eq_left hus, min_eq_left (hus.trans hst)]

end InteractingSLE.WFS
