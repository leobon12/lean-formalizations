/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalLocal

/-!
# The chosen integral of a stopping indicator

Packet PROVE-ZHAN-GT4-A22. The finite dyadic sum differs from the stopped
Brownian increment only in its crossing cell. Reuse the existing crossing
remainder estimate, allowing the cutoff to depend on the sample.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}

/-- The strict stopping coefficient is adapted, bounded, and Riemann regular. -/
theorem seed_stop_one_facts (P : Measure Ω)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    StronglyAdapted 𝓕 (cutRate S (fun _ _ => 1)) ∧
      (∀ u ω, |cutRate S (fun _ _ => 1) u ω| ≤ 1) ∧
      IsRiemannRegular P (cutRate S (fun _ _ => 1)) := by
  refine ⟨?_, ?_, seed_isRiemannRegular_cutRate (fun _ => continuousOn_const)⟩
  · intro u
    exact (measurable_cutRate hS (fun v => measurable_const.indicator
      (by simpa only [WithTop.coe_le_coe] using hS.measurableSet_ge v)) u).stronglyMeasurable
  · intro u ω
    unfold cutRate
    split_ifs <;> norm_num

/-- The stopping-indicator sums converge pathwise to the stopped increment. -/
theorem tendsto_seed_riemannSum_stop_one (hBc : ∀ ω, Continuous (B · ω))
    (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => riemannSum B (cutRate S (fun _ _ => 1)) n t ω) atTop
      (𝓝 (B (min t (S ω)) ω - B 0 ω)) := by
  have hnat : ∀ᶠ n : ℕ in atTop, t ≤ (n : ℝ≥0) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop t)
  by_cases hSt : S ω ≤ t
  · rw [min_eq_right hSt]
    have hh := tendsto_seedEndWindow_error
      (c := fun _ _ => (1 : ℝ)) (C := 1) (fun _ _ => by norm_num) hBc hSt ω
    have hsum (n : ℕ) : riemannSum B (cutRate S (fun _ _ => 1)) n t ω +
        riemannSum B (seedEndWindow (S ω) (fun _ _ => 1)) n t ω =
        riemannSum B (fun _ _ => 1) n t ω := by
      simp only [riemannSum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : grid n k < S ω
      · simp only [cutRate, hk, ite_true, seedEndWindow, not_le_of_gt hk, ite_false,
          one_mul, zero_mul, add_zero]
      · simp only [cutRate, hk, ite_false, seedEndWindow, le_of_not_gt hk, ite_true,
          one_mul, zero_mul, zero_add]
    have he : ∀ᶠ n in atTop, riemannSum B (cutRate S (fun _ _ => 1)) n t ω =
        (B (S ω) ω - B 0 ω) + (riemannSum B (fun _ _ => 1) n t ω -
          riemannSum B (fun _ _ => 1) n (S ω) ω -
          riemannSum B (seedEndWindow (S ω) (fun _ _ => 1)) n t ω) := by
      filter_upwards [hnat] with n hn
      rw [seed_riemannSum_one B n (S ω) (hSt.trans hn)]
      linarith only [hsum n]
    exact (tendsto_congr' he).2 (by simpa only [add_zero] using tendsto_const_nhds.add hh)
  · have htS : t < S ω := lt_of_not_ge hSt
    rw [min_eq_left htS.le]
    have he : ∀ᶠ n in atTop, riemannSum B (cutRate S (fun _ _ => 1)) n t ω = B t ω - B 0 ω := by
      filter_upwards [hnat] with n hn
      have hsum : riemannSum B (cutRate S (fun _ _ => 1)) n t ω =
          riemannSum B (fun _ _ => 1) n t ω := by
        rw [seed_riemannSum_clamped, seed_riemannSum_clamped]
        apply Finset.sum_congr rfl
        intro k _
        simp only [cutRate, (min_le_right (grid n k) t).trans_lt htS, ite_true]
      rw [hsum, seed_riemannSum_one B n t hn]
    exact (tendsto_congr' he).2 tendsto_const_nhds

/-- The original chosen integral of the stopping indicator is the stopped Brownian increment. -/
theorem seed_stochIntegral_stop_one (hB : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    stochIntegral P 𝓕 B (cutRate S (fun _ _ => 1)) t =ᵐ[P]
      fun ω => B (min t (S ω)) ω - B 0 ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hm, hb, hr⟩ := seed_stop_one_facts P hS
  obtain ⟨a, ha, hI⟩ := (tendstoInMeasure_riemannSum hB hm hb hr t).exists_seq_tendsto_ae
  filter_upwards [hI] with ω hi
  exact tendsto_nhds_unique hi ((tendsto_seed_riemannSum_stop_one hBc t ω).comp ha.tendsto_atTop)

end InteractingSLE.ZhanGT4
