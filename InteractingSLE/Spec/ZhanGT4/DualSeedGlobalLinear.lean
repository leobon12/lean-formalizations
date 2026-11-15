/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Finite

/-!
# Linearity and the unit coefficient for the chosen stochastic integral

Packet PROVE-ZHAN-GT4-A22. These identities refer to the original chosen
Riemann integral and will splice the mapped noise with its Brownian
continuation after the protected horizon.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w v : ℝ≥0 → Ω → ℝ}

/-- Additivity of the actual chosen integral of bounded adapted regular coefficients. -/
theorem seed_stochIntegral_add (hB : IsFilteredPreBrownian B 𝓕 P)
    (hw : StronglyAdapted 𝓕 w) (hv : StronglyAdapted 𝓕 v) {Cw Cv : ℝ}
    (hbw : ∀ u ω, |w u ω| ≤ Cw) (hbv : ∀ u ω, |v u ω| ≤ Cv)
    (hrw : IsRiemannRegular P w) (hrv : IsRiemannRegular P v) (t : ℝ≥0) :
    stochIntegral P 𝓕 B (fun u ω => w u ω + v u ω) t =ᵐ[P]
      fun ω => stochIntegral P 𝓕 B w t ω + stochIntegral P 𝓕 B v t ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : StronglyAdapted 𝓕 (fun u ω => w u ω + v u ω) := fun u => (hw u).add (hv u)
  have hb (u : ℝ≥0) (ω : Ω) : |w u ω + v u ω| ≤ Cw + Cv :=
    (abs_add_le _ _).trans (add_le_add (hbw u ω) (hbv u ω))
  have hr : IsRiemannRegular P (fun u ω => w u ω + v u ω) := by
    filter_upwards [hrw, hrv] with ω hω hω'
    filter_upwards [hω, hω'] with u hu hu'
    exact hu.add hu'
  obtain ⟨a, ha, hI⟩ := (tendstoInMeasure_riemannSum hB hw hbw hrw t).exists_seq_tendsto_ae
  obtain ⟨b, hb', hJ⟩ :=
    ((tendstoInMeasure_riemannSum hB hv hbv hrv t).comp ha.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨c, hc, hK⟩ := ((tendstoInMeasure_riemannSum hB hm hb hr t).comp
    (ha.tendsto_atTop.comp hb'.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hI, hJ, hK] with ω hi hj hk
  have he (n : ℕ) : riemannSum B (fun u ω => w u ω + v u ω) n t ω =
      riemannSum B w n t ω + riemannSum B v n t ω := by
    simp only [riemannSum, add_mul, Finset.sum_add_distrib]
  simp only [Function.comp_def, he] at hk
  exact tendsto_nhds_unique hk
    ((hi.comp (hb'.tendsto_atTop.comp hc.tendsto_atTop)).add (hj.comp hc.tendsto_atTop))

/-- The dyadic sum of the unit coefficient telescopes exactly once its grid covers `t`. -/
theorem seed_riemannSum_one (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0)
    (ht : t ≤ n) (ω : Ω) : riemannSum B (fun _ _ => 1) n t ω = B t ω - B 0 ω := by
  simp only [riemannSum, one_mul]
  rw [Finset.sum_range_sub (fun k => B (min (grid n k) t) ω), grid_cells,
    min_eq_right ht, grid_zero, zero_min]

/-- Integrating one recovers the Brownian increment for the actual chosen version. -/
theorem seed_stochIntegral_one (hB : IsFilteredPreBrownian B 𝓕 P) (t : ℝ≥0) :
    stochIntegral P 𝓕 B (fun _ _ => 1) t =ᵐ[P] fun ω => B t ω - B 0 ω := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm : StronglyAdapted 𝓕 (fun _ _ => (1 : ℝ)) := fun _ => stronglyMeasurable_const
  have hb : ∀ (u : ℝ≥0) (ω : Ω), |(1 : ℝ)| ≤ 1 := fun _ _ => (abs_one : |(1 : ℝ)| = 1).le
  have hr : IsRiemannRegular P (fun _ _ => (1 : ℝ)) :=
    Eventually.of_forall fun _ => Eventually.of_forall fun _ => continuousWithinAt_const
  obtain ⟨a, ha, hI⟩ := (tendstoInMeasure_riemannSum hB hm hb hr t).exists_seq_tendsto_ae
  filter_upwards [hI] with ω hi
  have ht : ∀ᶠ k in atTop, t ≤ (a k : ℝ≥0) :=
    (tendsto_natCast_atTop_atTop.comp ha.tendsto_atTop).eventually (eventually_ge_atTop t)
  have he : ∀ᶠ k in atTop, riemannSum B (fun _ _ => 1) (a k) t ω = B t ω - B 0 ω :=
    ht.mono fun k hk => seed_riemannSum_one B (a k) t hk ω
  exact tendsto_nhds_unique hi ((tendsto_congr' he).2 tendsto_const_nhds)

end InteractingSLE.ZhanGT4
