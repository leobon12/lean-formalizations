/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndWindowIntegral

/-!
# A single random endpoint does not change the chosen integral

Packet PROVE-ZHAN-GT4-A22. Strict and inclusive stopped coefficients
can differ at the stopping time. On every grid there is at most one
nonzero cell starting there; its Brownian increment tends to zero.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {B w v : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}

/-- Pathwise Riemann sums ignore a coefficient change at one random time. -/
theorem tendsto_seed_endpoint_error {Cw Cv : ℝ}
    (hbw : ∀ u ω, |w u ω| ≤ Cw) (hbv : ∀ u ω, |v u ω| ≤ Cv)
    (heq : ∀ ω u, u ≠ S ω → w u ω = v u ω)
    (hBc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => riemannSum B w n t ω - riemannSum B v n t ω) atTop (𝓝 0) := by
  let K := |Cw| + |Cv| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hBr : Continuous (fun r : ℝ => B r.toNNReal ω) := (hBc ω).comp continuous_real_toNNReal
  apply Metric.tendsto_nhds.2
  intro η hη
  obtain ⟨δ, hδ, hBu⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hBr.continuousOn (s := Icc (0 : ℝ) t))) (η / (2 * K)) (by positivity)
  have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  filter_upwards [hmesh.eventually_lt_const hδ] with n hn
  let p : ℕ → ℝ≥0 := fun k => min (grid n k) t
  have hp : Monotone p := fun k j hkj => min_le_min_right t (grid_mono n hkj)
  have hm (k : ℕ) : (p k : ℝ) ∈ Icc (0 : ℝ) t := ⟨(p k).coe_nonneg, min_le_right _ _⟩
  have hinc (k : ℕ) : |B (p (k + 1)) ω - B (p k) ω| ≤ η / (2 * K) := by
    have hd : dist (p (k + 1) : ℝ) (p k : ℝ) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2
        (show (p k : ℝ) ≤ p (k + 1) from hp (Nat.le_succ k)))]
      exact (seed_grid_sub_le n k t).trans_lt hn
    simpa only [Real.toNNReal_coe, Real.dist_eq] using
      (hBu _ (hm (k + 1)) _ (hm k) hd).le
  have hcell (k : ℕ) : |(w (p k) ω - v (p k) ω) * (B (p (k + 1)) ω - B (p k) ω)| ≤
      if p k = S ω ∧ p k < p (k + 1) then η / 2 else 0 := by
    split_ifs with hk
    · have hc : |w (p k) ω - v (p k) ω| ≤ K :=
        (abs_sub _ _).trans ((add_le_add (hbw _ _) (hbv _ _)).trans (by
          dsimp only [K]; linarith only [le_abs_self Cw, le_abs_self Cv]))
      rw [abs_mul]
      calc _ ≤ K * (η / (2 * K)) := mul_le_mul hc (hinc k) (abs_nonneg _) hK.le
        _ = η / 2 := by field_simp
    · by_cases he : p k = S ω
      · have hp' : p (k + 1) = p k := le_antisymm
          (le_of_not_gt (fun hl => hk ⟨he, hl⟩)) (hp (Nat.le_succ k))
        simp only [hp', sub_self, mul_zero, abs_zero, le_refl]
      · simp only [heq ω _ he, sub_self, zero_mul, abs_zero, le_refl]
  have huniq {k j : ℕ} (hk : p k = S ω ∧ p k < p (k + 1))
      (hj : p j = S ω ∧ p j < p (j + 1)) : k = j := by
    apply le_antisymm
    · by_contra hh
      have hl := hp (Nat.succ_le_of_lt (lt_of_not_ge hh))
      rw [hk.1] at hl
      exact (not_lt_of_ge hl) (hj.1 ▸ hj.2)
    · by_contra hh
      have hl := hp (Nat.succ_le_of_lt (lt_of_not_ge hh))
      rw [hj.1] at hl
      exact (not_lt_of_ge hl) (hk.1 ▸ hk.2)
  rw [Real.dist_eq, sub_zero, seed_riemannSum_clamped, seed_riemannSum_clamped,
    ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ Finset.range (cells n),
        |(w (p k) ω - v (p k) ω) * (B (p (k + 1)) ω - B (p k) ω)| := by
          simpa only [sub_mul] using Finset.abs_sum_le_sum_abs
            (fun k => (w (p k) ω - v (p k) ω) * (B (p (k + 1)) ω - B (p k) ω)) (Finset.range (cells n))
    _ ≤ ∑ k ∈ Finset.range (cells n),
        if p k = S ω ∧ p k < p (k + 1) then η / 2 else 0 := Finset.sum_le_sum fun k _ => hcell k
    _ ≤ η / 2 := Ito.sum_ite_le_of_unique (by positivity) (fun _ _ _ => le_rfl)
      (fun _ _ hk hj => huniq hk hj)
    _ < η := half_lt_self hη

/-- The actual chosen integrals agree when bounded Riemann-regular
adapted coefficients differ only at one pathwise time. -/
theorem seed_stochIntegral_eq_of_endpoint {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (hB : IsFilteredPreBrownian B 𝓕 P)
    (hBc : ∀ ω, Continuous (B · ω)) (hw : StronglyAdapted 𝓕 w) (hv : StronglyAdapted 𝓕 v)
    {Cw Cv : ℝ} (hbw : ∀ u ω, |w u ω| ≤ Cw) (hbv : ∀ u ω, |v u ω| ≤ Cv)
    (hrw : IsRiemannRegular P w) (hrv : IsRiemannRegular P v)
    (heq : ∀ ω u, u ≠ S ω → w u ω = v u ω) (t : ℝ≥0) :
    stochIntegral P 𝓕 B w t =ᵐ[P] stochIntegral P 𝓕 B v t := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨a, ha, hI⟩ := (tendstoInMeasure_riemannSum hB hw hbw hrw t).exists_seq_tendsto_ae
  obtain ⟨b, hb, hJ⟩ :=
    ((tendstoInMeasure_riemannSum hB hv hbv hrv t).comp ha.tendsto_atTop).exists_seq_tendsto_ae
  filter_upwards [hI, hJ] with ω hi hj
  have he := tendsto_nhds_unique ((hi.comp hb.tendsto_atTop).sub hj)
    ((tendsto_seed_endpoint_error hbw hbv heq hBc t ω).comp
      (ha.tendsto_atTop.comp hb.tendsto_atTop))
  exact sub_eq_zero.1 he

end InteractingSLE.ZhanGT4
