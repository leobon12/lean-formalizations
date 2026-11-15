/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandTaylor
import InteractingSLE.Spec.ZhanGT4.DualSeedBandCrossing
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalIto

/-!
# Pasting the actual logarithmic field through a stopping boundary

Packet PROVE-ZHAN-GT4-A22. Work on the clamped partitions of the actual
stochastic integral. The moving-tube modulus handles all regular cells
simultaneously; the unique stopping-boundary cell vanishes by continuity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
  {Φ Φ₁ Φ₂ Φ₃ Ψ : ℝ → Ω → ℝ → ℝ} {S : Ω → ℝ≥0}

/-- Only continuity along the path is needed for the compensated field's
increments; no off-tube extension of its actual generator is assumed. -/
theorem seed_fieldStopped_sub_of_le {a b : ℝ≥0} {ω : Ω} (hab : a ≤ b) (hbS : b ≤ S ω)
    (hg : ContinuousOn (fun u => Ito.fieldGen Φ₂ Ψ B u ω) (Icc 0 (S ω : ℝ))) :
    Ito.fieldStopped Φ Φ₂ Ψ B S 0 b ω - Ito.fieldStopped Φ Φ₂ Ψ B S 0 a ω =
      Φ b ω (B b ω) - Φ a ω (B a ω) -
        ∫ u in (a : ℝ)..b, Ito.fieldGen Φ₂ Ψ B u ω := by
  have hi₁ := (hg.mono (Icc_subset_Icc_right (show (b : ℝ) ≤ S ω from hbS)))
    |>.intervalIntegrable_of_Icc b.coe_nonneg (μ := volume)
  have hi₂ := (hg.mono (Icc_subset_Icc_right (show (a : ℝ) ≤ S ω from hab.trans hbS)))
    |>.intervalIntegrable_of_Icc a.coe_nonneg (μ := volume)
  have hh := intervalIntegral.integral_interval_sub_left hi₁ hi₂
  unfold Ito.fieldStopped
  rw [min_eq_left hbS, min_eq_left (hab.trans hbS)]
  rw [← hh]
  ring

/-- Full pathwise band pasting on the actual stochastic-integral grid.
The hypotheses concern the regular field and bounded coefficients, not
an assumed Taylor-error estimate or an assumed stochastic identity. -/
theorem seed_stopped_field_taylor_bound (t : ℝ≥0) (ω : Ω) {ρ K : ℝ}
    (hρ : 0 < ρ) (hK : 0 ≤ K) (hB : Continuous (B · ω))
    (hX : Continuous (Ito.fieldStopped Φ Φ₂ Ψ B S 0 · ω))
    (hloc : ∀ a b y : ℝ, 0 ≤ a → a ≤ b → b ≤ S ω →
      (∀ u ∈ Icc a b, |B u.toNNReal ω - y| < ρ) →
      IsLogField (fun u x => Φ u ω x) (fun u x => Φ₁ u ω x) (fun u x => Φ₂ u ω x)
        (fun u x => Φ₃ u ω x) (fun u x => Ψ u ω x) a b y ρ K)
    (hΨ : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2)
      (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ)))
    (hΦ : ContinuousOn (fun p : ℝ × ℝ => Φ₂ p.1 ω p.2)
      (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ)))
    (h₁ : ∀ u ≤ t, |Ito.stopCoef Φ₁ B S u ω| ≤ K)
    (h₂ : ∀ u ≤ t, |Ito.stopCoef Φ₂ B S u ω| ≤ K) :
    ∃ (C : ℝ) (R : ℕ → ℝ), Tendsto R atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      |seedDyadicDefect (Ito.fieldStopped Φ Φ₂ Ψ B S 0)
        (Ito.stopCoef Φ₁ B S) (Ito.stopCoef Φ₂ B S) B n t ω| ≤
          C * seedCubicError B n t ω + R n := by
  let β : ℝ → ℝ := fun u => B u.toNNReal ω
  have hβ : ContinuousOn β (Icc 0 (S ω : ℝ)) :=
    (hB.comp continuous_real_toNNReal).continuousOn
  have hm : MapsTo (fun u => (u, β u)) (Icc 0 (S ω : ℝ))
      (seedPathTube β 0 (S ω) (3 * ρ)) := fun u hu =>
    ⟨hu, by simp only [sub_self, abs_zero]; positivity⟩
  have hg : ContinuousOn (fun u => Ito.fieldGen Φ₂ Ψ B u ω) (Icc 0 (S ω : ℝ)) :=
    (hΨ.comp (continuousOn_id.prodMk hβ) hm).add
      (continuousOn_const.mul (hΦ.comp (continuousOn_id.prodMk hβ) hm))
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_bound_cutChi_uniform ρ
  let C := 8 * Cχ * K
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let R : ℕ → ℝ := fun n => seedBandRemainder (fun u x => Ψ u ω x)
    (fun u x => Φ₂ u ω x) β (S ω) t n +
      seedCrossingRemainder (Ito.fieldStopped Φ Φ₂ Ψ B S 0)
        (Ito.stopCoef Φ₁ B S) (Ito.stopCoef Φ₂ B S) B (S ω) t ω n
  refine ⟨C, R, ?_, ?_⟩
  · simpa only [add_zero] using (tendsto_seedBandRemainder (S ω) t hρ hβ hΨ hΦ).add
      (tendsto_seedCrossingRemainder (S ω) t ω hX hB hK h₁ h₂)
  · obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hβ) ρ hρ
    have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    filter_upwards [hmesh.eventually_lt_const hδ] with n hn
    let p : ℕ → ℝ≥0 := fun k => min (grid n k) t
    have hp : Monotone p := fun k j hkj => min_le_min_right t (grid_mono n hkj)
    let E : ℕ → ℝ := fun k => Ito.itoDefect (Ito.fieldStopped Φ Φ₂ Ψ B S 0)
      (Ito.stopCoef Φ₁ B S) (Ito.stopCoef Φ₂ B S) B (p k) (p (k + 1)) ω
    have he (k : ℕ) : |E k| ≤ C * |B (p (k + 1)) ω - B (p k) ω| ^ 3 +
        (if p k < S ω ∧ p (k + 1) ≤ S ω then
          Ito.fieldStepRem (fun u x => Ψ u ω x) (fun u x => Φ₂ u ω x) β (p k) (p (k + 1)) else 0) +
        (if p k < S ω ∧ S ω < p (k + 1) then |E k| else 0) := by
      by_cases ha : p k < S ω
      · by_cases hb : p (k + 1) ≤ S ω
        · have hnear (u : ℝ) (hu : u ∈ Icc (p k : ℝ) (p (k + 1))) :
              |β u - B (p k) ω| < ρ := by
            have hd : dist u (p k : ℝ) < δ := by
              rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hu.1)]
              exact (sub_le_sub_right hu.2 _).trans_lt ((seed_grid_sub_le n k t).trans_lt hn)
            have hh := hosc u ⟨(p k).coe_nonneg.trans hu.1, hu.2.trans hb⟩
              (p k) ⟨(p k).coe_nonneg, ha.le⟩ hd
            simpa only [Real.dist_eq, β, Real.toNNReal_coe] using hh
          have hLF := hloc (p k) (p (k + 1)) (B (p k) ω) (p k).coe_nonneg
            (show (p k : ℝ) ≤ p (k + 1) from hp (Nat.le_succ k)) hb hnear
          have ht := hLF.seed_log_step_actual hCχ (hχ _) le_rfl
            (show (p k : ℝ) ≤ p (k + 1) from hp (Nat.le_succ k)) le_rfl
            (hβ.mono (Icc_subset_Icc (p k).coe_nonneg hb)) hnear
          have hi := seed_fieldStopped_sub_of_le (Φ := Φ) (hp (Nat.le_succ k)) hb hg
          simp only [β, Real.toNNReal_coe] at ht
          rw [ite_eq_left ⟨ha, hb⟩, ite_eq_right (fun hh => not_lt_of_ge hb hh.2), add_zero]
          dsimp only [E, Ito.itoDefect, Ito.stopCoef]
          rw [ite_eq_left ha, ite_eq_left ha, hi]
          exact ht
        · rw [ite_eq_right (fun hh => hb hh.2), ite_eq_left ⟨ha, lt_of_not_ge hb⟩]
          have hn0 : 0 ≤ C * |B (p (k + 1)) ω - B (p k) ω| ^ 3 := by positivity
          linarith only [hn0]
      · have hz := Ito.itoDefect_stopped_eq_zero_of_le (Φ := Φ) (Φ1 := Φ₁) (Φ2 := Φ₂)
          (Ψ := Ψ) (B := B) (s := 0) (hp (Nat.le_succ k)) (le_of_not_gt ha)
        rw [ite_eq_right (fun hh => ha hh.1), ite_eq_right (fun hh => ha hh.1)]
        change |E k| ≤ _
        rw [show E k = 0 from hz, abs_zero]
        positivity
    calc _ ≤ ∑ k ∈ Finset.range (cells n), |E k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (cells n),
          (C * |B (p (k + 1)) ω - B (p k) ω| ^ 3 +
            (if p k < S ω ∧ p (k + 1) ≤ S ω then
              Ito.fieldStepRem (fun u x => Ψ u ω x) (fun u x => Φ₂ u ω x) β (p k) (p (k + 1)) else 0) +
            (if p k < S ω ∧ S ω < p (k + 1) then |E k| else 0)) :=
        Finset.sum_le_sum (fun k _ => he k)
      _ = C * seedCubicError B n t ω + R n := by
        simp only [seedCubicError, R, seedBandRemainder, seedCrossingRemainder,
          Finset.sum_add_distrib, ← Finset.mul_sum, p, E, NNReal.coe_min]
        ring

end InteractingSLE.ZhanGT4
