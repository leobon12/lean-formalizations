/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndRemainder

/-!
# Band pasting on the original clock

Packet PROVE-ZHAN-GT4-A22. Regular cells are translated to the restarted
field. There are at most two exceptional cells, at the deterministic
restart and the stopping horizon; both errors vanish by continuity.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} {τ : Ω → ℝ≥0}
  {Φ Φ₁ Φ₂ Φ₃ Ψ : ℝ → Ω → ℝ → ℝ} {ρ K : ℝ}

/-- The actual restarted field has the required Taylor estimate on the
original Brownian grid, including the cell crossing the restart. -/
theorem SeedRegularBand.original_taylor_bound
    (h : SeedRegularBand (shiftBM B ε) τ Φ Φ₁ Φ₂ Φ₃ Ψ ρ K)
    (hBc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0) (ω : Ω) :
    ∃ (C : ℝ) (R : ℕ → ℝ), Tendsto R atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      |seedDyadicDefect (seedEndProcess ε (Ito.fieldStopped Φ Φ₂ Ψ (shiftBM B ε) τ 0))
        (seedEndCoef ε (Ito.stopCoef Φ₁ (shiftBM B ε) τ))
        (seedEndCoef ε (Ito.stopCoef Φ₂ (shiftBM B ε) τ)) B n t ω| ≤
          C * seedCubicError B n t ω + R n := by
  let B' := shiftBM B ε
  let X := seedEndProcess ε (Ito.fieldStopped Φ Φ₂ Ψ B' τ 0)
  let c₁ := seedEndCoef ε (Ito.stopCoef Φ₁ B' τ)
  let c₂ := seedEndCoef ε (Ito.stopCoef Φ₂ B' τ)
  let β : ℝ → ℝ := fun u => B' u.toNNReal ω
  have hB' : ∀ ω, Continuous (B' · ω) := fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hβ : ContinuousOn β (Icc 0 (τ ω : ℝ)) :=
    ((hB' ω).comp continuous_real_toNNReal).continuousOn
  have hX : Continuous (X · ω) := continuous_seedEndProcess ε ω (h.continuous_stopped hB' ω)
  have hc₁ (u : ℝ≥0) : |c₁ u ω| ≤ K :=
    abs_seedEndCoef_le h.bound_nonneg (fun u ω => (h.coef_bound ω u).1) ε u ω
  have hc₂ (u : ℝ≥0) : |c₂ u ω| ≤ K :=
    abs_seedEndCoef_le h.bound_nonneg (fun u ω => (h.coef_bound ω u).2) ε u ω
  have hm : MapsTo (fun u => (u, β u)) (Icc 0 (τ ω : ℝ)) (seedPathTube β 0 (τ ω) (3 * ρ)) :=
    fun u hu => ⟨hu, by simp only [sub_self, abs_zero]; linarith only [h.radius_pos]⟩
  have hg : ContinuousOn (fun u => Ito.fieldGen Φ₂ Ψ B' u ω) (Icc 0 (τ ω : ℝ)) :=
    ((h.contT ω).comp (continuousOn_id.prodMk hβ) hm).add
      (continuousOn_const.mul ((h.contXX ω).comp (continuousOn_id.prodMk hβ) hm))
  obtain ⟨Cχ, hCχ, hχ⟩ := exists_bound_cutChi_uniform ρ
  let C := 8 * Cχ * K
  have hC : 0 ≤ C := by dsimp only [C]; exact mul_nonneg (by positivity) h.bound_nonneg
  let R : ℕ → ℝ := fun n => seedEndRemainder (fun u x => Ψ u ω x) (fun u x => Φ₂ u ω x)
    β ε (τ ω) t n + seedCrossingRemainder X c₁ c₂ B ε t ω n +
      seedCrossingRemainder X c₁ c₂ B (ε + τ ω) t ω n
  refine ⟨C, R, ?_, ?_⟩
  · simpa only [add_zero] using
      ((tendsto_seedEndRemainder ε (τ ω) t h.radius_pos hβ (h.contT ω) (h.contXX ω)).add
        (tendsto_seedCrossingRemainder ε t ω hX (hBc ω) h.bound_nonneg
          (fun u _ => hc₁ u) (fun u _ => hc₂ u))).add
        (tendsto_seedCrossingRemainder (ε + τ ω) t ω hX (hBc ω) h.bound_nonneg
          (fun u _ => hc₁ u) (fun u _ => hc₂ u))
  · obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hβ) ρ h.radius_pos
    have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
    filter_upwards [hmesh.eventually_lt_const hδ] with n hn
    let p : ℕ → ℝ≥0 := fun k => min (grid n k) t
    have hp : Monotone p := fun k j hkj => min_le_min_right t (grid_mono n hkj)
    let E : ℕ → ℝ := fun k => Ito.itoDefect X c₁ c₂ B (p k) (p (k + 1)) ω
    have he (k : ℕ) : |E k| ≤ C * |B (p (k + 1)) ω - B (p k) ω| ^ 3 +
        (if ε ≤ p k ∧ p k < ε + τ ω ∧ p (k + 1) ≤ ε + τ ω then
          Ito.fieldStepRem (fun u x => Ψ u ω x) (fun u x => Φ₂ u ω x) β
            (p k - ε : ℝ≥0) (p (k + 1) - ε : ℝ≥0) else 0) +
        (if p k < ε ∧ ε < p (k + 1) then |E k| else 0) +
        (if p k < ε + τ ω ∧ ε + τ ω < p (k + 1) then |E k| else 0) := by
      have hcube : 0 ≤ C * |B (p (k + 1)) ω - B (p k) ω| ^ 3 := by positivity
      by_cases ha : ε ≤ p k
      · have hae : ε ≤ p (k + 1) := ha.trans (hp (Nat.le_succ k))
        have hab : p k - ε ≤ p (k + 1) - ε := tsub_le_tsub_right (hp (Nat.le_succ k)) ε
        have hlen : ((p (k + 1) - ε : ℝ≥0) : ℝ) - (p k - ε : ℝ≥0) =
            (p (k + 1) : ℝ) - p k := by
          rw [NNReal.coe_sub hae, NNReal.coe_sub ha]
          ring
        have hE : E k = Ito.itoDefect (Ito.fieldStopped Φ Φ₂ Ψ B' τ 0)
            (Ito.stopCoef Φ₁ B' τ) (Ito.stopCoef Φ₂ B' τ) B' (p k - ε) (p (k + 1) - ε) ω :=
          seedEnd_itoDefect_eq ha (hp (Nat.le_succ k)) ω
        by_cases haS : p k < ε + τ ω
        · by_cases hbS : p (k + 1) ≤ ε + τ ω
          · have hbτ : p (k + 1) - ε ≤ τ ω := tsub_le_iff_left.2 hbS
            have haτ : p k - ε < τ ω := by
              apply (add_lt_add_iff_left ε).1
              rwa [add_tsub_cancel_of_le ha]
            have hnear (u : ℝ) (hu : u ∈ Icc ((p k - ε : ℝ≥0) : ℝ) ((p (k + 1) - ε : ℝ≥0) : ℝ)) :
                |β u - B' (p k - ε) ω| < ρ := by
              have hd : dist u ((p k - ε : ℝ≥0) : ℝ) < δ := by
                rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hu.1)]
                exact (sub_le_sub_right hu.2 _).trans_lt (by
                  rw [hlen]; exact (seed_grid_sub_le n k t).trans_lt hn)
              simpa only [Real.dist_eq, β, Real.toNNReal_coe] using
                hosc u ⟨(p k - ε).coe_nonneg.trans hu.1, hu.2.trans hbτ⟩
                  ((p k - ε : ℝ≥0) : ℝ) ⟨(p k - ε).coe_nonneg, haτ.le⟩ hd
            have hl := h.local_field ω ((p k - ε : ℝ≥0) : ℝ) ((p (k + 1) - ε : ℝ≥0) : ℝ) (B' (p k - ε) ω)
              (p k - ε).coe_nonneg hab hbτ hnear
            have ht := hl.seed_log_step_actual (β := β)
              (a := ((p k - ε : ℝ≥0) : ℝ)) (z := ((p (k + 1) - ε : ℝ≥0) : ℝ))
              hCχ (hχ _) le_rfl hab le_rfl
              (hβ.mono (Icc_subset_Icc (p k - ε).coe_nonneg hbτ)) hnear
            have hi := seed_fieldStopped_sub_of_le (Φ := Φ) hab hbτ hg
            rw [ite_eq_left ⟨ha, haS, hbS⟩, ite_eq_right (fun hh => not_lt_of_ge ha hh.1),
              ite_eq_right (fun hh => not_lt_of_ge hbS hh.2), add_zero, add_zero, hE]
            dsimp only [Ito.itoDefect, Ito.stopCoef]
            rw [ite_eq_left haτ, ite_eq_left haτ, hi]
            simpa only [β, B', C, Ito.fieldGen, shiftBM, Real.toNNReal_coe,
              add_tsub_cancel_of_le ha, add_tsub_cancel_of_le hae, sub_sub_sub_cancel_right] using ht
          · rw [ite_eq_right (fun hh => hbS hh.2.2),
              ite_eq_right (fun hh => not_lt_of_ge ha hh.1), ite_eq_left ⟨haS, lt_of_not_ge hbS⟩]
            linarith only [hcube]
        · have haτ : τ ω ≤ p k - ε := by
            apply (add_le_add_iff_left ε).1
            rw [add_tsub_cancel_of_le ha]
            exact le_of_not_gt haS
          have hz := Ito.itoDefect_stopped_eq_zero_of_le (Φ := Φ) (Φ1 := Φ₁) (Φ2 := Φ₂)
            (Ψ := Ψ) (B := B') (s := 0) hab haτ
          simp only [NNReal.coe_zero] at hz
          rw [ite_eq_right (fun hh => haS hh.2.1), ite_eq_right (fun hh => not_lt_of_ge ha hh.1),
            ite_eq_right (fun hh => haS hh.1), hE, hz, abs_zero]
          linarith only [hcube]
      · rw [ite_eq_right (fun hh => ha hh.1)]
        by_cases hb : p (k + 1) ≤ ε
        · have hz : E k = 0 := seedEnd_itoDefect_eq_zero_before (hp (Nat.le_succ k)) hb ω
          have hbS : p (k + 1) ≤ ε + τ ω := hb.trans (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ τ ω from bot_le))
          rw [ite_eq_right (fun hh => not_lt_of_ge hb hh.2),
            ite_eq_right (fun hh => not_lt_of_ge hbS hh.2), hz, abs_zero]
          linarith only [hcube]
        · rw [ite_eq_left ⟨lt_of_not_ge ha, lt_of_not_ge hb⟩]
          have hh : 0 ≤ (if p k < ε + τ ω ∧ ε + τ ω < p (k + 1) then |E k| else 0) := by
            split_ifs <;> positivity
          linarith only [hcube, hh]
    calc _ ≤ ∑ k ∈ Finset.range (cells n), |E k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (cells n),
          (C * |B (p (k + 1)) ω - B (p k) ω| ^ 3 +
            (if ε ≤ p k ∧ p k < ε + τ ω ∧ p (k + 1) ≤ ε + τ ω then
              Ito.fieldStepRem (fun u x => Ψ u ω x) (fun u x => Φ₂ u ω x) β
                (p k - ε : ℝ≥0) (p (k + 1) - ε : ℝ≥0) else 0) +
            (if p k < ε ∧ ε < p (k + 1) then |E k| else 0) +
            (if p k < ε + τ ω ∧ ε + τ ω < p (k + 1) then |E k| else 0)) :=
        Finset.sum_le_sum (fun k _ => he k)
      _ = C * seedCubicError B n t ω + R n := by
        simp only [seedCubicError, R, seedEndRemainder, seedCrossingRemainder,
          Finset.sum_add_distrib, ← Finset.mul_sum, p, E]
        ring

end InteractingSLE.ZhanGT4
