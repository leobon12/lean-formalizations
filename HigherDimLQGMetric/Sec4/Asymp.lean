import HigherDimLQGMetric.Sec4.Radii

/-!
# Asymptotic bookkeeping for [1] Lemma 4.4 (packet L9b)

Elementary eventual inequalities as `ε ↓ 0` (`L = log ε⁻¹ → ∞`): the localization radius `s(ε) = ε L^{10}` is
`≤ ε^{1-ζ/2}/24`, the grid mesh `ε` is `≪ ε^{1-ζ/2}`, and a counting lemma for the shell decoupling.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

theorem l9b_rpow_neg_half {ε ζ : ℝ} (hε : 0 < ε) :
    ε ^ (-(ζ / 2)) = Real.exp (ζ / 2 * Real.log ε⁻¹) := by
  rw [Real.rpow_def_of_pos hε, Real.log_inv]
  ring_nf

theorem l9b_rpow_one_sub_half {ε ζ : ℝ} (hε : 0 < ε) :
    ε ^ (1 - ζ / 2) = ε * ε ^ (-(ζ / 2)) := by
  rw [show 1 - ζ / 2 = 1 + -(ζ / 2) by ring, Real.rpow_add hε, Real.rpow_one]

theorem l9b_tendsto_rpow_neg_half {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun ε : ℝ => ε ^ (-(ζ / 2))) (𝓝[>] 0) atTop := by
  have h := Real.tendsto_exp_atTop.comp
    ((tendsto_log_inv_nhdsGT_zero).const_mul_atTop (by positivity : 0 < ζ / 2))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (l9b_rpow_neg_half hε).symm

/-- the mesh `K ε` is eventually below `ε^{1-ζ/2}` -/
theorem l9b_eventually_mesh {ζ : ℝ} (hζ : 0 < ζ) (K : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), K * ε < ε ^ (1 - ζ / 2) := by
  filter_upwards [self_mem_nhdsWithin, (l9b_tendsto_rpow_neg_half hζ).eventually
    (eventually_gt_atTop K)] with ε hε hK
  have hε0 : 0 < ε := hε
  rw [l9b_rpow_one_sub_half hε0]
  nlinarith

/-- the localization radius is eventually `≤ ε^{1-ζ/2}/24` -/
theorem l9b_eventually_locRad_small {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 24 * locRad ε ≤ ε ^ (1 - ζ / 2) := by
  have hx := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 10).comp
    ((tendsto_log_inv_nhdsGT_zero).const_mul_atTop (by positivity : 0 < ζ / 2))
  have hsmall := hx.eventually (gt_mem_nhds (show (0 : ℝ) < (ζ / 2) ^ 10 / 24 by positivity))
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hs
  have hε0 : 0 < ε := hε
  simp only [Function.comp_apply] at hs
  set L := Real.log ε⁻¹
  rw [l9b_rpow_one_sub_half hε0, l9b_rpow_neg_half hε0, locRad]
  have hpow : (ζ / 2 * L) ^ 10 = (ζ / 2) ^ 10 * L ^ 10 := mul_pow _ _ _
  rw [hpow] at hs
  have hE := Real.exp_pos (ζ / 2 * L)
  have hs' : (ζ / 2) ^ 10 * L ^ 10 / Real.exp (ζ / 2 * L) < (ζ / 2) ^ 10 / 24 := by
    rwa [Real.exp_neg, ← div_eq_mul_inv] at hs
  have h1 : (ζ / 2) ^ 10 * L ^ 10 < (ζ / 2) ^ 10 / 24 * Real.exp (ζ / 2 * L) :=
    (div_lt_iff₀ hE).1 hs'
  have h2 : 24 * L ^ 10 < Real.exp (ζ / 2 * L) := by
    have hz : 0 < (ζ / 2) ^ 10 := by positivity
    have := (mul_lt_mul_iff_right₀ hz).1 (show (ζ / 2) ^ 10 * (24 * L ^ 10) <
      (ζ / 2) ^ 10 * Real.exp (ζ / 2 * L) by nlinarith)
    exact this
  nlinarith

/-- **counting**: indices `i < n` with `k₀ + i ∉ R`, for `R ⊆ [k₀, k₀ + n)` with `n ≤ 10 |R|`, number fewer than
`(19/20) n` -/
theorem l9b_card_lt {n k₀ : ℕ} {R : Finset ℕ} (hR : R ⊆ Finset.Ico k₀ (k₀ + n))
    (hcard : n ≤ 10 * R.card) (hn : 0 < n) (S : Finset ℕ) (hS : ∀ i ∈ S, i < n ∧ k₀ + i ∉ R) :
    (S.card : ℝ) < 19 / 20 * n := by
  classical
  set T := R.image (fun k => k - k₀)
  have hTcard : T.card = R.card := by
    refine Finset.card_image_of_injOn fun a ha b hb hab => ?_
    have ha' := (Finset.mem_Ico.1 (hR ha)).1
    have hb' := (Finset.mem_Ico.1 (hR hb)).1
    omega
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hiT
    have hk0 := (Finset.mem_Ico.1 (hR hk)).1
    exact (hS _ hiS).2 (by rwa [Nat.add_sub_cancel' hk0])
  have hsub : S ∪ T ⊆ Finset.range n := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · exact Finset.mem_range.2 (hS i hi).1
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
      have := Finset.mem_Ico.1 (hR hk)
      exact Finset.mem_range.2 (by omega)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_range, hTcard] at hle
  have h1 : (S.card : ℝ) + R.card ≤ n := by exact_mod_cast hle
  have h2 : (n : ℝ) ≤ 10 * R.card := by exact_mod_cast hcard
  have h3 : (0 : ℝ) < n := by exact_mod_cast hn
  linarith

end HigherDimLQGMetric
