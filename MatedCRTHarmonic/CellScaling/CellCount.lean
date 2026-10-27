import Mathlib
import MatedCRTHarmonic.CellScaling.Radial
import MatedCRTHarmonic.CellScaling.CellArea
import MatedCRTHarmonic.CellScaling.AreaGrowth

/-!
# the cell-count bound as printed: `#V_{G¹}(B_{R_{2^k}}(0)) ≤ 2^{(1+δ)k}` eventually, almost surely

Paper: the cell-count bound. The cited argument ([17] : unit-mass
cells and [16, Lemma A.3]) counts only the cells *contained* in the ball; cells *meeting* the ball may protrude
(the cell-counting argument, MINOR). We follow the cell-counting argument : with
`k' = k + ⌈δ₁k⌉`, a.s. for all large `k`
1. every unit cell meeting `B_{ρR_{k'}}(0)` has diameter `≤ R_{k'} 2^{-qk'}` (`UnitCellDiamEventually` at `k'`);
2. `R_k ≤ ρ R_{k'}`, `R_{k'} 2^{-qk'} ≤ R_k`, `2R_k ≤ R_{k'}` (the cone-radius asymptotic, `eventually_scale_shift`);
3. `μ_h(B_{R_{k'}}(0)) ≤ 2^{(1+δ₁)k'}` (the area-growth bound).
So every cell meeting `B_{R_k}(0)` lies in `B_{2R_k}(0) ⊆ B_{R_{k'}}(0)`, and unit mass with null overlaps
(`measure_biUnion_unitCell`) bounds their number by `2^{(1+δ₁)k'} ≤ 2^{(1+δ)k}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- **Scale shift** (the cell-counting argument (ii)): if `log₂ R_k / k → a > 0`, then with `k' = k + ⌈δ₁ k⌉` (where
`0 < δ₁ ≤ 1/4` and `a δ₁ ≤ q/2`), eventually `R_k ≤ ρ R_{k'}`, `R_{k'} (2^{-k'})^q ≤ R_k` and `2 R_k ≤ R_{k'}`. -/
theorem eventually_scale_shift {R : ℕ → ℝ} (hR : ∀ k, 0 < R k) {a : ℝ}
    (hlim : Tendsto (fun k : ℕ => Real.logb 2 (R k) / k) atTop (𝓝 a)) (ha : 0 < a)
    {ρ q δ₁ : ℝ} (hρ : 0 < ρ) (hq : 0 < q) (hδ₁ : 0 < δ₁) (hδ₁4 : δ₁ ≤ 1 / 4) (hδ₁q : a * δ₁ ≤ q / 2) :
    ∀ᶠ k : ℕ in atTop,
      R k ≤ ρ * R (k + ⌈δ₁ * k⌉₊) ∧
        R (k + ⌈δ₁ * k⌉₊) * ((2 : ℝ) ^ (-((k + ⌈δ₁ * k⌉₊ : ℕ) : ℝ))) ^ q ≤ R k ∧
        2 * R k ≤ R (k + ⌈δ₁ * k⌉₊) := by
  set θ : ℝ := min (a * δ₁ / 4) (q / 8) with hθ
  have hθpos : 0 < θ := lt_min (by positivity) (by positivity)
  have hθ1 : θ ≤ a * δ₁ / 4 := min_le_left _ _
  have hθ2 : θ ≤ q / 8 := min_le_right _ _
  set c₁ : ℝ := (a - θ) * δ₁ - 2 * θ with hc₁
  set c₂ : ℝ := q - (a + θ) * δ₁ - 2 * θ with hc₂
  have haθ : 0 ≤ a - θ := by nlinarith
  have hc₁pos : 0 < c₁ := by
    have : c₁ ≥ a * δ₁ * (1 / 2 - δ₁ / 4) := by nlinarith
    have : 0 < a * δ₁ * (1 / 2 - δ₁ / 4) := by
      apply mul_pos (mul_pos ha hδ₁); linarith
    linarith
  have hc₂pos : 0 < c₂ := by nlinarith
  set L : ℕ → ℝ := fun k => Real.logb 2 (R k) with hL
  -- eventual two-sided bounds on `L k / k`
  have hev : ∀ᶠ k : ℕ in atTop, L k / k ∈ Ioo (a - θ) (a + θ) :=
    hlim.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hev
  obtain ⟨K₁, hK₁⟩ := exists_nat_ge (max 1 (-Real.logb 2 ρ) / c₁)
  obtain ⟨K₂, hK₂⟩ := exists_nat_ge ((a + θ) / c₂)
  refine eventually_atTop.2 ⟨max (max K 1) (max K₁ K₂), fun k hk => ?_⟩
  have hkK : K ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkK₁ : (K₁ : ℝ) ≤ k := by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkK₂ : (K₂ : ℝ) ≤ k := by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  set j : ℕ := ⌈δ₁ * k⌉₊ with hj
  set k' : ℕ := k + j with hk'
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hj_lo : δ₁ * k ≤ (j : ℝ) := Nat.le_ceil _
  have hj_hi : (j : ℝ) < δ₁ * k + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk'_eq : (k' : ℝ) = k + j := by rw [hk']; push_cast; ring
  have hk'pos : (0 : ℝ) < k' := by rw [hk'_eq]; positivity
  have hb := hK k hkK
  have hb' := hK k' (le_trans hkK (by omega))
  have hLk_lo : (a - θ) * k < L k := (lt_div_iff₀ hkpos).1 hb.1
  have hLk_hi : L k < (a + θ) * k := (div_lt_iff₀ hkpos).1 hb.2
  have hLk'_lo : (a - θ) * k' < L k' := (lt_div_iff₀ hk'pos).1 hb'.1
  have hLk'_hi : L k' < (a + θ) * k' := (div_lt_iff₀ hk'pos).1 hb'.2
  -- the gap `L k' − L k`
  have hgap_lo : c₁ * k < L k' - L k := by
    have h1 : (a - θ) * (j : ℝ) ≥ (a - θ) * (δ₁ * k) := mul_le_mul_of_nonneg_left hj_lo haθ
    rw [hk'_eq] at hLk'_lo
    nlinarith
  have hgap_hi : L k' - L k < q * k := by
    have h1 : (a + θ) * (j : ℝ) ≤ (a + θ) * (δ₁ * k + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt hj_hi) (by linarith)
    have h2 : (a + θ) ≤ c₂ * k := by
      have := (div_le_iff₀ hc₂pos).1 (le_trans hK₂ hkK₂)
      linarith
    rw [hk'_eq] at hLk'_hi
    nlinarith
  have hc₁k : max 1 (-Real.logb 2 ρ) ≤ c₁ * k := by
    have := (div_le_iff₀ hc₁pos).1 (le_trans hK₁ hkK₁)
    linarith
  have hRk := hR k
  have hRk' := hR k'
  have h2 : (1 : ℝ) < 2 := by norm_num
  refine ⟨?_, ?_, ?_⟩
  · -- `R_k ≤ ρ R_{k'}`
    rw [← Real.logb_le_logb h2 hRk (mul_pos hρ hRk'), Real.logb_mul (ne_of_gt hρ) (ne_of_gt hRk')]
    have := le_max_right 1 (-Real.logb 2 ρ)
    change L k ≤ Real.logb 2 ρ + L k'
    linarith
  · -- `R_{k'} (2^{-k'})^q ≤ R_k`
    have hpow : ((2 : ℝ) ^ (-(k' : ℝ))) ^ q = (2 : ℝ) ^ (-(k' : ℝ) * q) := by
      rw [← Real.rpow_mul (by norm_num)]
    rw [hpow]
    have hp : (0 : ℝ) < (2 : ℝ) ^ (-(k' : ℝ) * q) := by positivity
    rw [← Real.logb_le_logb h2 (mul_pos hRk' hp) hRk, Real.logb_mul (ne_of_gt hRk') (ne_of_gt hp),
      Real.logb_rpow (by norm_num) (by norm_num)]
    change L k' + -(k' : ℝ) * q ≤ L k
    have : q * (k : ℝ) ≤ q * k' := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hq)
      rw [hk'_eq]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    nlinarith
  · -- `2 R_k ≤ R_{k'}`
    rw [← Real.logb_le_logb h2 (mul_pos (by norm_num) hRk) hRk', Real.logb_mul (by norm_num) (ne_of_gt hRk),
      Real.logb_self_eq_one h2]
    have := le_max_left 1 (-Real.logb 2 ρ)
    change 1 + L k ≤ L k'
    linarith

/-- The exponent bookkeeping of the cell-counting argument: `(1 + δ₁) k' ≤ (1 + δ) k` eventually when `δ₁ ≤ δ/4`, `δ₁ ≤ 1/4`. -/
theorem eventually_exponent_le {δ δ₁ : ℝ} (hδ : 0 < δ) (hδ₁ : 0 < δ₁) (hδ₁δ : δ₁ ≤ δ / 4)
    (hδ₁4 : δ₁ ≤ 1 / 4) :
    ∀ᶠ k : ℕ in atTop, (1 + δ₁) * ((k + ⌈δ₁ * k⌉₊ : ℕ) : ℝ) ≤ (1 + δ) * k := by
  obtain ⟨K, hK⟩ := exists_nat_ge ((1 + δ₁) / (δ - 2 * δ₁ - δ₁ ^ 2))
  have hpos : 0 < δ - 2 * δ₁ - δ₁ ^ 2 := by nlinarith
  refine eventually_atTop.2 ⟨K, fun k hk => ?_⟩
  have hkK : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hj : (⌈δ₁ * k⌉₊ : ℝ) < δ₁ * k + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (1 + δ₁) ≤ (δ - 2 * δ₁ - δ₁ ^ 2) * k := by
    have := (div_le_iff₀ hpos).1 (le_trans hK hkK)
    linarith
  push_cast
  nlinarith

/-- **the cell-count bound as printed** , in the exact form `MesoModel.MatedCRTProposition25CellCountInput`
used in the mesoscopic construction: for the SLE/LQG cone realization, from the area parameterization, the area scaling law, the
GMC moment ([16, Lemma A.3]) and the eventual unit-cell diameter bound. -/
theorem matedCRTProposition25CellCountInput_of_cone {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ}
    (D : ConeRealization M) (hpar : AreaParametrization D) (hscale : AreaScalingLaw D)
    (hmom : AreaBallMoment D) (hdiam : UnitCellDiamEventually M) :
    MesoModel.MatedCRTProposition25CellCountInput M := by
  intro δ hδ
  have hγ := M.hγ
  set a := radiusExponent γ with ha_def
  have ha : 0 < a := by
    rw [ha_def, radiusExponent]
    have : γ ^ 2 < 4 := by nlinarith [hγ.1, hγ.2]
    exact one_div_pos.2 (by linarith)
  have hq : 0 < M.q := M.hq.1
  have hρ0 : 0 < M.ρ := M.hρ.1
  set δ₁ : ℝ := min (min δ 1 / 4) (M.q / (2 * a)) with hδ₁_def
  have hmin : 0 < min δ 1 := lt_min hδ one_pos
  have hδ₁pos : 0 < δ₁ := lt_min (by positivity) (by positivity)
  have hδ₁4 : δ₁ ≤ 1 / 4 :=
    le_trans (min_le_left _ _) (by have := min_le_right δ 1; linarith)
  have hδ₁δ : δ₁ ≤ δ / 4 :=
    le_trans (min_le_left _ _) (by have := min_le_left δ 1; linarith)
  have hδ₁q : a * δ₁ ≤ M.q / 2 := by
    have h1 : δ₁ ≤ M.q / (2 * a) := min_le_right _ _
    calc a * δ₁ ≤ a * (M.q / (2 * a)) := mul_le_mul_of_nonneg_left h1 (le_of_lt ha)
      _ = M.q / 2 := by field_simp
  have h24 := ae_tendsto_logb_coneScale hγ.1 hγ.2 D.B D.brownian'
  have hA := ae_eventually_area_ball_le hγ.1 hγ.2 D hscale hmom hδ₁pos
  filter_upwards [h24, hA, hdiam, hpar, D.radius_eq, D.cell_eq] with ω h24ω hAω hdiamω hparω hradω hcellω
  have hRlim : Tendsto (fun k : ℕ => Real.logb 2 (M.radius ω k) / k) atTop (𝓝 a) := by
    have hfun : (fun k : ℕ => Real.logb 2 (M.radius ω k) / k) =
        (fun k : ℕ => Real.logb 2 (coneScale γ γ (fun t => D.B t ω) (fun t => D.B' t ω) (2 ^ k)) / k) := by
      funext k
      rw [hradω k]
    rw [hfun]
    exact h24ω
  have hshift := eventually_scale_shift (M.radius_pos ω) hRlim ha hρ0 hq hδ₁pos hδ₁4 hδ₁q
  have hexp := eventually_exponent_le hδ hδ₁pos hδ₁δ hδ₁4
  have hk'_tend : Tendsto (fun k : ℕ => k + ⌈δ₁ * k⌉₊) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right k _) tendsto_id
  have hdiam' := hk'_tend.eventually hdiamω
  have hA' := hk'_tend.eventually hAω
  have hcellfun : (M.unitEmbedding ω).cell = fun x : ℤ => D.curve ω '' Icc ((x : ℝ) - 1) x := by
    funext x
    rw [M.unitEmbedding_cell ω]
    exact hcellω x
  have hmass : ∀ F : Finset ℤ, D.area ω (⋃ x ∈ F, (M.unitEmbedding ω).cell x) = F.card := by
    intro F
    rw [hcellfun]
    exact measure_biUnion_unitCell hparω.2 F
  filter_upwards [hshift, hexp, hdiam', hA'] with k hsk hek hdk hak
  obtain ⟨h1, h2, h3⟩ := hsk
  have hsub : ∀ x, ((M.unitEmbedding ω).cell x ∩ ball 0 (M.radius ω k)).Nonempty →
      (M.unitEmbedding ω).cell x ⊆ ball 0 (M.radius ω (k + ⌈δ₁ * k⌉₊)) := by
    rintro x ⟨p, hpJ, hpB⟩
    have hmeet : ((M.unitEmbedding ω).cell x ∩ ball 0 (M.ρ * M.radius ω (k + ⌈δ₁ * k⌉₊))).Nonempty :=
      ⟨p, hpJ, ball_subset_ball h1 hpB⟩
    have hd := le_trans (hdk x hmeet) h2
    have hbdd := ((M.unitEmbedding ω).isCompact_cell x).isBounded
    intro z hz
    have hdist : dist z p ≤ diam ((M.unitEmbedding ω).cell x) := dist_le_diam_of_mem hbdd hz hpJ
    rw [mem_ball_zero_iff] at hpB ⊢
    have hzp : ‖z‖ ≤ ‖p‖ + dist z p := by
      rw [dist_eq_norm]
      calc ‖z‖ = ‖p + (z - p)‖ := by congr 1; ring
        _ ≤ ‖p‖ + ‖z - p‖ := norm_add_le _ _
    linarith
  have hE : D.area ω (ball 0 (M.radius ω (k + ⌈δ₁ * k⌉₊))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ ((1 + δ) * k)) := by
    have hak' := hak
    rw [show D.scale ((2 : ℝ) ^ (k + ⌈δ₁ * k⌉₊)) ω = M.radius ω (k + ⌈δ₁ * k⌉₊) from
      (hradω _).symm] at hak'
    exact le_trans hak' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) hek))
  exact finite_card_le_of_area hmass hsub (by positivity) hE

end MatedCRTHarmonic.CellScaling
