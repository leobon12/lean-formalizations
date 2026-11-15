/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AbsMergeCore
import InteractingSLE.Spec.Supplement.GW2aForcePath

/-!
# A force collision at a fixed time: the pathwise bounds

Packet PROVE-ABSMERGE. Deterministic, one integrated path at a time.

By (N1) (`IsForcePath.w_eq_N1`), `w + ½ ∑ ρ (v − x) = √κ b`: the driver is the Brownian path minus half the weighted
mark displacements. Let the right marks `0, …, k` be the ones that meet the driver at the fixed time `t`, with weight
`S = ∑_{l ≤ k} ρ_l > −2` (no threshold at `t`), and put

`Γ(s) = (v^k_s − w_s) + ∑_{l ≤ k} (ρ_l/2)(v^k_s − v^l_s)`   (`gamR`).

Then for `s ≤ r < ζ` (`sqrt_mul_sub_eq`)

`√κ (b_r − b_s) = Γ(s) − Γ(r) + (1 + S/2)(v^k_r − v^k_s) + R(s, r)`,

where `R` (`farR`) collects the displacements of the other marks. Along the grid `a_n ↑ t`, `Γ(a_j) → 0` (the
colliding gaps vanish at `t`), `v^k` is nondecreasing and `R(a_n, a_j) = O(t − a_n)`. Hence:

* (**lower bound**, `gamR_sub_le`) `Γ(a_n) − √(t − a_n) ≤ √κ (b_t − b_{a_n})` for large `n`;
* (**upper bound**, `sqrt_mul_le_gamR_add`) if `Γ(a_j) ≤ −√κ √(t − a_j)` for all `j ≥ n₀`, then
  `√κ (b_t − b_{a_n}) ≤ Γ(a_n) + C √(t − a_n)`. Indeed `Γ ≥ −C_k (v^k − v^0)` (`neg_cR_mul_le_gamR`), so the
  spread `v^k − v^0` is at least a multiple of `√(t − a_j)` on the grid; the spread is nonincreasing in time, so the
  gap `v^k − w ≥ v^k − v^0` is at least `c √(t − s)` for all `s ∈ [a_{n₀}, t)`, and
  `v^k_{a_j} − v^k_{a_n} = ∫ 2/(v^k − w) ≤ (4/c) √(t − a_n)`.

No absorbed-merge structure and no Bessel comparison is needed: the drift of the colliding group is a total
derivative of the mark positions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace AbsMerge

open Sec2 GW2aForce

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
  {ζ : ℝ≥0∞}

/-- `Γ_k(s) = (v^k_s − w_s) + ∑_{l ≤ k} (ρ_l/2)(v^k_s − v^l_s)`. -/
def gamR (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (k : Fin nR) (s : ℝ≥0) : ℝ :=
  (vR k s - w s) + ∑ l ∈ univ.filter (fun l : Fin nR => l ≤ k), ρR l / 2 * (vR k s - vR l s)

/-- The displacement term `R(s, r)` of the marks outside the group `0, …, k` between `s` and `r`. -/
def farR (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (k : Fin nR)
    (s r : ℝ≥0) : ℝ :=
  (∑ j ∈ univ.filter (fun j : Fin nR => ¬ j ≤ k), ρR j / 2 * (vR j r - vR j s)) +
    ∑ i, ρL i / 2 * (vL i r - vL i s)

/-- `C_k = 1 + ∑_{l ≤ k} |ρ_l| / 2`. -/
def cR (ρR : Fin nR → ℝ) (k : Fin nR) : ℝ := (∑ l ∈ univ.filter (fun l : Fin nR => l ≤ k), |ρR l| / 2) + 1

theorem one_le_cR (ρR : Fin nR → ℝ) (k : Fin nR) : 1 ≤ cR ρR k := by
  have : 0 ≤ ∑ l ∈ univ.filter (fun l : Fin nR => l ≤ k), |ρR l| / 2 :=
    Finset.sum_nonneg fun l _ => by positivity
  rw [cR]
  linarith

/-- **The exact identity** (from (N1) at two times). -/
theorem sqrt_mul_sub_eq (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {s r : ℝ≥0} (hsr : s ≤ r)
    (hr : (r : ℝ≥0∞) < ζ) (k : Fin nR) :
    Real.sqrt κ * (b r - b s) = gamR ρR w vR k s - gamR ρR w vR k r +
      (1 + partialR ρR k / 2) * (vR k r - vR k s) + farR ρL ρR vL vR k s r := by
  have hs : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hsr) hr
  have hNr := hp.isForcePath.w_eq_N1 hp.driverEq hr
  have hNs := hp.isForcePath.w_eq_N1 hp.driverEq hs
  set F := univ.filter (fun j : Fin nR => j ≤ k) with hF
  set Fc := univ.filter (fun j : Fin nR => ¬ j ≤ k) with hFc
  have hL : ∑ i, ρL i * (vL i r - xL i) - ∑ i, ρL i * (vL i s - xL i) = ∑ i, ρL i * (vL i r - vL i s) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∑ j, ρR j * (vR j r - xR j) - ∑ j, ρR j * (vR j s - xR j) = ∑ j, ρR j * (vR j r - vR j s) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsplit : ∑ j, ρR j * (vR j r - vR j s) =
      ∑ j ∈ F, ρR j * (vR j r - vR j s) + ∑ j ∈ Fc, ρR j * (vR j r - vR j s) :=
    (Finset.sum_filter_add_sum_filter_not univ _ _).symm
  have hin : ∑ j ∈ F, ρR j * (vR j r - vR j s) = partialR ρR k * (vR k r - vR k s) -
      ∑ j ∈ F, ρR j * ((vR k r - vR j r) - (vR k s - vR j s)) := by
    rw [partialR, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hgam : gamR ρR w vR k s - gamR ρR w vR k r = (vR k s - w s) - (vR k r - w r) -
      1 / 2 * ∑ j ∈ F, ρR j * ((vR k r - vR j r) - (vR k s - vR j s)) := by
    have : ∑ l ∈ F, ρR l / 2 * (vR k s - vR l s) - ∑ l ∈ F, ρR l / 2 * (vR k r - vR l r) =
        -(1 / 2 * ∑ j ∈ F, ρR j * ((vR k r - vR j r) - (vR k s - vR j s))) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [gamR]
    rw [← hF]
    linarith
  have hfar : farR ρL ρR vL vR k s r = 1 / 2 * ∑ j ∈ Fc, ρR j * (vR j r - vR j s) +
      1 / 2 * ∑ i, ρL i * (vL i r - vL i s) := by
    simp only [farR]
    rw [← hFc, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  linear_combination hNs - hNr + (1 / 2 : ℝ) * hL + (1 / 2 : ℝ) * hR + (1 / 2 : ℝ) * hsplit +
    (1 / 2 : ℝ) * hin - hgam - hfar

/-- **`Γ` is bounded below by the spread:** `−C_k (v^k − v^{k₀}) ≤ Γ_k` for the first mark `k₀`. -/
theorem neg_cR_mul_le_gamR (hp : IsForcePath xL xR ρL ρR w vL vR ζ) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ)
    (k k₀ : Fin nR) (hk₀ : ∀ l, k₀ ≤ l) :
    -(cR ρR k * (vR k s - vR k₀ s)) ≤ gamR ρR w vR k s := by
  set F := univ.filter (fun l : Fin nR => l ≤ k) with hF
  have hD : 0 ≤ vR k s - vR k₀ s := sub_nonneg.2 (hp.monotone_vR hs (hk₀ k))
  have hw : 0 ≤ vR k s - w s := sub_nonneg.2 (hp.w_le_vR hs k)
  have hsum : -((∑ l ∈ F, |ρR l| / 2) * (vR k s - vR k₀ s)) ≤ ∑ l ∈ F, ρR l / 2 * (vR k s - vR l s) := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun l hl => ?_
    have hlk : l ≤ k := (Finset.mem_filter.1 hl).2
    have h0 : 0 ≤ vR k s - vR l s := sub_nonneg.2 (hp.monotone_vR hs hlk)
    have h1 : vR k s - vR l s ≤ vR k s - vR k₀ s := sub_le_sub_left (hp.monotone_vR hs (hk₀ l)) _
    have h2 : -(|ρR l| / 2 * (vR k s - vR l s)) ≤ ρR l / 2 * (vR k s - vR l s) := by
      have := neg_abs_le (ρR l / 2 * (vR k s - vR l s))
      rwa [abs_mul, abs_div, abs_two, abs_of_nonneg h0] at this
    have h3 : |ρR l| / 2 * (vR k s - vR l s) ≤ |ρR l| / 2 * (vR k s - vR k₀ s) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  simp only [gamR, cR]
  rw [← hF, add_mul, one_mul]
  linarith

/-- If the colliding gaps tend to `0` along the grid, so does `Γ`. -/
theorem tendsto_gamR {t : ℝ≥0} {k : Fin nR}
    (hcol : ∀ l, l ≤ k → Tendsto (fun n => vR l (grid t n) - w (grid t n)) atTop (𝓝 0)) :
    Tendsto (fun n => gamR ρR w vR k (grid t n)) atTop (𝓝 0) := by
  have hk := hcol k le_rfl
  have hsum : Tendsto (fun n => ∑ l ∈ univ.filter (fun l : Fin nR => l ≤ k),
      ρR l / 2 * ((vR k (grid t n) - w (grid t n)) - (vR l (grid t n) - w (grid t n)))) atTop (𝓝 0) := by
    have := tendsto_finsetSum (univ.filter (fun l : Fin nR => l ≤ k)) fun l hl =>
      ((hk.sub (hcol l (Finset.mem_filter.1 hl).2)).const_mul (ρR l / 2))
    simpa only [sub_zero, mul_zero, Finset.sum_const_zero] using this
  have := hk.add hsum
  rw [add_zero] at this
  refine this.congr fun n => ?_
  simp only [gamR]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

theorem lt_zeta_of_lt {t : ℝ≥0} (hζ : ∀ n, (grid t n : ℝ≥0∞) < ζ) {s : ℝ≥0} (hst : s < t) :
    (s : ℝ≥0∞) < ζ := by
  obtain ⟨j, hj⟩ := ((tendsto_grid t).eventually (lt_mem_nhds hst)).exists
  exact lt_trans (by exact_mod_cast hj) (hζ j)

/-- **Lower bound along the grid**: `Γ(a_n) − √(t − a_n) ≤ √κ (b_t − b_{a_n})` for `n ≥ N`. -/
theorem gamR_sub_le (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (hζ : ∀ n, (grid t n : ℝ≥0∞) < ζ) (hbt : Tendsto (fun n => b (grid t n)) atTop (𝓝 (b t)))
    {k : Fin nR} (hS : -2 < partialR ρR k)
    (hcol : ∀ l, l ≤ k → Tendsto (fun n => vR l (grid t n) - w (grid t n)) atTop (𝓝 0)) {N : ℕ}
    (hfar : ∀ n, N ≤ n → ∀ j, n ≤ j →
      |farR ρL ρR vL vR k (grid t n) (grid t j)| ≤ Real.sqrt ((t : ℝ) - grid t n))
    {n : ℕ} (hn : N ≤ n) :
    gamR ρR w vR k (grid t n) - Real.sqrt ((t : ℝ) - grid t n) ≤ Real.sqrt κ * (b t - b (grid t n)) := by
  have hlim : Tendsto (fun j => Real.sqrt κ * (b (grid t j) - b (grid t n))) atTop
      (𝓝 (Real.sqrt κ * (b t - b (grid t n)))) := (hbt.sub_const _).const_mul _
  have hlow : Tendsto (fun j => gamR ρR w vR k (grid t n) - gamR ρR w vR k (grid t j) -
      Real.sqrt ((t : ℝ) - grid t n)) atTop
      (𝓝 (gamR ρR w vR k (grid t n) - 0 - Real.sqrt ((t : ℝ) - grid t n))) :=
    ((tendsto_gamR hcol).const_sub _).sub_const _
  rw [sub_zero] at hlow
  refine le_of_tendsto_of_tendsto hlow hlim ?_
  filter_upwards [eventually_ge_atTop n] with j hj
  have hid := sqrt_mul_sub_eq hp (grid_mono t hj) (hζ j) k
  have hmono : 0 ≤ vR k (grid t j) - vR k (grid t n) :=
    sub_nonneg.2 (hp.isForcePath.monotoneOn_vR k (hζ n) (hζ j) (grid_mono t hj))
  have hS' : 0 ≤ 1 + partialR ρR k / 2 := by linarith
  have hf := (abs_le.1 (hfar n hn j hj)).1
  have hprod := mul_nonneg hS' hmono
  linarith

/-- **The spread on the grid controls the spread everywhere** (the spread `v^k − v^{k₀}` is nonincreasing in
time and `t − a_{j+1} = (t − a_j)/2`). -/
theorem le_spread_of_grid (hp : IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0}
    (hζ : ∀ n, (grid t n : ℝ≥0∞) < ζ) {k k₀ : Fin nR} (hk₀ : k₀ ≤ k) {c : ℝ} (hc : 0 ≤ c) {n₀ : ℕ}
    (hgrid : ∀ j, n₀ ≤ j → c * Real.sqrt ((t : ℝ) - grid t j) ≤ vR k (grid t j) - vR k₀ (grid t j))
    {s : ℝ≥0} (hs₀ : grid t n₀ ≤ s) (hst : s < t) :
    c / Real.sqrt 2 * Real.sqrt ((t : ℝ) - s) ≤ vR k s - vR k₀ s := by
  classical
  have hex : ∃ j, s < grid t j := ((tendsto_grid t).eventually (lt_mem_nhds hst)).exists
  have hj₁s : s < grid t (Nat.find hex) := Nat.find_spec hex
  have hj₁pos : n₀ < Nat.find hex := by
    by_contra h
    exact absurd (lt_of_lt_of_le hj₁s (grid_mono t (not_lt.1 h))) (not_lt.2 hs₀)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hj] at hj₁s
  have hjs : grid t j ≤ s := not_lt.1 (Nat.find_min hex (by omega))
  have hmono := hp.vR_sub_vR_le_of_le hj₁s.le (hζ (j + 1)) hk₀
  have hg := hgrid (j + 1) (by omega)
  have hsq : Real.sqrt ((t : ℝ) - s) / Real.sqrt 2 ≤ Real.sqrt ((t : ℝ) - grid t (j + 1)) := by
    rw [sub_grid_succ, Real.sqrt_div' _ zero_le_two]
    refine div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg 2)
    have : (grid t j : ℝ) ≤ s := by exact_mod_cast hjs
    linarith
  calc c / Real.sqrt 2 * Real.sqrt ((t : ℝ) - s) = c * (Real.sqrt ((t : ℝ) - s) / Real.sqrt 2) := by ring
    _ ≤ c * Real.sqrt ((t : ℝ) - grid t (j + 1)) := mul_le_mul_of_nonneg_left hsq hc
    _ ≤ vR k s - vR k₀ s := hg.trans hmono

/-- **The colliding mark moves little**: if `v^k − w ≥ c √(t − ·)` on `[a_{n₀}, t)`, then
`v^k_{a_j} − v^k_{a_n} ≤ (4/c) √(t − a_n)`. -/
theorem vR_sub_le_of_gap (hp : IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0} (ht : 0 < t)
    (hζ : ∀ n, (grid t n : ℝ≥0∞) < ζ) {k : Fin nR} {c : ℝ} (hc : 0 < c) {n₀ : ℕ}
    (hgap : ∀ s : ℝ≥0, grid t n₀ ≤ s → s < t → c * Real.sqrt ((t : ℝ) - s) ≤ vR k s - w s)
    {n j : ℕ} (hn : n₀ ≤ n) (hj : n ≤ j) :
    vR k (grid t j) - vR k (grid t n) ≤ 4 / c * Real.sqrt ((t : ℝ) - grid t n) := by
  set a : ℝ := (grid t n : ℝ) with ha
  set e : ℝ := (grid t j : ℝ) with he
  have hae : a ≤ e := by exact_mod_cast grid_mono t hj
  have ha0 : 0 ≤ a := NNReal.coe_nonneg _
  have het : e < t := by exact_mod_cast grid_lt ht j
  rw [hp.vR_sub (grid_mono t hj) (hζ j) k]
  have hsub : uIcc a e ⊆ uIcc 0 e := by
    rw [uIcc_of_le hae, uIcc_of_le (ha0.trans hae)]
    exact Icc_subset_Icc ha0 le_rfl
  have hint1 := (hp.intervalIntegrable_forceR (hζ j) k).mono_set hsub
  have hpos : ∀ r ∈ uIcc a e, 0 < (t : ℝ) - r := fun r hr => by
    rw [uIcc_of_le hae] at hr
    linarith [hr.2]
  have hcont : ContinuousOn (fun r : ℝ => 2 / (c * Real.sqrt ((t : ℝ) - r))) (uIcc a e) := by
    refine ContinuousOn.div continuousOn_const
      ((continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.sub continuous_id))).continuousOn)
      fun r hr => ?_
    exact (mul_pos hc (Real.sqrt_pos.2 (hpos r hr))).ne'
  have hint2 : IntervalIntegrable (fun r : ℝ => 2 / (c * Real.sqrt ((t : ℝ) - r))) volume a e :=
    hcont.intervalIntegrable
  have hle : ∫ r in a..e, 2 / (vR k r.toNNReal - w r.toNNReal) ≤
      ∫ r in a..e, 2 / (c * Real.sqrt ((t : ℝ) - r)) := by
    refine intervalIntegral.integral_mono_on hae hint1 hint2 fun r hr => ?_
    have hr0 : 0 ≤ r := ha0.trans hr.1
    have hs₀ : grid t n₀ ≤ r.toNNReal :=
      (grid_mono t hn).trans ((Real.le_toNNReal_iff_coe_le hr0).2 hr.1)
    have hst : r.toNNReal < t := (Real.toNNReal_lt_iff_lt_coe hr0).2 (lt_of_le_of_lt hr.2 het)
    have hg := hgap _ hs₀ hst
    rw [Real.coe_toNNReal r hr0] at hg
    have hp' : 0 < c * Real.sqrt ((t : ℝ) - r) :=
      mul_pos hc (Real.sqrt_pos.2 (hpos r (by rw [uIcc_of_le hae]; exact hr)))
    exact div_le_div_of_nonneg_left zero_le_two hp' hg
  have hFTC : ∫ r in a..e, 2 / (c * Real.sqrt ((t : ℝ) - r)) =
      -(4 / c) * Real.sqrt ((t : ℝ) - e) - -(4 / c) * Real.sqrt ((t : ℝ) - a) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun r => -(4 / c) * Real.sqrt ((t : ℝ) - r)) (fun r hr => ?_) hint2
    have hr' := hpos r hr
    have h1 : HasDerivAt (fun x : ℝ => (t : ℝ) - x) (-1) r := (hasDerivAt_id r).const_sub _
    have h3 := (h1.sqrt hr'.ne').const_mul (-(4 / c))
    refine h3.congr_deriv ?_
    have hs : 0 < Real.sqrt ((t : ℝ) - r) := Real.sqrt_pos.2 hr'
    field_simp
    ring
  have hnn : 0 ≤ 4 / c * Real.sqrt ((t : ℝ) - e) := by positivity
  linarith

/-- The constant of the upper bound. -/
def upC (κ : ℝ) (ρR : Fin nR → ℝ) (k : Fin nR) : ℝ :=
  (1 + partialR ρR k / 2) * (4 / (Real.sqrt κ / cR ρR k / Real.sqrt 2)) + 1

/-- **Upper bound along the grid**: if `Γ(a_j) ≤ −√κ √(t − a_j)` for all `j ≥ n₀`, then
`√κ (b_t − b_{a_n}) ≤ Γ(a_n) + C √(t − a_n)` for `n ≥ max n₀ N`. -/
theorem sqrt_mul_le_gamR_add (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hκ : 0 < κ)
    {t : ℝ≥0} (ht : 0 < t) (hζ : ∀ n, (grid t n : ℝ≥0∞) < ζ)
    (hbt : Tendsto (fun n => b (grid t n)) atTop (𝓝 (b t))) {k : Fin nR} (hS : -2 < partialR ρR k)
    (hcol : ∀ l, l ≤ k → Tendsto (fun n => vR l (grid t n) - w (grid t n)) atTop (𝓝 0)) {N : ℕ}
    (hfar : ∀ n, N ≤ n → ∀ j, n ≤ j →
      |farR ρL ρR vL vR k (grid t n) (grid t j)| ≤ Real.sqrt ((t : ℝ) - grid t n))
    {n₀ : ℕ} (hneg : ∀ j, n₀ ≤ j →
      gamR ρR w vR k (grid t j) ≤ -(Real.sqrt κ * Real.sqrt ((t : ℝ) - grid t j)))
    {n : ℕ} (hn₀ : n₀ ≤ n) (hN : N ≤ n) :
    Real.sqrt κ * (b t - b (grid t n)) ≤
      gamR ρR w vR k (grid t n) + upC κ ρR k * Real.sqrt ((t : ℝ) - grid t n) := by
  have hfp := hp.isForcePath
  set k₀ : Fin nR := ⟨0, k.pos⟩ with hk₀_def
  have hk₀ : ∀ l, k₀ ≤ l := fun l => Fin.le_def.2 (Nat.zero_le _)
  have hC : 1 ≤ cR ρR k := one_le_cR ρR k
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hgrid : ∀ j, n₀ ≤ j → Real.sqrt κ / cR ρR k * Real.sqrt ((t : ℝ) - grid t j) ≤
      vR k (grid t j) - vR k₀ (grid t j) := by
    intro j hj
    have h1 := neg_cR_mul_le_gamR hfp (hζ j) k k₀ hk₀
    have h2 := hneg j hj
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    linarith
  set c₁ := Real.sqrt κ / cR ρR k / Real.sqrt 2 with hc₁_def
  have hc₁ : 0 < c₁ := by positivity
  have hgap : ∀ s : ℝ≥0, grid t n₀ ≤ s → s < t → c₁ * Real.sqrt ((t : ℝ) - s) ≤ vR k s - w s := by
    intro s hs hst
    have h1 := le_spread_of_grid hfp hζ (hk₀ k) (by positivity) hgrid hs hst
    have h2 := hfp.w_le_vR (lt_zeta_of_lt hζ hst) k₀
    linarith
  have hlim : Tendsto (fun j => Real.sqrt κ * (b (grid t j) - b (grid t n))) atTop
      (𝓝 (Real.sqrt κ * (b t - b (grid t n)))) := (hbt.sub_const _).const_mul _
  have hup : Tendsto (fun j => gamR ρR w vR k (grid t n) - gamR ρR w vR k (grid t j) +
      upC κ ρR k * Real.sqrt ((t : ℝ) - grid t n)) atTop
      (𝓝 (gamR ρR w vR k (grid t n) - 0 + upC κ ρR k * Real.sqrt ((t : ℝ) - grid t n))) :=
    ((tendsto_gamR hcol).const_sub _).add_const _
  rw [sub_zero] at hup
  refine le_of_tendsto_of_tendsto hlim hup ?_
  filter_upwards [eventually_ge_atTop n] with j hj
  have hid := sqrt_mul_sub_eq hp (grid_mono t hj) (hζ j) k
  have hf := (abs_le.1 (hfar n hN j hj)).2
  have hS' : 0 ≤ 1 + partialR ρR k / 2 := by linarith
  have hmv := mul_le_mul_of_nonneg_left (vR_sub_le_of_gap hfp ht hζ hc₁ hgap hn₀ hj) hS'
  have hC' : upC κ ρR k * Real.sqrt ((t : ℝ) - grid t n) =
      (1 + partialR ρR k / 2) * (4 / c₁ * Real.sqrt ((t : ℝ) - grid t n)) +
        Real.sqrt ((t : ℝ) - grid t n) := by
    rw [upC, hc₁_def]; ring
  linarith

/-- A displacement `∫_{a_n}^{a_j} 2/(u − v)` with `|u − v| > δ` near `t` is at most `(2/δ)(t − a_n)`. -/
theorem abs_integral_le_of_gap {t : ℝ≥0} (ht : 0 < t) {u v : ℝ≥0 → ℝ} {δ ε : ℝ} (hδ : 0 < δ)
    (hgap : ∀ s : ℝ≥0, dist s t < ε → δ < |u s - v s|) {n j : ℕ} (hn : (t : ℝ) - grid t n < ε)
    (hj : n ≤ j) :
    |∫ r in (grid t n : ℝ)..(grid t j), 2 / (u r.toNNReal - v r.toNNReal)| ≤ 2 / δ * ((t : ℝ) - grid t n) := by
  have hnj : (grid t n : ℝ) ≤ grid t j := by exact_mod_cast grid_mono t hj
  have hjt : (grid t j : ℝ) < t := by exact_mod_cast grid_lt ht j
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (grid t n : ℝ)) (b := grid t j)
    (C := 2 / δ) (f := fun r : ℝ => 2 / (u r.toNNReal - v r.toNNReal)) fun x hx => ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hnj)] at h
    have : 2 / δ * ((grid t j : ℝ) - grid t n) ≤ 2 / δ * ((t : ℝ) - grid t n) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact h.trans this
  · rw [uIoc_of_le hnj] at hx
    have hx0 : 0 ≤ x := (NNReal.coe_nonneg _).trans hx.1.le
    have hd : dist x.toNNReal t < ε := by
      rw [NNReal.dist_eq, Real.coe_toNNReal x hx0, abs_sub_comm, abs_of_pos (by linarith [hx.2])]
      linarith [hx.1]
    have hg := hgap _ hd
    rw [Real.norm_eq_abs, abs_div, abs_two]
    exact div_le_div_of_nonneg_left zero_le_two hδ hg.le

/-- **The marks outside the colliding group move by `O(t − a_n)`**, hence by at most `√(t − a_n)` for large `n`. -/
theorem exists_abs_farR_le (hp : IsForcePath xL xR ρL ρR w vL vR ζ) {t : ℝ≥0} (ht : 0 < t)
    (htζ : (t : ℝ≥0∞) < ζ) {k : Fin nR} (hR : ∀ l, ¬ l ≤ k → w t < vR l t) (hL : ∀ i, vL i t < w t) :
    ∃ N, ∀ n, N ≤ n → ∀ j, n ≤ j →
      |farR ρL ρR vL vR k (grid t n) (grid t j)| ≤ Real.sqrt ((t : ℝ) - grid t n) := by
  classical
  obtain ⟨δR, hδR, hδR'⟩ := exists_pos_lt_all (fun l : Fin nR => if l ≤ k then (1 : ℝ) else vR l t - w t)
    (fun l => by split_ifs with h; exacts [one_pos, sub_pos.2 (hR l h)])
  obtain ⟨δL, hδL, hδL'⟩ := exists_pos_lt_all (fun i : Fin nL => w t - vL i t) (fun i => sub_pos.2 (hL i))
  set δ := min δR δL with hδ_def
  have hδ : 0 < δ := lt_min hδR hδL
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hnhds : {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} ∈ 𝓝 t := hopen.mem_nhds htζ
  have hcw : ContinuousAt w t := hp.continuousOn_w.continuousAt hnhds
  have hev : ∀ᶠ s in 𝓝 t, (∀ l : Fin nR, ¬ l ≤ k → δ < |vR l s - w s|) ∧ ∀ i, δ < |vL i s - w s| := by
    refine (eventually_all.2 fun l => ?_).and (eventually_all.2 fun i => ?_)
    · by_cases hl : l ≤ k
      · exact Eventually.of_forall fun s h => absurd hl h
      · have h1 : δ < vR l t - w t := by
          have := hδR' l
          simp only [hl, ↓reduceIte] at this
          exact (min_le_left _ _).trans_lt this
        have hc : ContinuousAt (fun s => vR l s - w s) t :=
          ((hp.continuousOn_vR l).continuousAt hnhds).sub hcw
        filter_upwards [hc.eventually (lt_mem_nhds h1)] with s hs _
        exact hs.trans_le (le_abs_self _)
    · have h1 : δ < w t - vL i t := (min_le_right _ _).trans_lt (hδL' i)
      have hc : ContinuousAt (fun s => w s - vL i s) t :=
        hcw.sub ((hp.continuousOn_vL i).continuousAt hnhds)
      filter_upwards [hc.eventually (lt_mem_nhds h1)] with s hs
      rw [abs_sub_comm]
      exact hs.trans_le (le_abs_self _)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set M : ℝ := ((∑ l, |ρR l| / 2) + ∑ i, |ρL i| / 2) * (2 / δ) with hM
  have hM0 : 0 ≤ M := by positivity
  have hs0 := tendsto_sub_grid t
  have h1 : ∀ᶠ n in atTop, (t : ℝ) - grid t n < ε := hs0.eventually (gt_mem_nhds hε)
  have hsq : Tendsto (fun n => Real.sqrt ((t : ℝ) - grid t n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hs0
    rwa [Real.sqrt_zero] at this
  have h2 : ∀ᶠ n in atTop, Real.sqrt ((t : ℝ) - grid t n) < 1 / (M + 1) :=
    hsq.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨N, fun n hn j hj => ?_⟩
  obtain ⟨hεn, hsqn⟩ := hN n hn
  have hpos := sub_grid_pos ht n
  set d : ℝ := (t : ℝ) - grid t n with hd_def
  have hjζ : (grid t j : ℝ≥0∞) < ζ := lt_trans (by exact_mod_cast grid_lt ht j) htζ
  have hdR : ∀ l : Fin nR, ¬ l ≤ k → |vR l (grid t j) - vR l (grid t n)| ≤ 2 / δ * d := by
    intro l hl
    rw [hp.vR_sub (grid_mono t hj) hjζ l]
    exact abs_integral_le_of_gap ht hδ (fun s hs => (hball hs).1 l hl) hεn hj
  have hdL : ∀ i, |vL i (grid t j) - vL i (grid t n)| ≤ 2 / δ * d := by
    intro i
    rw [hp.vL_sub (grid_mono t hj) hjζ i]
    exact abs_integral_le_of_gap ht hδ (fun s hs => (hball hs).2 i) hεn hj
  have hA : |∑ l ∈ univ.filter (fun l : Fin nR => ¬ l ≤ k), ρR l / 2 * (vR l (grid t j) - vR l (grid t n))| ≤
      (∑ l, |ρR l| / 2) * (2 / δ * d) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine (Finset.sum_le_sum fun l hl => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun l _ _ => by positivity)
    rw [abs_mul, abs_div, abs_two]
    exact mul_le_mul_of_nonneg_left (hdR l (Finset.mem_filter.1 hl).2) (by positivity)
  have hB : |∑ i, ρL i / 2 * (vL i (grid t j) - vL i (grid t n))| ≤ (∑ i, |ρL i| / 2) * (2 / δ * d) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, abs_div, abs_two]
    exact mul_le_mul_of_nonneg_left (hdL i) (by positivity)
  have hfarle : |farR ρL ρR vL vR k (grid t n) (grid t j)| ≤ M * d := by
    refine (abs_add_le _ _).trans ?_
    rw [hM]
    nlinarith [hA, hB]
  have hsd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hpos.le
  have hMs : M * Real.sqrt d ≤ 1 := by
    have h3 : M * Real.sqrt d ≤ M * (1 / (M + 1)) := mul_le_mul_of_nonneg_left hsqn.le hM0
    have h4 : M * (1 / (M + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    linarith
  calc |farR ρL ρR vL vR k (grid t n) (grid t j)| ≤ M * d := hfarle
    _ = (M * Real.sqrt d) * Real.sqrt d := by rw [mul_assoc M (Real.sqrt d), hsd]
    _ ≤ 1 * Real.sqrt d := mul_le_mul_of_nonneg_right hMs (Real.sqrt_nonneg _)
    _ = Real.sqrt d := one_mul _

end AbsMerge

end Theorem14

end InteractingSLE
