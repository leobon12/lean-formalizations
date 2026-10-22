import HigherDimLQGMetric.Modulus.BallDiam
import HigherDimLQGMetric.Sharp.GridCount
import HigherDimLQGMetric.Sharp.GridNear

/-!
# Grid and covering (packet W3b, [S] Lemma 2.6, Steps 3–4)

`w3bGrid d L R ε` is the finite set of points of the lattice `(t/(8d)) ℤ^d`, `t = εR`, in the open
ball `B_{(L+1)R}`. It has at most `(16d(L+1) + 5)^d ε^{-d}` points (`w3b_card_grid_le`), and every
point of `B_{LR}` lies within `t/8` of a grid point (`w3b_exists_grid_near`).

**Covering (MA1 A8, Step 4, the midpoint fix of erratum E-8).** For `x, y ∈ B_{LR}` with
`|x − y| ≤ t` let `m = (x + y)/2`; with `w₁` a grid point near `x` and `w₂` a grid point near `m`,
both `x, m ∈ B̄_t(w₁)` and `m, y ∈ B̄_t(w₂)` (`w3b_cover_pair`). Hence if every grid ball has
`s_R(0)⁻¹ sup_{B̄_t(w)} D ≤ ε^s`, then `D(x, y) ≤ 2 ε^s s_R(0)` (`w3b_apply_le_two_mul_of_grid`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The grid of centres: lattice points of `(εR/(8d)) ℤ^d` in the open ball `B_{(L+1)R}`. -/
def w3bGrid (d : ℕ) (L R ε : ℝ) : Finset (Rd d) :=
  (shellGridBox d (⌈(L + 1) * R / (ε * R / (8 * d))⌉₊ + 1) (ε * R / (8 * d))).filter
    (fun w => ‖w‖ < (L + 1) * R)

theorem w3b_norm_lt_of_mem_grid {L R ε : ℝ} {w : Rd d} (hw : w ∈ w3bGrid d L R ε) :
    ‖w‖ < (L + 1) * R :=
  (Finset.mem_filter.1 hw).2

/-- Every point of `B_{LR}` is within `εR/8` of a grid point. -/
theorem w3b_exists_grid_near (hd : 1 ≤ d) {L R ε : ℝ} (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hε1 : ε ≤ 1) {x : Rd d} (hx : ‖x‖ < L * R) :
    ∃ w ∈ w3bGrid d L R ε, ‖x - w‖ ≤ ε * R / 8 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set s : ℝ := ε * R / (8 * d) with hs_def
  have hs : 0 < s := by positivity
  obtain ⟨w, hwg, hxw⟩ := exists_gridPt_near hs x
  have hds : (d : ℝ) * s = ε * R / 8 := by
    rw [hs_def]
    field_simp
  rw [hds] at hxw
  have hεR : ε * R ≤ R := by nlinarith
  have hwn : ‖w‖ < (L + 1) * R := by
    have h1 : ‖w‖ ≤ ‖x‖ + ‖x - w‖ := by
      calc ‖w‖ = ‖x - (x - w)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - w‖ := norm_sub_le _ _
    nlinarith
  refine ⟨w, ?_, hxw⟩
  refine Finset.mem_filter.2 ⟨?_, hwn⟩
  have hB : 0 ≤ (L + 1) * R := by positivity
  have hmem : w ∈ gridPts s ∩ ball (0 : Rd d) ((L + 1) * R) :=
    ⟨hwg, by rw [mem_ball_zero_iff]; exact hwn⟩
  exact grid_ball_subset_shellGridBox hs hB hmem

/-- Counting: `#grid ≤ (16d(L+1) + 5)^d / ε^d`. -/
theorem w3b_card_grid_le (hd : 1 ≤ d) {L R ε : ℝ} (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    ((w3bGrid d L R ε).card : ℝ) ≤ (16 * d * (L + 1) + 5) ^ d / ε ^ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  set s : ℝ := ε * R / (8 * d) with hs_def
  have hs : 0 < s := by positivity
  set N : ℕ := ⌈(L + 1) * R / s⌉₊ + 1 with hN_def
  have hBs : (L + 1) * R / s = 8 * d * (L + 1) / ε := by
    rw [hs_def]
    field_simp
  have hceil : (⌈(L + 1) * R / s⌉₊ : ℝ) < (L + 1) * R / s + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hNle : (2 * (N : ℝ) + 1) ≤ (16 * d * (L + 1) + 5) / ε := by
    have hN : (N : ℝ) = (⌈(L + 1) * R / s⌉₊ : ℝ) + 1 := by
      rw [hN_def]
      push_cast
      ring
    rw [hN, hBs] at *
    rw [hBs] at hceil
    rw [le_div_iff₀ hε]
    have h5 : 5 * ε ≤ 5 := by linarith
    have hx : (8 * d * (L + 1) / ε) * ε = 8 * d * (L + 1) := by field_simp
    nlinarith
  have hcard : ((w3bGrid d L R ε).card : ℝ) ≤ ((2 * N + 1) ^ d : ℕ) := by
    have h1 : (w3bGrid d L R ε).card ≤ (shellGridBox d N s).card := Finset.card_filter_le _ _
    have h2 := card_shellGridBox_le d N s
    exact_mod_cast h1.trans h2
  calc ((w3bGrid d L R ε).card : ℝ) ≤ ((2 * N + 1) ^ d : ℕ) := hcard
    _ = (2 * (N : ℝ) + 1) ^ d := by push_cast; ring
    _ ≤ ((16 * d * (L + 1) + 5) / ε) ^ d :=
        pow_le_pow_left₀ (by positivity) hNle d
    _ = (16 * d * (L + 1) + 5) ^ d / ε ^ d := div_pow _ _ _

/-- **Covering by grid balls with the midpoint** (MA1 A8, Step 4). -/
theorem w3b_cover_pair (hd : 1 ≤ d) {L R ε : ℝ} (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hε1 : ε ≤ 1) {x y : Rd d} (hx : ‖x‖ < L * R) (hy : ‖y‖ < L * R) (hxy : ‖x - y‖ ≤ ε * R) :
    ∃ m : Rd d, ∃ w₁ ∈ w3bGrid d L R ε, ∃ w₂ ∈ w3bGrid d L R ε,
      x ∈ closedBall w₁ (ε * R) ∧ m ∈ closedBall w₁ (ε * R) ∧
      m ∈ closedBall w₂ (ε * R) ∧ y ∈ closedBall w₂ (ε * R) := by
  set m : Rd d := (2 : ℝ)⁻¹ • (x + y) with hm
  have hmx : ‖m - x‖ ≤ ε * R / 2 := by
    have e : m - x = (2 : ℝ)⁻¹ • (y - x) := by
      rw [hm, smul_add, smul_sub]
      module
    rw [e, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    linarith
  have hmy : ‖y - m‖ ≤ ε * R / 2 := by
    have e : y - m = (2 : ℝ)⁻¹ • (y - x) := by
      rw [hm, smul_add, smul_sub]
      module
    rw [e, norm_smul, norm_sub_rev, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
    linarith
  have hmn : ‖m‖ < L * R := by
    have : ‖m‖ ≤ (‖x‖ + ‖y‖) / 2 := by
      rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
      have := norm_add_le x y
      linarith
    linarith
  obtain ⟨w₁, hw₁, hxw₁⟩ := w3b_exists_grid_near hd hL hR hε hε1 hx
  obtain ⟨w₂, hw₂, hmw₂⟩ := w3b_exists_grid_near hd hL hR hε hε1 hmn
  have hεR : 0 ≤ ε * R := by positivity
  refine ⟨m, w₁, hw₁, w₂, hw₂, ?_, ?_, ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm]
    linarith
  · rw [mem_closedBall, dist_eq_norm]
    calc ‖m - w₁‖ = ‖(m - x) + (x - w₁)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖m - x‖ + ‖x - w₁‖ := norm_add_le _ _
      _ ≤ ε * R := by linarith
  · rw [mem_closedBall, dist_eq_norm]
    linarith
  · rw [mem_closedBall, dist_eq_norm]
    calc ‖y - w₂‖ = ‖(y - m) + (m - w₂)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖y - m‖ + ‖m - w₂‖ := norm_add_le _ _
      _ ≤ ε * R := by linarith

/-- A bound on the normalized ball diameter bounds the metric on the ball. -/
theorem w3b_apply_le_of_ballDiam_le {D : ContMetric d} {S c : ℝ} (hS : 0 < S) (hc : 0 ≤ c)
    {w u v : Rd d} {t : ℝ}
    (hY : ENNReal.ofReal S⁻¹ * w3bBallDiam D w t ≤ ENNReal.ofReal c)
    (hu : u ∈ closedBall w t) (hv : v ∈ closedBall w t) :
    D.1 (u, v) ≤ c * S := by
  have h1 : ENNReal.ofReal (S⁻¹ * D.1 (u, v)) ≤ ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul (inv_nonneg.2 hS.le)]
    exact (mul_le_mul' le_rfl (w3b_ofReal_le_ballDiam D hu hv)).trans hY
  have h2 := (ENNReal.ofReal_le_ofReal_iff hc).1 h1
  rw [inv_mul_le_iff₀ hS] at h2
  linarith

/-- **Deterministic modulus from the grid**: if every grid ball has normalized diameter at most `c`,
then `D(x, y) ≤ 2 c S` for all `x, y ∈ B_{LR}` with `|x − y| ≤ εR`. -/
theorem w3b_apply_le_two_mul_of_grid (hd : 1 ≤ d) {L R ε : ℝ} (hL : 0 < L) (hR : 0 < R)
    (hε : 0 < ε) (hε1 : ε ≤ 1) {D : ContMetric d} {S c : ℝ} (hS : 0 < S) (hc : 0 ≤ c)
    (hgrid : ∀ w ∈ w3bGrid d L R ε,
      ENNReal.ofReal S⁻¹ * w3bBallDiam D w (ε * R) ≤ ENNReal.ofReal c)
    {x y : Rd d} (hx : ‖x‖ < L * R) (hy : ‖y‖ < L * R) (hxy : ‖x - y‖ ≤ ε * R) :
    D.1 (x, y) ≤ 2 * c * S := by
  obtain ⟨m, w₁, hw₁, w₂, hw₂, hx₁, hm₁, hm₂, hy₂⟩ := w3b_cover_pair hd hL hR hε hε1 hx hy hxy
  have h1 := w3b_apply_le_of_ballDiam_le hS hc (hgrid w₁ hw₁) hx₁ hm₁
  have h2 := w3b_apply_le_of_ballDiam_le hS hc (hgrid w₂ hw₂) hm₂ hy₂
  have htri : D.1 (x, y) ≤ D.1 (x, m) + D.1 (m, y) := D.2.triangle x m y
  linarith

end HigherDimLQGMetric
