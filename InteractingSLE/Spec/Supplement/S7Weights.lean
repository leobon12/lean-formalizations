/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityWeights
import InteractingSLE.Spec.Sec7.ContinuityStrip

/-!
# Supplement §7: the weight algebra of the local comparison and ordered completion lemmas

Packet PROVE-SUPP7 (specification supplement §7, `source/spec/p481-528.md`, pp. 489–510). Throughout
`0 < κ < 4`, `λ = sleLambda κ = π/√κ`, `χ = chiC κ = 2/√κ − √κ/2`, `c = κ/2 − 2`, `d_* = κ/2 − 4`. An angle-`θ`
flow line sees a boundary height `C` as the cumulative weight `cumWeightLeft κ (C + θχ) = −(C + θχ)/λ − 1` on its
left and `cumWeightRight κ (C + θχ) = (C + θχ)/λ − 1` on its right. The angle gap of two angles `θ₁ < θ₂` is
`d = (θ₂ − θ₁)χ/λ` (`angleGap`).

* **Lemma G2** (p. 491): the cumulative weights `0, d − 2, d` of the two four-height reference flows
  (`g2_left_weights`, `g2_right_weights`), all `> −2` (`g2_weights_gt`), so their force words meet no continuation
  threshold (`g2_not_thresholdCondition`).
* **Lemma G2a** (p. 492): intermediate heights `−λ − θ₂χ < C < λ − θ₁χ` are exactly those with admissible
  intermediate weights for both flows (`g2a_weights_gt_iff`).
* **Lemma G2b** (p. 492): the reflected two-mark weights `r₁ = d − 2`, `r₂ = 2`, `S = d > 0 > c`, and `d > d_*`
  (`g2b_weights`).
* **Lemma G4** (p. 494): `R > −λ − πχ` iff the cumulative weight `S = R/λ − 1` exceeds `κ/2 − 4` (`g4_iff`), and the
  angular version (`g4_iff_angle`).
* **Theorem G6** (p. 495): an old-range side has seed weights `0` and `d` (`g6_old_left_weights`,
  `g6_old_right_weights`), and `d > c` iff `θ₁ − θ₂ < π` (`g6_angleGap_gt_iff`).
* **Lemma G8** (pp. 499–501): the seed weights `(1 + d; r)` and `(1; r + d)` (`g8_weights`), their admissibility and
  the nonhitting left sides (`g8_admissible`), and the affine normalization of the small-gap frame
  (`g8_affine_normalization`, `g8_subset_Ioi_junction`).
* **Lemma G11** (pp. 503–504), reusing Aux. lemma 98 (`Sec7.aux98*`, PROVE-SEC7-C): the classification
  `d_* < S < c ↔ −1 < μ < 1`, `S ≥ c ↔ μ ≤ −1` (`g11_mu_mem_iff`, `g11_mu_le_iff`), `μ < 1` and `A − σ > 0` from
  `S > d_*` alone (`g11_mu_lt_one`, `g11_A_sub_sigma_pos`), and the comparison `X_t ≥ −√κ B_t + (S − d_*)t`
  (`g11_Q3`).
* **Lemma G12** (p. 504): `d_* < −2` for `κ < 4` (`dStar_lt_neg_two`).
* **Lemmas G14, G15** (pp. 507–509): `r₂ = r₁ + d`, `ℓ₂ = ℓ₁ − d`, so termination of the outer path forces
  termination of the inner one (`g14_right`, `g14_left`).
-/

set_option autoImplicit false

noncomputable section

open Real Finset
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Supp7

open Sec4

variable {κ : ℝ}

/-- The angle gap `d = (θ₂ − θ₁)χ/λ` of two angles (supplement §7, G2, G6, G8, G14, G15). -/
def angleGap (κ θ₁ θ₂ : ℝ) : ℝ := (θ₂ - θ₁) * chiC κ / sleLambda κ

/-- `d > 0` for `θ₁ < θ₂` and `0 < κ < 4`. -/
theorem angleGap_pos (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    0 < angleGap κ θ₁ θ₂ :=
  div_pos (mul_pos (sub_pos.2 hθ) (chiC_pos hκ hκ4)) (sleLambda_pos hκ)

/-- Shifting the angle by `θ₂ − θ₁` adds `d` to a right weight. -/
theorem cumWeightRight_add_angle (hκ : 0 < κ) (C θ₁ θ₂ : ℝ) :
    cumWeightRight κ (C + θ₂ * chiC κ) = cumWeightRight κ (C + θ₁ * chiC κ) + angleGap κ θ₁ θ₂ := by
  have := sleLambda_ne_zero hκ
  simp only [cumWeightRight, angleGap]
  field_simp
  ring

/-- Shifting the angle by `θ₂ − θ₁` subtracts `d` from a left weight. -/
theorem cumWeightLeft_add_angle (hκ : 0 < κ) (C θ₁ θ₂ : ℝ) :
    cumWeightLeft κ (C + θ₂ * chiC κ) = cumWeightLeft κ (C + θ₁ * chiC κ) - angleGap κ θ₁ θ₂ := by
  have := sleLambda_ne_zero hκ
  simp only [cumWeightLeft, angleGap]
  field_simp
  ring

/-! ### Lemma G2: the four-height reference -/

/-- **Lemma G2**, the flow from `w₁` (angle `θ₁`): its successive cumulative left weights, read from its seed
outward over the heights `−λ − θ₁χ`, `λ − θ₂χ`, `−λ − θ₂χ`, are `0, d − 2, d`, and its right seed weight (height
`λ − θ₁χ`) is `0`. -/
theorem g2_left_weights (hκ : 0 < κ) (θ₁ θ₂ : ℝ) :
    cumWeightLeft κ ((-sleLambda κ - θ₁ * chiC κ) + θ₁ * chiC κ) = 0 ∧
    cumWeightLeft κ ((sleLambda κ - θ₂ * chiC κ) + θ₁ * chiC κ) = angleGap κ θ₁ θ₂ - 2 ∧
    cumWeightLeft κ ((-sleLambda κ - θ₂ * chiC κ) + θ₁ * chiC κ) = angleGap κ θ₁ θ₂ ∧
    cumWeightRight κ ((sleLambda κ - θ₁ * chiC κ) + θ₁ * chiC κ) = 0 := by
  have := sleLambda_ne_zero hκ
  simp only [cumWeightLeft, cumWeightRight, angleGap]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **Lemma G2**, the flow from `w₂` (angle `θ₂`): its successive cumulative right weights over the heights
`λ − θ₂χ`, `−λ − θ₁χ`, `λ − θ₁χ` are `0, d − 2, d`, and its left seed weight (height `−λ − θ₂χ`) is `0`. -/
theorem g2_right_weights (hκ : 0 < κ) (θ₁ θ₂ : ℝ) :
    cumWeightRight κ ((sleLambda κ - θ₂ * chiC κ) + θ₂ * chiC κ) = 0 ∧
    cumWeightRight κ ((-sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ) = angleGap κ θ₁ θ₂ - 2 ∧
    cumWeightRight κ ((sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ) = angleGap κ θ₁ θ₂ ∧
    cumWeightLeft κ ((-sleLambda κ - θ₂ * chiC κ) + θ₂ * chiC κ) = 0 := by
  have := sleLambda_ne_zero hκ
  simp only [cumWeightLeft, cumWeightRight, angleGap]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- **Lemma G2**: every cumulative weight `0, d − 2, d` is strictly greater than `−2`. -/
theorem g2_weights_gt (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    (-2 : ℝ) < 0 ∧ -2 < angleGap κ θ₁ θ₂ - 2 ∧ -2 < angleGap κ θ₁ θ₂ := by
  have := angleGap_pos hκ hκ4 hθ
  exact ⟨by norm_num, by linarith, by linarith⟩

/-- The partial sums of a three-entry weight vector. -/
theorem partialSum_fin_three (ρ : Fin 3 → ℝ) (m : Fin 3) :
    ∑ i ∈ univ.filter (fun i => i ≤ m), ρ i =
      if m = 0 then ρ 0 else if m = 1 then ρ 0 + ρ 1 else ρ 0 + ρ 1 + ρ 2 := by
  fin_cases m
  · simp only [Fin.zero_eta, Fin.isValue, ite_true]
    rw [show univ.filter (fun i : Fin 3 => i ≤ 0) = {0} by decide, sum_singleton]
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ite_false, ite_true]
    rw [show univ.filter (fun i : Fin 3 => i ≤ 1) = {0, 1} by decide, sum_pair (by decide)]
  · simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, ite_false]
    rw [show univ.filter (fun i : Fin 3 => i ≤ 2) = univ by decide, Fin.sum_univ_three]

/-- **Lemma G2**, no continuation threshold: the force word of the flow from `w₁` has left weights
`(0, d − 2, 2)` (seed, then the marks at `m` and `w₂`; cumulative `0, d − 2, d`) and right seed weight `0`; in no
ordered state does it meet the continuation-threshold condition. By reflection the same holds for the flow from
`w₂`. -/
theorem g2_not_thresholdCondition (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) {w : ℝ}
    {vL : Fin 3 → ℝ} {vR : Fin 1 → ℝ} (hL : Antitone vL) (hLw : ∀ i, vL i ≤ w) (hR : Monotone vR)
    (hRw : ∀ i, w ≤ vR i) :
    ¬ ForceWord.ThresholdCondition ![0, angleGap κ θ₁ θ₂ - 2, 2] ![0] w vL vR := by
  have hd := angleGap_pos hκ hκ4 hθ
  refine Sec7.not_thresholdCondition_of_partialSums hL hLw hR hRw (fun m => ?_) (fun m => ?_)
  · rw [partialSum_fin_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    split_ifs <;> linarith
  · rw [show univ.filter (fun i : Fin 1 => i ≤ m) = univ by ext i; simp [Subsingleton.elim i m]]
    simp

/-! ### Lemma G2a: an arbitrary admissible middle word -/

/-- **Lemma G2a**: an intermediate height `C` gives the flow from `w₁` (angle `θ₁`) an admissible left weight
`−(C + θ₁χ)/λ − 1 > −2`, and the flow from `w₂` (angle `θ₂`) an admissible right weight `(C + θ₂χ)/λ − 1 > −2`,
exactly when `−λ − θ₂χ < C < λ − θ₁χ`. -/
theorem g2a_weights_gt_iff (hκ : 0 < κ) (θ₁ θ₂ C : ℝ) :
    (-2 < cumWeightLeft κ (C + θ₁ * chiC κ) ∧ -2 < cumWeightRight κ (C + θ₂ * chiC κ)) ↔
      (-sleLambda κ - θ₂ * chiC κ < C ∧ C < sleLambda κ - θ₁ * chiC κ) := by
  have hl := sleLambda_pos hκ
  have e1 : -2 < cumWeightLeft κ (C + θ₁ * chiC κ) ↔ C < sleLambda κ - θ₁ * chiC κ := by
    simp only [cumWeightLeft]
    rw [show -2 < -(C + θ₁ * chiC κ) / sleLambda κ - 1 ↔ -1 < -(C + θ₁ * chiC κ) / sleLambda κ by
      constructor <;> intro h <;> linarith, lt_div_iff₀ hl]
    constructor <;> intro h <;> linarith
  have e2 : -2 < cumWeightRight κ (C + θ₂ * chiC κ) ↔ -sleLambda κ - θ₂ * chiC κ < C := by
    simp only [cumWeightRight]
    rw [show -2 < (C + θ₂ * chiC κ) / sleLambda κ - 1 ↔ -1 < (C + θ₂ * chiC κ) / sleLambda κ by
      constructor <;> intro h <;> linarith, lt_div_iff₀ hl]
    constructor <;> intro h <;> linarith
  rw [e1, e2, and_comm]

/-! ### Lemma G2b: avoidance of the other seed -/

/-- `c = κ/2 − 2 < 0` for `κ < 4`. -/
theorem c_neg (hκ4 : κ < 4) : κ / 2 - 2 < 0 := by linarith

/-- `d_* = κ/2 − 4 < −2` for `κ < 4` (**Lemma G12**: a visited nonseed mark has cumulative weight at most
`d_* < −2`, so it is an original terminal point). -/
theorem dStar_lt_neg_two (hκ4 : κ < 4) : κ / 2 - 4 < -2 := by linarith

/-- **Lemma G2b**: in reflected coordinates the flow from `w₁` has the two separated right marks of weights
`r₁ = d − 2` and `r₂ = 2`, with total `S = r₁ + r₂ = d`; then `r₁ > −2`, `S > 0 > c`, and `S > d_*` (the bound used
for G2a's extension through Lemma G12). -/
theorem g2b_weights (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    -2 < angleGap κ θ₁ θ₂ - 2 ∧ (angleGap κ θ₁ θ₂ - 2) + 2 = angleGap κ θ₁ θ₂ ∧
    0 < angleGap κ θ₁ θ₂ ∧ κ / 2 - 2 < 0 ∧ κ / 2 - 4 < angleGap κ θ₁ θ₂ := by
  have hd := angleGap_pos hκ hκ4 hθ
  exact ⟨by linarith, by ring, hd, c_neg hκ4, by linarith⟩

/-! ### Lemma G4: the outward jump threshold -/

/-- `−λ − πχ = (κ/2 − 3)λ`. -/
theorem neg_sleLambda_sub_pi_mul_chiC (hκ : 0 < κ) :
    -sleLambda κ - π * chiC κ = (κ / 2 - 3) * sleLambda κ := by
  rw [pi_mul_chiC hκ]; ring

/-- **Lemma G4**: the outward height `R` exceeds `−λ − πχ` iff its cumulative weight `S = R/λ − 1` exceeds
`κ/2 − 4`. -/
theorem g4_iff (hκ : 0 < κ) (R : ℝ) :
    -sleLambda κ - π * chiC κ < R ↔ κ / 2 - 4 < cumWeightRight κ R := by
  have hl := sleLambda_pos hκ
  rw [neg_sleLambda_sub_pi_mul_chiC hκ]
  simp only [cumWeightRight]
  rw [show κ / 2 - 4 < R / sleLambda κ - 1 ↔ κ / 2 - 3 < R / sleLambda κ by
    constructor <;> intro h <;> linarith, lt_div_iff₀ hl]

/-- **Lemma G4**, original angular convention: `R + θχ > −λ − πχ` iff the angle-`θ` cumulative weight
`(R + θχ)/λ − 1` exceeds `κ/2 − 4`. -/
theorem g4_iff_angle (hκ : 0 < κ) (R θ : ℝ) :
    -sleLambda κ - π * chiC κ < R + θ * chiC κ ↔ κ / 2 - 4 < cumWeightRight κ (R + θ * chiC κ) :=
  g4_iff hκ _

/-- **Lemma G4**, the two-mark reference: with successive right heights `λ, L, R` the cumulative right weights
are `0`, `r₁ = L/λ − 1` and `S = R/λ − 1`. -/
theorem g4_reference_weights (hκ : 0 < κ) (L R : ℝ) :
    cumWeightRight κ (sleLambda κ) = 0 ∧ cumWeightRight κ L = L / sleLambda κ - 1 ∧
      cumWeightRight κ R = R / sleLambda κ - 1 := by
  refine ⟨?_, rfl, rfl⟩
  simp only [cumWeightRight, div_self (sleLambda_ne_zero hκ), sub_self]

/-! ### Theorem G6: the two-height first-contact sector -/

/-- **Theorem G6**: on a left half-line containing an old-range side the height is `−λ − θ₂χ`; the seed weights
of the angle-`θ₁` and angle-`θ₂` flows there are `d` and `0`. -/
theorem g6_old_left_weights (hκ : 0 < κ) (θ₁ θ₂ : ℝ) :
    cumWeightLeft κ ((-sleLambda κ - θ₂ * chiC κ) + θ₁ * chiC κ) = angleGap κ θ₁ θ₂ ∧
    cumWeightLeft κ ((-sleLambda κ - θ₂ * chiC κ) + θ₂ * chiC κ) = 0 :=
  ⟨(g2_left_weights hκ θ₁ θ₂).2.2.1, (g2_right_weights hκ θ₁ θ₂).2.2.2⟩

/-- **Theorem G6**: on a right half-line containing an old-range side the height is `λ − θ₁χ`; the seed weights
of the angle-`θ₁` and angle-`θ₂` flows there are `0` and `d`. -/
theorem g6_old_right_weights (hκ : 0 < κ) (θ₁ θ₂ : ℝ) :
    cumWeightRight κ ((sleLambda κ - θ₁ * chiC κ) + θ₁ * chiC κ) = 0 ∧
    cumWeightRight κ ((sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ) = angleGap κ θ₁ θ₂ :=
  ⟨(g2_left_weights hκ θ₁ θ₂).2.2.2, (g2_right_weights hκ θ₁ θ₂).2.2.1⟩

/-- **Theorem G6**: `d > c` iff `θ₁ − θ₂ < π` (`0 < κ < 4`); so both seed weights `0, d` of an old-range side are
noncolliding (`≥ c`) under the hypothesis `θ₁ < θ₂ + π` of declaration 7.9B. -/
theorem g6_angleGap_gt_iff (hκ : 0 < κ) (hκ4 : κ < 4) (θ₁ θ₂ : ℝ) :
    κ / 2 - 2 < angleGap κ θ₁ θ₂ ↔ θ₁ - θ₂ < π := by
  have hl := sleLambda_pos hκ
  have hc := chiC_pos hκ hκ4
  rw [← neg_pi_mul_chiC_div_sleLambda hκ, angleGap, div_lt_div_iff_of_pos_right hl, neg_mul_eq_neg_mul,
    mul_lt_mul_iff_left₀ hc]
  constructor <;> intro h <;> linarith

/-- **Theorem G6**: under `θ₁ − θ₂ < π` (`θ₁ < θ₂ + π` in declaration 7.9B), both old-range seed weights `0` and
`d` are at least `c`, i.e. noncolliding. -/
theorem g6_noncolliding (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ - θ₂ < π) :
    κ / 2 - 2 ≤ 0 ∧ κ / 2 - 2 < angleGap κ θ₁ θ₂ :=
  ⟨(c_neg hκ4).le, (g6_angleGap_gt_iff hκ hκ4 θ₁ θ₂).2 hθ⟩

/-- **Theorem G6**: the seed weights `r_{i,L} = −(c_L + θᵢχ)/λ − 1`, `r_{i,R} = (c_R + θᵢχ)/λ − 1`. -/
theorem g6_seed_weights (cL cR θ : ℝ) :
    cumWeightLeft κ (cL + θ * chiC κ) = -(cL + θ * chiC κ) / sleLambda κ - 1 ∧
      cumWeightRight κ (cR + θ * chiC κ) = (cR + θ * chiC κ) / sleLambda κ - 1 :=
  ⟨rfl, rfl⟩

/-! ### Lemma G8: the right-boundary reference frame -/

/-- **Lemma G8**: with left value `−a`, `a = 2λ + θ₂χ`, and right value `C`, the angle-`θ₁` path `α` has seed
weights `(1 + d; r)` and the angle-`θ₂` path `β` has `(1; r + d)`, where `r = (C + θ₁χ)/λ − 1`. -/
theorem g8_weights (hκ : 0 < κ) (θ₁ θ₂ C : ℝ) :
    cumWeightLeft κ (-(2 * sleLambda κ + θ₂ * chiC κ) + θ₁ * chiC κ) = 1 + angleGap κ θ₁ θ₂ ∧
    cumWeightRight κ (C + θ₁ * chiC κ) = (C + θ₁ * chiC κ) / sleLambda κ - 1 ∧
    cumWeightLeft κ (-(2 * sleLambda κ + θ₂ * chiC κ) + θ₂ * chiC κ) = 1 ∧
    cumWeightRight κ (C + θ₂ * chiC κ) = cumWeightRight κ (C + θ₁ * chiC κ) + angleGap κ θ₁ θ₂ := by
  have := sleLambda_ne_zero hκ
  refine ⟨?_, rfl, ?_, cumWeightRight_add_angle hκ C θ₁ θ₂⟩ <;>
    simp only [cumWeightLeft, angleGap] <;> field_simp <;> ring

/-- **Lemma G8**: for `−2 < r < c` all four seed weights are admissible (`> −2`), both left sides are nonhitting
(`≥ c`), and the weight `d − 2` of `α` on a side of the known `β` is admissible; moreover `r < c` (the right gap of
`α` has an accessible Jacobi endpoint). -/
theorem g8_admissible (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ r : ℝ} (hθ : θ₁ < θ₂) (hr : -2 < r)
    (hrc : r < κ / 2 - 2) :
    -2 < 1 + angleGap κ θ₁ θ₂ ∧ -2 < r ∧ -2 < (1 : ℝ) ∧ -2 < r + angleGap κ θ₁ θ₂ ∧
      κ / 2 - 2 ≤ 1 + angleGap κ θ₁ θ₂ ∧ κ / 2 - 2 ≤ 1 ∧ -2 < angleGap κ θ₁ θ₂ - 2 ∧ r < κ / 2 - 2 := by
  have hd := angleGap_pos hκ hκ4 hθ
  refine ⟨by linarith, hr, by norm_num, by linarith, by linarith, by linarith, by linarith, hrc⟩

/-- The positive affine map of G8's normalization, sending `w_β ↦ w₂` and `w_α ↦ w₁`. -/
def g8Affine (wβ wα w₂ w₁ x : ℝ) : ℝ := w₂ + (x - wβ) * ((w₁ - w₂) / (wα - wβ))

/-- **Lemma G8**, the affine normalization: if the current coordinates satisfy `w_β < w_α < v_R` with
`v_R − w_α < ε (w_α − w_β)`, the positive affine map `T = g8Affine w_β w_α w₂ w₁` (`w_β ↦ w₂`, `w_α ↦ w₁`) is strictly
increasing and puts the junction `T v_R` in `(w₁, w₁ + ε(w₁ − w₂))`. -/
theorem g8_affine_normalization {wβ wα vR w₂ w₁ ε : ℝ} (hβα : wβ < wα) (h21 : w₂ < w₁)
    (hgap : 0 < vR - wα) (hε : vR - wα < ε * (wα - wβ)) :
    g8Affine wβ wα w₂ w₁ wβ = w₂ ∧ g8Affine wβ wα w₂ w₁ wα = w₁ ∧ w₁ < g8Affine wβ wα w₂ w₁ vR ∧
      g8Affine wβ wα w₂ w₁ vR < w₁ + ε * (w₁ - w₂) ∧ StrictMono (g8Affine wβ wα w₂ w₁) := by
  have hpos : 0 < wα - wβ := sub_pos.2 hβα
  have hk : 0 < (w₁ - w₂) / (wα - wβ) := div_pos (sub_pos.2 h21) hpos
  have hTvR : g8Affine wβ wα w₂ w₁ vR = w₁ + (vR - wα) * ((w₁ - w₂) / (wα - wβ)) := by
    simp only [g8Affine]; field_simp; ring
  refine ⟨by simp [g8Affine], by simp only [g8Affine]; field_simp; ring, ?_, ?_, ?_⟩
  · rw [hTvR]; nlinarith
  · rw [hTvR]
    have : (vR - wα) * ((w₁ - w₂) / (wα - wβ)) < ε * (wα - wβ) * ((w₁ - w₂) / (wα - wβ)) :=
      mul_lt_mul_of_pos_right hε hk
    have e : ε * (wα - wβ) * ((w₁ - w₂) / (wα - wβ)) = ε * (w₁ - w₂) := by field_simp
    linarith
  · intro x y hxy
    simp only [g8Affine]
    nlinarith

/-- **Lemma G8**, the choice of `ε`: if `ε (w₁ − w₂) < x − w₁` for every `x ∈ J` (i.e.
`ε < dist(J, w₁)/(w₁ − w₂)` for the compact `J ⊂ (w₁, ∞)`), then after the normalization the whole interval `J` lies
beyond the junction `T v_R`. -/
theorem g8_subset_Ioi_junction {wβ wα vR w₂ w₁ ε : ℝ} {J : Set ℝ} (hβα : wβ < wα) (h21 : w₂ < w₁)
    (hgap : 0 < vR - wα) (hε : vR - wα < ε * (wα - wβ)) (hJ : ∀ x ∈ J, w₁ + ε * (w₁ - w₂) < x) :
    J ⊆ Set.Ioi (g8Affine wβ wα w₂ w₁ vR) := fun x hx =>
  ((g8_affine_normalization hβα h21 hgap hε).2.2.2.1).trans (hJ x hx)

/-! ### Lemma G11: seed force and a separated mark

G11's proof uses the strip chart and notation of Aux. lemma 98, whose deterministic content is in
`InteractingSLE.Spec.Sec7.ContinuityStrip` (PROVE-SEC7-C): `A = aux98A r = 1 + r/2`,
`σ = aux98Sigma κ r ρ = (κ − 6 − r − 2ρ)/2`, `μ = aux98Mu κ r ρ = σ − r/2`, the identities `A − σ = S − d_*`
(`Sec7.aux98A_sub_aux98Sigma`) and `μ = κ/2 − 3 − S` (`Sec7.aux98Mu_eq`), the Bessel dimension
(`Sec7.one_lt_aux98_bessel_dimension`), the comparison (Q3) (`Sec7.aux98_Q3`) and the tail energy
(`Sec7.aux98_integrableOn_sq_error`). Here are the G11-specific consequences. -/

/-- **Lemma G11**: `d_* < S < c` is exactly `−1 < μ < 1` (`S = r + ρ`, `d_* = κ/2 − 4`, `c = κ/2 − 2`). -/
theorem g11_mu_mem_iff (κ r ρ : ℝ) :
    (κ / 2 - 4 < r + ρ ∧ r + ρ < κ / 2 - 2) ↔ (-1 < Sec7.aux98Mu κ r ρ ∧ Sec7.aux98Mu κ r ρ < 1) := by
  rw [Sec7.aux98Mu_eq]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **Lemma G11**: `S ≥ c` is exactly `μ ≤ −1` (the no-swallow alternative). -/
theorem g11_mu_le_iff (κ r ρ : ℝ) : κ / 2 - 2 ≤ r + ρ ↔ Sec7.aux98Mu κ r ρ ≤ -1 := by
  rw [Sec7.aux98Mu_eq]
  constructor <;> intro h <;> linarith

/-- **Lemma G11**: `S > d_*` gives `μ < 1` (no assumption `S > −2`, unlike `Sec7.aux98Mu_lt_one`). -/
theorem g11_mu_lt_one {κ r ρ : ℝ} (hS : κ / 2 - 4 < r + ρ) : Sec7.aux98Mu κ r ρ < 1 := by
  rw [Sec7.aux98Mu_eq]; linarith

/-- **Lemma G11**: `A − σ = S − d_* > 0` when `S > d_*`. -/
theorem g11_A_sub_sigma_pos {κ r ρ : ℝ} (hS : κ / 2 - 4 < r + ρ) :
    0 < Sec7.aux98A r - Sec7.aux98Sigma κ r ρ := by
  rw [Sec7.aux98A_sub_aux98Sigma]; linarith

/-- **Lemma G11**, the pathwise comparison: if the gap `X` solves
`X_t = −√κ b_t + ∫₀ᵗ (A coth(X_s/2) − σ) ds` and stays positive, then `X_t ≥ −√κ b_t + (S − d_*) t`
(Aux. lemma 98 (Q3) with G11's parameters; `r ≥ −2` makes `A ≥ 0`). -/
theorem g11_Q3 {κ r ρ t : ℝ} {X b : ℝ → ℝ} (hr : -2 ≤ r) (ht : 0 ≤ t)
    (hint : IntervalIntegrable (fun s => Sec7.aux98A r * Sec4.cothHalf (X s) - Sec7.aux98Sigma κ r ρ)
      MeasureTheory.volume 0 t)
    (hpos : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc 0 t)), 0 < X s)
    (heq : X t = -(Real.sqrt κ * b t) +
      ∫ s in (0 : ℝ)..t, (Sec7.aux98A r * Sec4.cothHalf (X s) - Sec7.aux98Sigma κ r ρ)) :
    -(Real.sqrt κ * b t) + ((r + ρ) - (κ / 2 - 4)) * t ≤ X t := by
  have hA : 0 ≤ Sec7.aux98A r := by unfold Sec7.aux98A; linarith
  have h := Sec7.aux98_Q3 hA ht hint hpos heq
  rwa [Sec7.aux98A_sub_aux98Sigma] at h

/-! ### Lemmas G14 and G15: the terminal exterior real meeting -/

/-- **Lemmas G14, G15**, right-hand case: the right cumulative weights at a real point of height `C` satisfy
`r₂ = r₁ + d`; since `d > 0`, termination of the outer path (`r₂ ≤ −2`) forces `r₁ ≤ −2`. -/
theorem g14_right (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) (C : ℝ) :
    cumWeightRight κ (C + θ₂ * chiC κ) = cumWeightRight κ (C + θ₁ * chiC κ) + angleGap κ θ₁ θ₂ ∧
    (cumWeightRight κ (C + θ₂ * chiC κ) ≤ -2 → cumWeightRight κ (C + θ₁ * chiC κ) ≤ -2) := by
  have hd := angleGap_pos hκ hκ4 hθ
  have e := cumWeightRight_add_angle hκ C θ₁ θ₂
  exact ⟨e, fun h => by linarith⟩

/-- **Lemmas G14, G15**, left-hand case: `ℓ₂ = ℓ₁ − d`, so termination of the outer path (`ℓ₁ ≤ −2`) forces
`ℓ₂ ≤ −2`. -/
theorem g14_left (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) (C : ℝ) :
    cumWeightLeft κ (C + θ₂ * chiC κ) = cumWeightLeft κ (C + θ₁ * chiC κ) - angleGap κ θ₁ θ₂ ∧
    (cumWeightLeft κ (C + θ₁ * chiC κ) ≤ -2 → cumWeightLeft κ (C + θ₂ * chiC κ) ≤ -2) := by
  have hd := angleGap_pos hκ hκ4 hθ
  have e := cumWeightLeft_add_angle hκ C θ₁ θ₂
  exact ⟨e, fun h => by linarith⟩

end Supp7

end InteractingSLE
