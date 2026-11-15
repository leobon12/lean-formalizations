/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S7Weights
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Supplement §10: the weight algebra of the later-contact restart and the critical exclusion

Packet PROVE-SUPP10 (specification supplement §10, `source/spec/p529-576.md`, pp. 536–544). Throughout
`0 < κ < 4`, `λ = sleLambda κ`, `χ = chiC κ`, `c = κ/2 − 2`, `e = κ/2 − 4 = c − 2` (p. 536), and the angle gap of
two angles is `d = (θ₂ − θ₁)χ/λ` (`Supp7.angleGap`). An angle-`θ` flow line sees a boundary height `C` as the
cumulative weight `cumWeightLeft κ (C + θχ)` on its left and `cumWeightRight κ (C + θχ)` on its right.

* **Lemma W7** (pp. 537–538): `πχ/λ = −c`, so `θ₁ < θ₂ + π` gives `d > c > −2` (W7.1; `w7_one`). On an exposed
  left old-range interval (height `−λ − θ₂χ`) and an exposed right old-range interval (height `λ − θ₁χ`) the
  outward weights of the two new paths are `0` and `d`, both at least `c` (`w7_oldRange_left`,
  `w7_oldRange_right`). At an old-range/original-real junction whose outer side is supplied by a curve with
  original cumulative weight `r > −2`, the two new outward weights are `r` and `r + d` (zero phase on the
  untouched original interval; `w7_junction_left`, `w7_junction_right`), and both exceed `e`
  (`w7_junction_gt_e`), so G12 excludes exact visits.
* **Theorem W8** (p. 541): the seed groups of a nonempty future are `0` or the positive angle difference on an old
  outer curve side (`w8_oldSide_seed_nonneg`), and at an untouched original-real contact the relative outward
  weight is the original angle-shifted one, so the relative threshold is the original one (`w8_realContact_weight`).
* **Theorem 7.12D** (pp. 543–544): the exposed first left side has height `−λ − θ₋χ`; after adding `θ₊χ` it is
  `−λ + (θ₊ − θ₋)χ`, with right outward cumulative weight `−2 + D_θ` (`thm712D_exposed_weight`), and
  `−2 + D_θ ≥ c ⟺ D_θ ≥ κ/2` (7.12D.1; `thm712D_one`).
* **Critical exclusion after a crossing** (p. 544): with `θ₂ < θ₁ < θ₂ + π`, the critical angle condition
  `(θ₁ − θ₂)χ/λ ≥ κ/2` can hold only if `κ < 2` (`critical_lt_pi_iff`, `kappa_lt_two_of_critical_crossing`).
-/

set_option autoImplicit false

noncomputable section

open Real
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Supp10

open Sec4 Supp7

variable {κ : ℝ}

/-! ### Lemma W7 -/

/-- **(W7.1)** (p. 537): since `πχ/λ = 2 − κ/2 = −c`, the angle hypothesis `θ₁ < θ₂ + π` gives
`d = (θ₂ − θ₁)χ/λ > c > −2`. -/
theorem w7_one (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂ + π) :
    κ / 2 - 2 < angleGap κ θ₁ θ₂ ∧ -2 < κ / 2 - 2 :=
  ⟨(g6_angleGap_gt_iff hκ hκ4 θ₁ θ₂).2 (by linarith), by linarith⟩

/-- **Lemma W7**, exposed left old-range interval (p. 537): its height is `−λ − θ₂χ`; the outward (left) weights
of the new angle-`θ₂` and angle-`θ₁` paths are `0` and `d`, and both are at least `c`, so GB7a excludes every point
of that open interval. -/
theorem w7_oldRange_left (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂ + π) :
    cumWeightLeft κ ((-sleLambda κ - θ₂ * chiC κ) + θ₂ * chiC κ) = 0 ∧
      cumWeightLeft κ ((-sleLambda κ - θ₂ * chiC κ) + θ₁ * chiC κ) = angleGap κ θ₁ θ₂ ∧
      κ / 2 - 2 ≤ 0 ∧ κ / 2 - 2 ≤ angleGap κ θ₁ θ₂ := by
  obtain ⟨hd, -⟩ := w7_one hκ hκ4 hθ
  exact ⟨(g6_old_left_weights hκ θ₁ θ₂).2, (g6_old_left_weights hκ θ₁ θ₂).1, (c_neg hκ4).le, hd.le⟩

/-- **Lemma W7**, exposed right old-range interval (p. 537): its height is `λ − θ₁χ`; the outward (right) weights
of the new angle-`θ₁` and angle-`θ₂` paths are `0` and `d`, both at least `c`. -/
theorem w7_oldRange_right (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂ + π) :
    cumWeightRight κ ((sleLambda κ - θ₁ * chiC κ) + θ₁ * chiC κ) = 0 ∧
      cumWeightRight κ ((sleLambda κ - θ₁ * chiC κ) + θ₂ * chiC κ) = angleGap κ θ₁ θ₂ ∧
      κ / 2 - 2 ≤ 0 ∧ κ / 2 - 2 ≤ angleGap κ θ₁ θ₂ := by
  obtain ⟨hd, -⟩ := w7_one hκ hκ4 hθ
  exact ⟨(g6_old_right_weights hκ θ₁ θ₂).1, (g6_old_right_weights hκ θ₁ θ₂).2, (c_neg hκ4).le, hd.le⟩

/-- **Lemma W7**, left junction (p. 538): on the untouched original interval of height `C` beyond a left
old-range/original-real junction, whose outer side is supplied by the angle-`θ₂` curve with original left
cumulative weight `r = cumWeightLeft κ (C + θ₂χ)`, exact zero phase gives the two new outward weights `r` and
`r + d`. -/
theorem w7_junction_left (hκ : 0 < κ) (C θ₁ θ₂ : ℝ) :
    cumWeightLeft κ (C + θ₁ * chiC κ) = cumWeightLeft κ (C + θ₂ * chiC κ) + angleGap κ θ₁ θ₂ := by
  rw [cumWeightLeft_add_angle hκ C θ₁ θ₂]; ring

/-- **Lemma W7**, right junction (p. 538): the same formula, with `r = cumWeightRight κ (C + θ₁χ)` supplied by the
other (angle-`θ₁`) original curve: the new outward weights are `r` and `r + d`. -/
theorem w7_junction_right (hκ : 0 < κ) (C θ₁ θ₂ : ℝ) :
    cumWeightRight κ (C + θ₂ * chiC κ) = cumWeightRight κ (C + θ₁ * chiC κ) + angleGap κ θ₁ θ₂ :=
  cumWeightRight_add_angle hκ C θ₁ θ₂

/-- **Lemma W7**, junction exclusion (p. 538): if `r > −2` (the supplying path has continued beyond the junction)
and `d > c`, then `r > −2 > e` and `r + d > c − 2 = e`, `e = κ/2 − 4`; G12 therefore excludes exact visits to the
junction by either maximal canonical relative path. -/
theorem w7_junction_gt_e (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ r : ℝ} (hθ : θ₁ < θ₂ + π) (hr : -2 < r) :
    κ / 2 - 4 < r ∧ κ / 2 - 4 < r + angleGap κ θ₁ θ₂ := by
  obtain ⟨hd, -⟩ := w7_one hκ hκ4 hθ
  have he := dStar_lt_neg_two hκ4
  constructor <;> linarith

/-- **Lemma W7**, junction exclusion in terms of the boundary height: at a left junction with original-real height
`C` whose supplying angle-`θ₂` curve has continued (`cumWeightLeft κ (C + θ₂χ) > −2`), both new left weights exceed
`e`. -/
theorem w7_junction_left_gt_e (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ C : ℝ} (hθ : θ₁ < θ₂ + π)
    (hr : -2 < cumWeightLeft κ (C + θ₂ * chiC κ)) :
    κ / 2 - 4 < cumWeightLeft κ (C + θ₂ * chiC κ) ∧ κ / 2 - 4 < cumWeightLeft κ (C + θ₁ * chiC κ) := by
  rw [w7_junction_left hκ C θ₁ θ₂]
  exact w7_junction_gt_e hκ hκ4 hθ hr

/-- **Lemma W7**, the right-junction version: the supplying curve is the angle-`θ₁` one. -/
theorem w7_junction_right_gt_e (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ C : ℝ} (hθ : θ₁ < θ₂ + π)
    (hr : -2 < cumWeightRight κ (C + θ₁ * chiC κ)) :
    κ / 2 - 4 < cumWeightRight κ (C + θ₁ * chiC κ) ∧
      κ / 2 - 4 < cumWeightRight κ (C + θ₂ * chiC κ) := by
  rw [w7_junction_right hκ C θ₁ θ₂]
  exact w7_junction_gt_e hκ hκ4 hθ hr

/-! ### Theorem W8 -/

/-- **Theorem W8**, seed groups (p. 541): an old outer curve side supplies the weight `0` or the positive
difference `d` of the ordered angles `θ₁ < θ₂`; both are admissible (`> −2`). -/
theorem w8_oldSide_seed_nonneg (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂) :
    0 < angleGap κ θ₁ θ₂ ∧ (-2 : ℝ) < 0 ∧ (-2 : ℝ) < angleGap κ θ₁ θ₂ := by
  have hd := angleGap_pos hκ hκ4 hθ
  exact ⟨hd, by norm_num, by linarith⟩

/-- **Theorem W8**, original-real contacts (p. 541): with exact zero phase on an untouched original interval of
height `C`, the relative outward cumulative weight of the angle-`θ` continuation is the original angle-shifted one,
`cumWeight κ (C + θχ)`; its relative threshold `≤ −2` is therefore the original one. (The phase enters the relative
height additively as `C + θχ + χ·0`.) -/
theorem w8_realContact_weight (C θ : ℝ) :
    cumWeightLeft κ (C + θ * chiC κ + chiC κ * 0) = cumWeightLeft κ (C + θ * chiC κ) ∧
      cumWeightRight κ (C + θ * chiC κ + chiC κ * 0) = cumWeightRight κ (C + θ * chiC κ) := by
  simp only [mul_zero, add_zero, and_self]

/-! ### Theorem 7.12D -/

/-- **Theorem 7.12D**, the exposed first left side (p. 543): its height `−λ − θ₋χ`, after adding `θ₊χ`, is
`−λ + (θ₊ − θ₋)χ`, and its right outward cumulative weight is `−2 + D_θ`, `D_θ = (θ₊ − θ₋)χ/λ`. -/
theorem thm712D_exposed_weight (hκ : 0 < κ) (θm θp : ℝ) :
    (-sleLambda κ - θm * chiC κ) + θp * chiC κ = -sleLambda κ + (θp - θm) * chiC κ ∧
      cumWeightRight κ ((-sleLambda κ - θm * chiC κ) + θp * chiC κ) = -2 + angleGap κ θm θp := by
  have hl := sleLambda_ne_zero hκ
  refine ⟨by ring, ?_⟩
  simp only [cumWeightRight, angleGap]
  field_simp
  ring

/-- **(7.12D.1)** (p. 543): the right outward cumulative weight `−2 + D_θ` of the exposed first left side is at
least `c = κ/2 − 2` exactly when `D_θ ≥ κ/2`. -/
theorem thm712D_one (hκ : 0 < κ) (θm θp : ℝ) :
    κ / 2 - 2 ≤ cumWeightRight κ ((-sleLambda κ - θm * chiC κ) + θp * chiC κ) ↔
      κ / 2 ≤ angleGap κ θm θp := by
  rw [(thm712D_exposed_weight hκ θm θp).2]
  constructor <;> intro h <;> linarith

/-- `D_θ ≥ κ/2` forces `θ₋ < θ₊` (`0 < κ < 4`): the critical condition orders the angles. -/
theorem lt_of_half_le_angleGap (hκ : 0 < κ) (hκ4 : κ < 4) {θm θp : ℝ}
    (h : κ / 2 ≤ angleGap κ θm θp) : θm < θp := by
  by_contra hle
  have hle' : θp - θm ≤ 0 := by linarith [not_lt.1 hle]
  have hc := chiC_pos hκ hκ4
  have hl := sleLambda_pos hκ
  have : angleGap κ θm θp ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hle' hc.le) hl.le
  linarith

/-! ### The critical exclusion after a crossing -/

/-- The critical angle `πκ/(4 − κ)` is less than `π` exactly when `κ < 2` (`κ < 4`). -/
theorem critical_lt_pi_iff (hκ4 : κ < 4) : π * κ / (4 - κ) < π ↔ κ < 2 := by
  have h4 : 0 < 4 - κ := sub_pos.2 hκ4
  rw [div_lt_iff₀ h4]
  constructor
  · intro h
    nlinarith [pi_pos]
  · intro h
    nlinarith [pi_pos]

/-- **Critical exclusion after a crossing** (p. 544): the hypotheses `θ₂ < θ₁ < θ₂ + π` and
`(θ₁ − θ₂)χ/λ ≥ κ/2` are compatible only for `κ < 2`, by the critical angle `πκ/(4 − κ)` (p. 544). -/
theorem kappa_lt_two_of_critical_crossing (hκ : 0 < κ) (hκ4 : κ < 4) {θ₁ θ₂ : ℝ}
    (hθ : θ₁ < θ₂ + π) (hcrit : κ / 2 ≤ (θ₁ - θ₂) * chiC κ / sleLambda κ) : κ < 2 := by
  have h := (Theorem15.half_le_mul_chiC_div_sleLambda_iff hκ hκ4 (θ₁ - θ₂)).1 hcrit
  exact (critical_lt_pi_iff hκ4).1 (lt_of_le_of_lt h (by linarith))

end Supp10

end InteractingSLE
