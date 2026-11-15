/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowWords
import InteractingSLE.Spec.Supplement.S7Weights

/-!
# Supplement §8: the weight and height algebra of the boundary-frame lemmas

Packet PROVE-SUPP8 (specification supplement §8, `source/spec/p481-528.md` L704–L1120, pp. 510–527). Throughout
`0 < κ < 4`, `k = κ' = 16/κ > 4`, `λ = sleLambda κ`, `λ' = Λ = sleLambda κ'`, `χ = chiC κ`, `A = counterflowA κ =
k/2 − 2`, `d = k/2 − 4`, `c = k/2 − 2` (counterflow), `c_κ = κ/2 − 2`, `d_κ = κ/2 − 4` (flow). A flow (parameter `κ`)
sees a boundary height `H` (with its angle `θ` absorbed, `H + θχ`) as `cumWeightLeft κ (H + θχ) = −(H + θχ)/λ − 1`
on its left and `cumWeightRight κ (H + θχ)` on its right; a counterflow sees `F` as `cumWeightLeft κ' F = −F/λ' − 1`
and `cumWeightRight κ' F = F/λ' − 1`.

* **GB2, consequence** (p. 513) and **GB4** (pp. 514–516): the pocket with incoming angles `+π/2` (left) and
  `−π/2` (right) has flow heights `λ'` on `ℝ₋` and `−λ'` on `ℝ₊` (`λ − (π/2)χ = λ'`); after the inversion with the
  compatible inverse lift and centering by `−πχ`, its heights are `λ' − πχ = −λ'(d + 1)` and `−λ' + πχ = λ'(d + 1)`,
  i.e. the initial word is exactly `(d, d)` (`gb4_word`, `gb2_initial_word`).
* **GB3** (p. 513): `q_∞ = k − 6 − 2d = 2`, outer left cumulative weight `d + 2 = c`, admissibility, `d < c`
  (`gb3_weights`).
* **GB6** (p. 518): the terminal counterflow partial sums `S_L = k/4 + (1 − θ/π)A − 1`, `S_R = k/4 + (1 + θ/π)A − 1`
  of an exposed angle-`θ` piece, from its heights (`gb6_SL_eq`, `gb6_SR_eq`), and `S_L − c = (1/2 − θ/π)A`,
  `S_R − c = (1/2 + θ/π)A`, both `≥ 0` for `θ ∈ [−π/2, π/2]` (`gb6_c_le_SL`, `gb6_c_le_SR`).
* **GB7** (pp. 521–522): an old side of angle `θᵢ` gets the new cumulative weight `±(θ − θᵢ)χ/λ`
  (`gb7_old_right`, `gb7_old_left`), at least `c_κ = −πχ/λ > −2` when `|θ − θᵢ| ≤ π` (`gb7_old_weight_ge`), and an
  exterior junction with admissible weight `r > −2` gets more than `d_κ` (`gb7_junction`).
* **GB7a, GB8** (p. 523): `c_κ > d_κ`, `κ − 4 > d_κ`, the strip upper height `−λ(1 + (κ − 4)) − πχ = λ(1 − κ/2)` lies
  in `(−λ, λ)` (`gb8_upper_height`, `gb8_upper_height_mem`); the relevance paragraph: an original piece with
  counterflow partial sum `S` gives every flow angle `θ ∈ [−π/2, π/2]` the partial sum
  `r_θ ≥ −2 + (κ/4)(S − d)` (`gb8_relevance_left`, `gb8_relevance_right`).
* **GB9** (pp. 524–526): the far heights `−λ' + (θ + π)χ`, `λ' + (θ − π)χ` give the totals `(κ − 4, c_κ)` at
  `θ = π/2` and `(c_κ, κ − 4)` at `θ = −π/2` (`gb9_far_weights_half_pi`, `gb9_far_weights_neg_half_pi`);
  `M = πχ/λ = 2 − κ/2 < 2` and the angle-change partial sums `(θ − θ')χ/λ` have modulus at most `M`
  (`gb9_M_lt_two`, `gb9_abs_angleGap_le`).
-/

set_option autoImplicit false

noncomputable section

open Real
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Supp8

open Sec4 Sec7 Supp7

variable {κ : ℝ}

/-! ### GB2 and GB4: the `(d, d)` pocket word -/

/-- **GB4**: the own right-side flow germ of angle `π/2` is `λ − (π/2)χ = λ'`. -/
theorem gb4_own_germ (hκ : 0 < κ) : sleLambda κ - π / 2 * chiC κ = sleLambda (16 / κ) :=
  (sleLambda_sixteen_div_eq_sub hκ).symm

/-- **GB4**: the pocket coordinate word for incoming angles `+π/2` (left side, `ℝ₋`) and `−π/2` (right side, `ℝ₊`) is
`λ'` on `ℝ₋` and `−λ'` on `ℝ₊`. -/
theorem gb4_pocket_heights (hκ : 0 < κ) {x : ℝ} :
    cf92Lower κ (-(π / 2)) (π / 2) x = if x < 0 then sleLambda (16 / κ) else -sleLambda (16 / κ) := by
  rw [cf92Lower, sleLambda_sixteen_div_eq_sub hκ]
  split_ifs <;> ring

/-- **GB4**, the `ψ` chart: the inversion `I(z) = −1/z` with the compatible inverse lift `2πi − 2 Log w` gives the
`h`-heights `−λ'` on `ℝ₋` and `λ' − 2πχ` on `ℝ₊`; centering, `λ' − πχ = −λ'(d + 1)` and `−λ' + πχ = λ'(d + 1)` with
`d = κ'/2 − 4`. -/
theorem gb4_centered_heights (hκ : 0 < κ) :
    sleLambda (16 / κ) - π * chiC κ = -sleLambda (16 / κ) * ((16 / κ / 2 - 4) + 1) ∧
      -sleLambda (16 / κ) + π * chiC κ = sleLambda (16 / κ) * ((16 / κ / 2 - 4) + 1) := by
  have h := pi_mul_chiC_eq_mul_sleLambda_sixteen_div hκ
  constructor <;> rw [h] <;> ring

/-- **GB4 / GB2**, the full word: the centred reversed-coordinate field of the pocket with incoming angles `+π/2`
(left) and `−π/2` (right) has heights `−λ'(1 + d)` on `ℝ₋` and `λ'(1 + d)` on `ℝ₊`, `d = κ'/2 − 4`: the
`SLE_{κ'}(d; d)` word. (Aux. lemma 120's (IF9.1) with `θ₁ = −π/2`, `θ₂ = π/2`.) -/
theorem gb4_word (hκ : 0 < κ) {x : ℝ} (hx : x ≠ 0) :
    if91Heights κ (-(π / 2)) (π / 2) (-(π * chiC κ)) x =
      if x < 0 then -sleLambda (16 / κ) * (1 + (16 / κ / 2 - 4))
      else sleLambda (16 / κ) * (1 + (16 / κ / 2 - 4)) := by
  have hd : counterflowA κ - 2 = 16 / κ / 2 - 4 := by rw [counterflowA]; ring
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · rw [if91Heights_centered_neg hκ hlt, cf95RhoL_neg_half_pi, hd, ite_eq_left hlt]
  · rw [if91Heights_centered_pos hκ hgt, cf95RhoR_half_pi, hd, ite_eq_right (not_lt.2 hgt.le)]

/-- **GB2, consequence for the nonfilling two-frontier word**: for angles `−π/2, +π/2` the initial counterflow word
is exactly `(d, d)`, `d = κ'/2 − 4`, the seed weights of Aux. lemma 120 / (CF9.5). -/
theorem gb2_initial_word (κ : ℝ) :
    cf95RhoL κ (-(π / 2)) = 16 / κ / 2 - 4 ∧ cf95RhoR κ (π / 2) = 16 / κ / 2 - 4 := by
  rw [cf95RhoL_neg_half_pi, cf95RhoR_half_pi, counterflowA]
  constructor <;> ring

/-! ### GB3: the target-changed word -/

/-- **GB3**, weights: with `d = k/2 − 4` and `c = k/2 − 2`, the old target gets `q_∞ = k − 6 − 2d = 2`, the outer left
cumulative weight is `d + 2 = c`, the inner seed weight satisfies `d < c`, and for `k > 4` all side partial sums
`d, d + 2` exceed `−2`. -/
theorem gb3_weights {k : ℝ} (hk : 4 < k) :
    k - 6 - 2 * (k / 2 - 4) = 2 ∧ (k / 2 - 4) + 2 = k / 2 - 2 ∧ k / 2 - 4 < k / 2 - 2 ∧
      -2 < k / 2 - 4 ∧ -2 < (k / 2 - 4) + 2 := by
  refine ⟨by ring, by ring, by linarith, by linarith, by linarith⟩

/-! ### GB6: the terminal counterflow partial sums -/

/-- **GB6**, `S_L`: the right side of an exposed flow piece of angle `θ` (`h`-height `λ − θχ`, no inversion shift)
becomes, after centering `F = −h − πχ`, a left counterflow tail with partial sum
`S_L = cumWeightLeft κ' (−(λ − θχ) − πχ) = k/4 + (1 − θ/π)A − 1`. -/
theorem gb6_SL_eq (hκ : 0 < κ) (θ : ℝ) :
    cumWeightLeft (16 / κ) (-(sleLambda κ - θ * chiC κ) - π * chiC κ) =
      16 / κ / 4 + (1 - θ / π) * counterflowA κ - 1 := by
  have hl := (sleLambda_sixteen_div_pos hκ).ne'
  have hπ := Real.pi_pos.ne'
  rw [cumWeightLeft, sleLambda_eq_of_sixteen_div hκ, chiC_eq_of_sixteen_div hκ, counterflowA]
  field_simp
  ring

/-- **GB6**, `S_R`: the left side (`h`-height `−λ − θχ`, inversion shift `−2πχ`) becomes a right counterflow tail with
partial sum `S_R = cumWeightRight κ' (−(−λ − θχ − 2πχ) − πχ) = k/4 + (1 + θ/π)A − 1`. -/
theorem gb6_SR_eq (hκ : 0 < κ) (θ : ℝ) :
    cumWeightRight (16 / κ) (-(-sleLambda κ - θ * chiC κ - 2 * π * chiC κ) - π * chiC κ) =
      16 / κ / 4 + (1 + θ / π) * counterflowA κ - 1 := by
  have hl := (sleLambda_sixteen_div_pos hκ).ne'
  have hπ := Real.pi_pos.ne'
  rw [cumWeightRight, sleLambda_eq_of_sixteen_div hκ, chiC_eq_of_sixteen_div hκ, counterflowA]
  field_simp
  ring

/-- **GB6**: `S_L − c = (1/2 − θ/π)A` with `c = k/2 − 2`. -/
theorem gb6_SL_sub (κ θ : ℝ) :
    16 / κ / 4 + (1 - θ / π) * counterflowA κ - 1 - (16 / κ / 2 - 2) = (1 / 2 - θ / π) * counterflowA κ := by
  rw [counterflowA]; ring

/-- **GB6**: `S_R − c = (1/2 + θ/π)A`. -/
theorem gb6_SR_sub (κ θ : ℝ) :
    16 / κ / 4 + (1 + θ / π) * counterflowA κ - 1 - (16 / κ / 2 - 2) = (1 / 2 + θ / π) * counterflowA κ := by
  rw [counterflowA]; ring

/-- **GB6**: `S_L ≥ c` for `θ ≤ π/2`. -/
theorem gb6_c_le_SL (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ : θ ≤ π / 2) :
    16 / κ / 2 - 2 ≤ 16 / κ / 4 + (1 - θ / π) * counterflowA κ - 1 := by
  have hA := (counterflowA_pos hκ hκ4).le
  have h1 : 0 ≤ 1 / 2 - θ / π := by
    rw [sub_nonneg, div_le_iff₀ Real.pi_pos]; linarith
  linarith [gb6_SL_sub κ θ, mul_nonneg h1 hA]

/-- **GB6**: `S_R ≥ c` for `θ ≥ −π/2`. -/
theorem gb6_c_le_SR (hκ : 0 < κ) (hκ4 : κ < 4) {θ : ℝ} (hθ : -(π / 2) ≤ θ) :
    16 / κ / 2 - 2 ≤ 16 / κ / 4 + (1 + θ / π) * counterflowA κ - 1 := by
  have hA := (counterflowA_pos hκ hκ4).le
  have h1 : 0 ≤ 1 / 2 + θ / π := by
    have : -(1 / 2) ≤ θ / π := by rw [le_div_iff₀ Real.pi_pos]; linarith
    linarith
  linarith [gb6_SR_sub κ θ, mul_nonneg h1 hA]

/-! ### GB7 and GB7a: old sides and exterior junctions -/

/-- **GB7**: an old exposed right side of angle `θᵢ` (height `λ − θᵢχ`) has new cumulative weight `(θ − θᵢ)χ/λ`. -/
theorem gb7_old_right (hκ : 0 < κ) (θᵢ θ : ℝ) :
    cumWeightRight κ (sleLambda κ - θᵢ * chiC κ + θ * chiC κ) = angleGap κ θᵢ θ := by
  have := sleLambda_ne_zero hκ
  rw [cumWeightRight, angleGap]
  field_simp
  ring

/-- **GB7**: an old exposed left side of angle `θᵢ` (height `−λ − θᵢχ`) has new cumulative weight `−(θ − θᵢ)χ/λ`. -/
theorem gb7_old_left (hκ : 0 < κ) (θᵢ θ : ℝ) :
    cumWeightLeft κ (-sleLambda κ - θᵢ * chiC κ + θ * chiC κ) = -angleGap κ θᵢ θ := by
  have := sleLambda_ne_zero hκ
  rw [cumWeightLeft, angleGap]
  field_simp
  ring

/-- `|(θ − θ')χ/λ| ≤ πχ/λ` when `|θ − θ'| ≤ π`. -/
theorem abs_angleGap_le (hκ : 0 < κ) (hκ4 : κ < 4) {θ θ' : ℝ} (h : |θ - θ'| ≤ π) :
    |angleGap κ θ' θ| ≤ π * chiC κ / sleLambda κ := by
  have hχ := chiC_pos hκ hκ4
  have hl := sleLambda_pos hκ
  rw [angleGap, abs_div, abs_mul, abs_of_pos hχ, abs_of_pos hl]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h hχ.le) hl.le

/-- **GB7**: both new old-side weights `±(θ − θᵢ)χ/λ` are at least `−πχ/λ = c_κ = κ/2 − 2 > −2` when the angles lie in
an interval of width at most `π`. -/
theorem gb7_old_weight_ge (hκ : 0 < κ) (hκ4 : κ < 4) {θᵢ θ : ℝ} (h : |θ - θᵢ| ≤ π) :
    κ / 2 - 2 ≤ angleGap κ θᵢ θ ∧ κ / 2 - 2 ≤ -angleGap κ θᵢ θ ∧ -2 < κ / 2 - 2 := by
  have hb := abs_le.1 (abs_angleGap_le hκ hκ4 h)
  have hc : -(π * chiC κ / sleLambda κ) = κ / 2 - 2 := by
    rw [← neg_div]; exact neg_pi_mul_chiC_div_sleLambda hκ
  refine ⟨by linarith [hb.1], by linarith [hb.2], by linarith⟩

/-- **GB7**, exterior junctions: if the cumulative weight `r` in force at an old admissible real contact satisfies
`r > −2`, the new outward cumulative weight `r ± (θ − θᵢ)χ/λ` exceeds `−2 − πχ/λ = d_κ = κ/2 − 4`. -/
theorem gb7_junction (hκ : 0 < κ) (hκ4 : κ < 4) {θᵢ θ r : ℝ} (h : |θ - θᵢ| ≤ π) (hr : -2 < r) :
    κ / 2 - 4 < r + angleGap κ θᵢ θ ∧ κ / 2 - 4 < r - angleGap κ θᵢ θ := by
  obtain ⟨h1, h2, -⟩ := gb7_old_weight_ge hκ hκ4 h
  constructor <;> linarith

/-- **GB7a / G12**: `c_κ = κ/2 − 2 > d_κ = κ/2 − 4`. -/
theorem gb7a_c_gt_d (κ : ℝ) : κ / 2 - 4 < κ / 2 - 2 := by linarith

/-! ### GB8: the critical far-side word -/

/-- **GB8**: `κ − 4 > d_κ` (G12 excludes an exact landing at `x₋`) for `κ > 0`. -/
theorem gb8_left_total_gt (hκ : 0 < κ) : κ / 2 - 4 < κ - 4 := by linarith

/-- **GB8**: the strip map `Φ(z) = (1/π) Log((z − a₋)/(−a₋))` turns the left total `κ − 4` (height
`−λ(1 + (κ − 4))`) into the upper strip height `−λ(1 + (κ − 4)) − πχ = λ(1 − κ/2)`. -/
theorem gb8_upper_height (hκ : 0 < κ) :
    -sleLambda κ * (1 + (κ - 4)) - π * chiC κ = sleLambda κ * (1 - κ / 2) := by
  rw [pi_mul_chiC hκ]; ring

/-- **GB8**: `λ(1 − κ/2) ∈ (−λ, λ)` for `0 < κ < 4`. -/
theorem gb8_upper_height_mem (hκ : 0 < κ) (hκ4 : κ < 4) :
    -sleLambda κ < sleLambda κ * (1 - κ / 2) ∧ sleLambda κ * (1 - κ / 2) < sleLambda κ := by
  have hl := sleLambda_pos hκ
  constructor <;> nlinarith

/-- **GB8, relevance for strictly nonfilling counterflow data** (left side): an original piece on which the
counterflow has partial sum `S` carries, in the reverse-target chart, the height `−λ'(1 + S) + πχ`; an angle
`θ ≤ π/2` flow sees the partial sum `r_θ ≥ −2 + (κ/4)(S − d)`, `d = κ'/2 − 4`, which exceeds `−2` when `S > d`. -/
theorem gb8_relevance_left (hκ : 0 < κ) (hκ4 : κ < 4) {S θ : ℝ} (hθ : θ ≤ π / 2) :
    -2 + κ / 4 * (S - (16 / κ / 2 - 4)) ≤
      cumWeightLeft κ (-sleLambda (16 / κ) * (1 + S) + π * chiC κ + θ * chiC κ) := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  have hθχ : θ * chiC κ ≤ π / 2 * chiC κ := mul_le_mul_of_nonneg_right hθ hχ.le
  rw [cumWeightLeft, le_sub_iff_add_le, le_div_iff₀ hl, sleLambda_sixteen_div hκ]
  have h := pi_mul_chiC hκ
  have e : κ / 4 * (16 / κ / 2 - 4) = 2 - κ := by field_simp; ring
  nlinarith [e]

/-- **GB8, relevance** (right side): the height `λ'(1 + S) − πχ` gives an angle `θ ≥ −π/2` flow the partial sum
`r_θ ≥ −2 + (κ/4)(S − d)`. -/
theorem gb8_relevance_right (hκ : 0 < κ) (hκ4 : κ < 4) {S θ : ℝ} (hθ : -(π / 2) ≤ θ) :
    -2 + κ / 4 * (S - (16 / κ / 2 - 4)) ≤
      cumWeightRight κ (sleLambda (16 / κ) * (1 + S) - π * chiC κ + θ * chiC κ) := by
  have hl := sleLambda_pos hκ
  have hχ := chiC_pos hκ hκ4
  have hθχ : -(π / 2) * chiC κ ≤ θ * chiC κ := mul_le_mul_of_nonneg_right hθ hχ.le
  rw [cumWeightRight, le_sub_iff_add_le, le_div_iff₀ hl, sleLambda_sixteen_div hκ]
  have h := pi_mul_chiC hκ
  have e : κ / 4 * (16 / κ / 2 - 4) = 2 - κ := by field_simp; ring
  nlinarith [e]

/-- **GB8, relevance**: `S > d` makes `−2 + (κ/4)(S − d) > −2`. -/
theorem gb8_relevance_gt (hκ : 0 < κ) {S : ℝ} (hS : 16 / κ / 2 - 4 < S) :
    -2 < -2 + κ / 4 * (S - (16 / κ / 2 - 4)) := by
  have : 0 < κ / 4 * (S - (16 / κ / 2 - 4)) := mul_pos (by linarith) (by linarith)
  linarith

/-! ### GB9: far heights and the Abel constant -/

/-- **GB9**: at `θ = π/2` the far heights `−λ' + (θ + π)χ`, `λ' + (θ − π)χ` give the totals `(κ − 4, c_κ)`. -/
theorem gb9_far_weights_half_pi (hκ : 0 < κ) :
    cumWeightLeft κ (-sleLambda (16 / κ) + (π / 2 + π) * chiC κ) = κ - 4 ∧
      cumWeightRight κ (sleLambda (16 / κ) + (π / 2 - π) * chiC κ) = κ / 2 - 2 := by
  have hl := sleLambda_ne_zero hκ
  have h := pi_mul_chiC hκ
  have e1 : (π / 2 + π) * chiC κ = 3 / 2 * (π * chiC κ) := by ring
  have e2 : (π / 2 - π) * chiC κ = -(1 / 2) * (π * chiC κ) := by ring
  rw [cumWeightLeft, cumWeightRight, sleLambda_sixteen_div hκ, e1, e2, h]
  constructor <;> field_simp <;> ring

/-- **GB9**: at `θ = −π/2` the far totals are reflected, `(c_κ, κ − 4)`. -/
theorem gb9_far_weights_neg_half_pi (hκ : 0 < κ) :
    cumWeightLeft κ (-sleLambda (16 / κ) + (-(π / 2) + π) * chiC κ) = κ / 2 - 2 ∧
      cumWeightRight κ (sleLambda (16 / κ) + (-(π / 2) - π) * chiC κ) = κ - 4 := by
  have hl := sleLambda_ne_zero hκ
  have h := pi_mul_chiC hκ
  have e1 : (-(π / 2) + π) * chiC κ = 1 / 2 * (π * chiC κ) := by ring
  have e2 : (-(π / 2) - π) * chiC κ = -(3 / 2) * (π * chiC κ) := by ring
  rw [cumWeightLeft, cumWeightRight, sleLambda_sixteen_div hκ, e1, e2, h]
  constructor <;> field_simp <;> ring

/-- **GB9**: `M = πχ/λ = 2 − κ/2 ∈ (0, 2)`, so `[−M, M] ⊂ (−2, ∞)`. -/
theorem gb9_M_lt_two (hκ : 0 < κ) (hκ4 : κ < 4) :
    π * chiC κ / sleLambda κ = 2 - κ / 2 ∧ 0 < π * chiC κ / sleLambda κ ∧ π * chiC κ / sleLambda κ < 2 := by
  rw [pi_mul_chiC_div_sleLambda hκ]
  refine ⟨rfl, by linarith, by linarith⟩

/-- **GB9**: for two angles in `[−π/2, π/2]` the telescoped angle-change partial sum `(θ − θ')χ/λ` has modulus at
most `M = πχ/λ`. -/
theorem gb9_abs_angleGap_le (hκ : 0 < κ) (hκ4 : κ < 4) {θ θ' : ℝ} (hθ : θ ∈ Set.Icc (-(π / 2)) (π / 2))
    (hθ' : θ' ∈ Set.Icc (-(π / 2)) (π / 2)) :
    |angleGap κ θ' θ| ≤ π * chiC κ / sleLambda κ :=
  abs_angleGap_le hκ hκ4 (abs_le.2 ⟨by linarith [hθ.1, hθ'.2], by linarith [hθ.2, hθ'.1]⟩)

end Supp8

end InteractingSLE
