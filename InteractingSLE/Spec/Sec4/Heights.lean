/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.sleLambda
import QuantumZipper.Common.Basic

/-!
# Critical heights in the strip: parameter identities (§4, §4.1)

Packet PROVE-SEC4-A (specification §4 opening and §4.1, `source/spec/p097-144.md` L154–L470, pp. 102–115).

The algebraic content of §4.1. Throughout, `k > 0` is the signed parameter of the proofs of Lemmas 4.3,
4.5 and Aux. lemmas 21–22, with `Λ = sleLambda k = π/√k` and `X = chiC k = 2/√k − √k/2`; the two applications
are `(k, Λ, X) = (κ, λ, χ)` and `(κ', λ', −χ)` with `κ' = 16/κ` (`sleLambda_sixteen_div`, `chiC_sixteen_div`).

* (4.1)–(4.3): `two_pi_mul_chiC_eq`, `sleLambda_sixteen_div_eq_sub`, `two_pi_mul_chiC_eq_four_sub_mul`,
  `two_pi_mul_chiC_eq_sixteen_div_sub_mul`;
* the basic conversion `π X / Λ = 2 − k/2` (`pi_mul_chiC_div_sleLambda`), hence `Λ − π X = (1 + c) Λ` with
  `c = k/2 − 2` (Lemma 4.5's identity, `sleLambda_sub_pi_mul_chiC`);
* Figure 4.1: the critical weight `ρ₀ = κ/2 − 2` corresponds to the upper height `−λ`;
* Lemma 4.3: the endpoint charges (HB1) and the two continuation-threshold criteria
  (`neg_two_lt_rhoLeft_iff`, `neg_two_lt_rhoRight_iff`), and the strict middle range `|q₊ − q₋| < 2 ↔ |a| < Λ`;
* Remark 4.4 (`neg_sleLambda_add_pi_mul_chiC`, `exists_branch_height_iff`);
* the height-to-weight conversion of Lemma 4.5 and Aux. lemma 22 (`le_cumWeightLeft_iff`,
  `le_cumWeightRight_iff`);
* the parameter-`κ'` remark after Figure 4.3;
* (UC13): the classification of the upper heights in the stopped counterflow chart of Proposition 5.1
  (`uc13_heights`, `uc13_first_exit_alternative`).
-/

set_option autoImplicit false

noncomputable section

open Real

namespace InteractingSLE

namespace Sec4

open QuantumZipper (chiC)

/-! ### Basic positivity and the conversion `π X / Λ = 2 − k/2` -/

theorem sleLambda_pos {k : ℝ} (hk : 0 < k) : 0 < sleLambda k :=
  div_pos pi_pos (sqrt_pos.2 hk)

theorem sleLambda_ne_zero {k : ℝ} (hk : 0 < k) : sleLambda k ≠ 0 := (sleLambda_pos hk).ne'

/-- `π/√k · √k = π`. -/
theorem sleLambda_mul_sqrt {k : ℝ} (hk : 0 < k) : sleLambda k * sqrt k = π := by
  have := (sqrt_pos.2 hk).ne'
  simp only [sleLambda]
  field_simp

/-- `π X = (2 − k/2) Λ`: the field gap of a half turn, in units of `Λ`. -/
theorem pi_mul_chiC {k : ℝ} (hk : 0 < k) : π * chiC k = (2 - k / 2) * sleLambda k := by
  have hs := sqrt_pos.2 hk
  have hsq : sqrt k ^ 2 = k := sq_sqrt hk.le
  simp only [chiC, sleLambda]
  field_simp
  rw [hsq]

/-- `π X / Λ = 2 − k/2`. -/
theorem pi_mul_chiC_div_sleLambda {k : ℝ} (hk : 0 < k) : π * chiC k / sleLambda k = 2 - k / 2 := by
  rw [pi_mul_chiC hk, mul_div_assoc, div_self (sleLambda_ne_zero hk), mul_one]

/-- `−π X / Λ = k/2 − 2 = c`. -/
theorem neg_pi_mul_chiC_div_sleLambda {k : ℝ} (hk : 0 < k) :
    -(π * chiC k) / sleLambda k = k / 2 - 2 := by
  rw [neg_div, pi_mul_chiC_div_sleLambda hk]; ring

/-- Lemma 4.5's identity `Λ − π X = (1 + c) Λ`, `c = k/2 − 2`. -/
theorem sleLambda_sub_pi_mul_chiC {k : ℝ} (hk : 0 < k) :
    sleLambda k - π * chiC k = (1 + (k / 2 - 2)) * sleLambda k := by
  rw [pi_mul_chiC hk]; ring

/-- `−Λ + π X = −(1 + c) Λ`. -/
theorem neg_sleLambda_add_pi_mul_chiC' {k : ℝ} (hk : 0 < k) :
    -sleLambda k + π * chiC k = -((1 + (k / 2 - 2)) * sleLambda k) := by
  rw [pi_mul_chiC hk]; ring

/-! ### The identities (4.1)–(4.3) -/

/-- `χ > 0` for `κ < 4`. -/
theorem chiC_pos {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < chiC κ := by
  have h := pi_mul_chiC hκ
  have hl := sleLambda_pos hκ
  have : 0 < π * chiC κ := by rw [h]; exact mul_pos (by linarith) hl
  exact pos_of_mul_pos_right this pi_pos.le

/-- (4.1): `λ' = π/√κ' = π√κ/4 = (κ/4) λ` for `κ' = 16/κ`. -/
theorem sleLambda_sixteen_div {κ : ℝ} (hκ : 0 < κ) :
    sleLambda (16 / κ) = κ / 4 * sleLambda κ := by
  have hs := sqrt_pos.2 hκ
  have h16 : sqrt (16 / κ) = 4 / sqrt κ := by
    rw [sqrt_div' 16 hκ.le, show (16 : ℝ) = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  have hsq : sqrt κ ^ 2 = κ := sq_sqrt hκ.le
  simp only [sleLambda, h16]
  field_simp
  rw [hsq]

/-- `χ(16/κ) = −χ(κ)`: the counterflow parameter reverses the sign of `χ` (the application
`(k, Λ, X) = (κ', λ', −χ)`). -/
theorem chiC_sixteen_div {κ : ℝ} (hκ : 0 < κ) : chiC (16 / κ) = -chiC κ := by
  have hs := sqrt_pos.2 hκ
  have h16 : sqrt (16 / κ) = 4 / sqrt κ := by
    rw [sqrt_div' 16 hκ.le, show (16 : ℝ) = 4 ^ 2 by norm_num, sqrt_sq (by norm_num)]
  simp only [chiC, h16]
  field_simp
  ring

/-- (4.2): `2πχ = 4(λ − λ')`. -/
theorem two_pi_mul_chiC_eq {κ : ℝ} (hκ : 0 < κ) :
    2 * π * chiC κ = 4 * (sleLambda κ - sleLambda (16 / κ)) := by
  rw [sleLambda_sixteen_div hκ, mul_assoc, pi_mul_chiC hκ]; ring

/-- (4.2): `λ' = λ − (π/2) χ`. -/
theorem sleLambda_sixteen_div_eq_sub {κ : ℝ} (hκ : 0 < κ) :
    sleLambda (16 / κ) = sleLambda κ - π / 2 * chiC κ := by
  have := two_pi_mul_chiC_eq hκ
  linarith

/-- (4.3): `2πχ = (4 − κ) λ`. -/
theorem two_pi_mul_chiC_eq_four_sub_mul {κ : ℝ} (hκ : 0 < κ) :
    2 * π * chiC κ = (4 - κ) * sleLambda κ := by
  rw [mul_assoc, pi_mul_chiC hκ]; ring

/-- (4.3): `2πχ = (κ' − 4) λ'`. -/
theorem two_pi_mul_chiC_eq_sixteen_div_sub_mul {κ : ℝ} (hκ : 0 < κ) :
    2 * π * chiC κ = (16 / κ - 4) * sleLambda (16 / κ) := by
  rw [sleLambda_sixteen_div hκ, two_pi_mul_chiC_eq_four_sub_mul hκ]
  field_simp
  ring

/-- `λ' < λ` for `0 < κ < 4` (4.1). -/
theorem sleLambda_sixteen_div_lt {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    sleLambda (16 / κ) < sleLambda κ := by
  rw [sleLambda_sixteen_div hκ]
  have := sleLambda_pos hκ
  nlinarith

/-- `λ' > 0`. -/
theorem sleLambda_sixteen_div_pos {κ : ℝ} (hκ : 0 < κ) : 0 < sleLambda (16 / κ) :=
  sleLambda_pos (div_pos (by norm_num) hκ)

/-- A `θ χ` gap in boundary values corresponds to the weight `ρ = θ/(2π) (4 − κ)` (after (4.3)). -/
theorem theta_mul_chiC_eq {κ : ℝ} (hκ : 0 < κ) (θ : ℝ) :
    θ * chiC κ = θ / (2 * π) * (4 - κ) * sleLambda κ := by
  have h := two_pi_mul_chiC_eq_four_sub_mul hκ
  have hπ := pi_pos.ne'
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (by positivity), mul_assoc θ (4 - κ), ← h]
  ring

/-! ### Figure 4.1 and Lemma 4.3 -/

/-- Figure 4.1: with the critical weight `ρ₀ = κ/2 − 2`, the critical upper height is
`−(1 + ρ₀) λ − π χ = −λ`. -/
theorem fig41_critical_height {k : ℝ} (hk : 0 < k) :
    -(1 + (k / 2 - 2)) * sleLambda k - π * chiC k = -sleLambda k := by
  rw [pi_mul_chiC hk]; ring

/-- The upper strip height `a` and the weight `ρ` of the force point at the left strip end in
Figure 4.1 (`a = −(1 + ρ) λ − π χ`): `ρ < κ/2 − 2 ↔ a > −λ`. -/
theorem fig41_lt_iff {k ρ : ℝ} (hk : 0 < k) :
    ρ < k / 2 - 2 ↔ -sleLambda k < -(1 + ρ) * sleLambda k - π * chiC k := by
  rw [pi_mul_chiC hk]
  have hl := sleLambda_pos hk
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- (HB1): the total endpoint charge at the right end, `q₊ = k/2 − 3 + a/Λ`. -/
def endChargeRight (k a : ℝ) : ℝ := k / 2 - 3 + a / sleLambda k

/-- (HB1): the total endpoint charge at the left end, `q₋ = k/2 − 3 − a/Λ`. -/
def endChargeLeft (k a : ℝ) : ℝ := k / 2 - 3 - a / sleLambda k

/-- (HB1): the upper boundary maps (under `z ↦ 1 − e^{−z}`) to `(1, ∞)` with transformed value
`a − π X`, and this equals `(1 + q₊) Λ`. -/
theorem sub_pi_mul_chiC_eq_endChargeRight {k : ℝ} (hk : 0 < k) (a : ℝ) :
    a - π * chiC k = (1 + endChargeRight k a) * sleLambda k := by
  have hl := sleLambda_ne_zero hk
  simp only [endChargeRight]
  rw [pi_mul_chiC hk]
  field_simp
  ring

/-- `q₊ + q₋ = k − 6`. -/
theorem endChargeRight_add_endChargeLeft (k a : ℝ) :
    endChargeRight k a + endChargeLeft k a = k - 6 := by
  simp only [endChargeRight, endChargeLeft]; ring

/-- `|q₊ − q₋| = 2 |a| / Λ`. -/
theorem abs_endCharge_sub {k : ℝ} (hk : 0 < k) (a : ℝ) :
    |endChargeRight k a - endChargeLeft k a| = 2 * |a| / sleLambda k := by
  have hl := sleLambda_pos hk
  simp only [endChargeRight, endChargeLeft]
  rw [show k / 2 - 3 + a / sleLambda k - (k / 2 - 3 - a / sleLambda k) = 2 * a / sleLambda k by ring,
    abs_div, abs_mul, abs_of_pos hl, abs_two]

/-- The hypothesis of Zhan's strip endpoint theorem, `|q₊ − q₋| < 2`, is exactly the middle range
`−Λ < a < Λ` of Lemma 4.3. -/
theorem abs_endCharge_sub_lt_two_iff {k : ℝ} (hk : 0 < k) (a : ℝ) :
    |endChargeRight k a - endChargeLeft k a| < 2 ↔ -sleLambda k < a ∧ a < sleLambda k := by
  have hl := sleLambda_pos hk
  rw [abs_endCharge_sub hk, div_lt_iff₀ hl, ← abs_lt]
  constructor <;> intro h <;> linarith

/-- Lemma 4.3, right-end target: the colliding left group's total at the first upper contact,
`ρ_left = k/2 − 3 − a/Λ = q₋`, exceeds `−2` exactly when `a < Λ − π X`. -/
theorem neg_two_lt_rhoLeft_iff {k : ℝ} (hk : 0 < k) (a : ℝ) :
    -2 < endChargeLeft k a ↔ a < sleLambda k - π * chiC k := by
  have hl := sleLambda_pos hk
  rw [sleLambda_sub_pi_mul_chiC hk]
  simp only [endChargeLeft]
  rw [show -2 < k / 2 - 3 - a / sleLambda k ↔ a / sleLambda k < k / 2 - 1 by
    constructor <;> intro h <;> linarith, div_lt_iff₀ hl]
  constructor <;> intro h <;> linarith

/-- Lemma 4.3, left-end target: `ρ_right = k/2 − 3 + a/Λ = q₊` exceeds `−2` exactly when
`a > −Λ + π X`. -/
theorem neg_two_lt_rhoRight_iff {k : ℝ} (hk : 0 < k) (a : ℝ) :
    -2 < endChargeRight k a ↔ -sleLambda k + π * chiC k < a := by
  have hl := sleLambda_pos hk
  rw [neg_sleLambda_add_pi_mul_chiC' hk]
  simp only [endChargeRight]
  rw [show -2 < k / 2 - 3 + a / sleLambda k ↔ -(k / 2 - 1) < a / sleLambda k by
    constructor <;> intro h <;> linarith, lt_div_iff₀ hl]
  constructor <;> intro h <;> linarith

/-- Lemma 4.3, first case: if `a ≤ −Λ`, the transformed upper value under `z ↦ e^{πz} − 1` (argument
`π` on the upper boundary) is `a + π X ≤ −(1 + c) Λ`. -/
theorem add_pi_mul_chiC_le_of_le_neg {k a : ℝ} (hk : 0 < k) (ha : a ≤ -sleLambda k) :
    a + π * chiC k ≤ -((1 + (k / 2 - 2)) * sleLambda k) := by
  rw [← neg_sleLambda_add_pi_mul_chiC' hk]; linarith

/-- Lemma 4.3, the reflected case: if `a ≥ Λ`, then `a − π X ≥ (1 + c) Λ`. -/
theorem le_sub_pi_mul_chiC_of_le {k a : ℝ} (hk : 0 < k) (ha : sleLambda k ≤ a) :
    (1 + (k / 2 - 2)) * sleLambda k ≤ a - π * chiC k := by
  rw [← sleLambda_sub_pi_mul_chiC hk]; linarith

/-! ### Height-to-weight conversion (Lemma 4.5, Aux. lemma 22) -/

/-- A lower-left height `h` corresponds to the cumulative weight `−h/Λ − 1` (`forceBoundaryData`: the
value on the left of `0` is `−Λ (1 + ∑ ρ)`). -/
def cumWeightLeft (k h : ℝ) : ℝ := -h / sleLambda k - 1

/-- A lower-right height `h` corresponds to the cumulative weight `h/Λ − 1`. -/
def cumWeightRight (k h : ℝ) : ℝ := h / sleLambda k - 1

theorem cumWeightLeft_spec {k : ℝ} (hk : 0 < k) (s : ℝ) :
    cumWeightLeft k (-sleLambda k * (1 + s)) = s := by
  have := sleLambda_ne_zero hk
  simp only [cumWeightLeft]; field_simp; ring

theorem cumWeightRight_spec {k : ℝ} (hk : 0 < k) (s : ℝ) :
    cumWeightRight k (sleLambda k * (1 + s)) = s := by
  have := sleLambda_ne_zero hk
  simp only [cumWeightRight]; field_simp; ring

/-- Aux. lemma 22: a lower-left height at most `−Λ + π X` is a cumulative weight at least
`−π X / Λ = k/2 − 2`. -/
theorem le_cumWeightLeft_iff {k h : ℝ} (hk : 0 < k) :
    k / 2 - 2 ≤ cumWeightLeft k h ↔ h ≤ -sleLambda k + π * chiC k := by
  have hl := sleLambda_pos hk
  rw [neg_sleLambda_add_pi_mul_chiC' hk]
  simp only [cumWeightLeft]
  rw [show k / 2 - 2 ≤ -h / sleLambda k - 1 ↔ k / 2 - 1 ≤ -h / sleLambda k by
    constructor <;> intro h <;> linarith, le_div_iff₀ hl]
  constructor <;> intro h <;> linarith

/-- Aux. lemma 22: a lower-right height at least `Λ − π X` is a cumulative weight at least
`k/2 − 2`. -/
theorem le_cumWeightRight_iff {k h : ℝ} (hk : 0 < k) :
    k / 2 - 2 ≤ cumWeightRight k h ↔ sleLambda k - π * chiC k ≤ h := by
  have hl := sleLambda_pos hk
  rw [sleLambda_sub_pi_mul_chiC hk]
  simp only [cumWeightRight]
  rw [show k / 2 - 2 ≤ h / sleLambda k - 1 ↔ k / 2 - 1 ≤ h / sleLambda k by
    constructor <;> intro h <;> linarith, le_div_iff₀ hl]
  constructor <;> intro h <;> linarith

/-- Lemma 4.5: an upper-left height `a ≤ −Λ`, raised by `π X` (argument `+π` of the derivative),
gives a cumulative left weight at least `c`. -/
theorem le_cumWeightLeft_add_of_le_neg {k a : ℝ} (hk : 0 < k) (ha : a ≤ -sleLambda k) :
    k / 2 - 2 ≤ cumWeightLeft k (a + π * chiC k) :=
  (le_cumWeightLeft_iff hk).2 (by linarith)

/-- Lemma 4.5: an upper-right height `b ≥ Λ`, lowered by `π X` (argument `−π`), gives a cumulative
right weight at least `c`. -/
theorem le_cumWeightRight_sub_of_le {k b : ℝ} (hk : 0 < k) (hb : sleLambda k ≤ b) :
    k / 2 - 2 ≤ cumWeightRight k (b - π * chiC k) :=
  (le_cumWeightRight_iff hk).2 (by linarith)

/-! ### Remark 4.4 -/

/-- Remark 4.4: `−λ + χπ = λ (1 − κ/2)`. -/
theorem neg_sleLambda_add_pi_mul_chiC {κ : ℝ} (hκ : 0 < κ) :
    -sleLambda κ + chiC κ * π = sleLambda κ * (1 - κ / 2) := by
  rw [mul_comm (chiC κ), pi_mul_chiC hκ]; ring

/-- Remark 4.4: a height `a` with `−λ + πχ < a < λ − πχ` (both continuations possible) exists exactly
when `κ > 2`. -/
theorem exists_branch_height_iff {κ : ℝ} (hκ : 0 < κ) :
    (∃ a, -sleLambda κ + π * chiC κ < a ∧ a < sleLambda κ - π * chiC κ) ↔ 2 < κ := by
  have hl := sleLambda_pos hκ
  rw [pi_mul_chiC hκ]
  constructor
  · rintro ⟨a, h1, h2⟩
    have : -sleLambda κ + (2 - κ / 2) * sleLambda κ < sleLambda κ - (2 - κ / 2) * sleLambda κ := by
      linarith
    nlinarith
  · intro h
    exact ⟨0, by nlinarith, by nlinarith⟩

/-! ### The parameter-`κ'` remark after Figure 4.3 -/

/-- For a parameter-`κ'` coupling (`Λ = λ'`, `X = −χ`) and `0 < κ < 4`, both continuation inequalities are
automatic on the middle range: `−λ' − πχ < −λ'` and `λ' < λ' + πχ`. -/
theorem kappaPrime_middle_range {κ a : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (ha : -sleLambda (16 / κ) < a ∧ a < sleLambda (16 / κ)) :
    -sleLambda (16 / κ) + π * chiC (16 / κ) < a ∧ a < sleLambda (16 / κ) - π * chiC (16 / κ) := by
  have hχ := chiC_pos hκ hκ4
  rw [chiC_sixteen_div hκ]
  constructor <;> nlinarith [pi_pos]

/-! ### (UC13): the heights of the stopped counterflow chart of Proposition 5.1 -/

/-- (UC13), with `λ' = λ − πχ/2`: for `θ > π/2`, `a₁ = −λ' + θχ > −λ` and `a₂ = λ' + θχ > λ`. -/
theorem uc13_heights {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : π / 2 < θ) :
    -sleLambda κ < -sleLambda (16 / κ) + θ * chiC κ ∧
      sleLambda κ < sleLambda (16 / κ) + θ * chiC κ := by
  have hχ := chiC_pos hκ hκ4
  rw [sleLambda_sixteen_div_eq_sub hκ]
  constructor <;> nlinarith [pi_pos]

/-- (UC13) first-exit alternative: for upper heights `a₀, a₁ < a₂ ≤ a₃` with `a₂ > λ` (in (UC13) also
`a₀ ≤ a₁` and `a₁ > −λ`, which the case split does not use), either
the pieces with heights in `(−λ, λ)` form a nonempty span inside the two left pieces (`a₁ < λ` or
`−λ < a₀ < λ`), or every height is at least `λ`, or `a₀ ≤ −λ` and `a₁ ≥ λ` (Lemma 4.5 at their junction). -/
theorem uc13_first_exit_alternative {l a₀ a₁ a₂ a₃ : ℝ} (h23 : a₂ ≤ a₃) (ha₂ : l < a₂) :
    ((-l < a₀ ∧ a₀ < l) ∨ a₁ < l) ∨ (l ≤ a₀ ∧ l ≤ a₁ ∧ l ≤ a₂ ∧ l ≤ a₃) ∨
      (a₀ ≤ -l ∧ l ≤ a₁) := by
  by_cases h1 : a₁ < l
  · exact Or.inl (Or.inr h1)
  push Not at h1
  by_cases h0 : l ≤ a₀
  · exact Or.inr (Or.inl ⟨h0, h1, ha₂.le, ha₂.le.trans h23⟩)
  push Not at h0
  by_cases h0' : -l < a₀
  · exact Or.inl (Or.inl ⟨h0', h0⟩)
  push Not at h0'
  exact Or.inr (Or.inr ⟨h0', h1⟩)

end Sec4

end InteractingSLE
