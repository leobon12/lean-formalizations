/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowCentering

/-!
# §7.4, Aux. lemmas 120–123: the reversed pocket word, finite force words and the phase lattice

Packet PROVE-SEC7-D (specification §7.4, `source/spec/p385-432.md` L56–L171 (Aux. lemmas 120–123), L489–L516
(Lemma 7.25, (RS13.6), (7.3)), L517–L520 (Aux. lemma 131, (CS13.1)–(CS13.3)); supplement §4.2, `source/spec/p433-480.md`
L789–L823 (Lemmas 7.27–7.28)).

Throughout `0 < κ < 4`, `κ' = 16/κ`, `χ = chiC κ`, `λ = sleLambda κ`, `λ' = sleLambda κ'`, and
`A = counterflowA κ = κ'/2 − 2 > 0`, `d = A − 2 = κ'/2 − 4`. A height `H` on the left (right) of the counterflow seed
corresponds to the weight `cumWeightLeft κ' H = −H/λ' − 1` (`cumWeightRight κ' H = H/λ' − 1`), i.e. `H = −λ'(1 + ρ)`
(`H = λ'(1 + ρ)`).

* **Aux. lemma 120.** The inversion `m(z) = −1/z` with `L_m = −2 Log z`: (IF9.2) is `DerivLog.neg_derivLog_neg_inv_eq`
  (reused), `log_neg_inv_of_mem_H`; the reversed-coordinate heights (IF9.1) `if91Heights`
  (`if91Heights_eq_coordChange`: `F^ψ_c = −(h^φ ∘ m⁻¹ − χ Im L_{m⁻¹}) + c` on `ℝ \ {0}`); for `c = −πχ` they are the
  (CF9.4) exterior heights with the (CF9.5) weights (`if91Heights_centered_neg`, `…_pos`), admissible for strict angles
  (`neg_two_lt_cf95RhoL_iff`, `neg_two_lt_cf95RhoR_iff`); for `c = 0` no integer branch makes both formal weights
  exceed `−2` (`if91_unshifted_obstruction`; branch shifts: `coordChange_sub_int_lift`).
* **Aux. lemma 121.** Cumulative weights (FW9.1)–(FW9.2) are `cf95RhoL`, `cf95RhoR` (`fw91_height`, `fw92_height`);
  the extremal values `cf95RhoL_neg_half_pi`, `cf95RhoR_half_pi` (`= A − 2`); the jump weights (FW9.3)
  `fw93_left`, `fw93_right`, `fw93_left_add`, `fw93_right_add`; all four values exceed `−2` for strict final angles
  (`fw93_admissible`).
* **Aux. lemma 122.** The parameter `k > 4` with `Λ = sleLambda k`, `χ = −chiC k`, `A = k/2 − 2`
  (`pi_mul_neg_chiC_eq`); the shifted seed weights (PS9.2) (`ps92_left`, `ps92_right`); the sign pattern (PS9.3)
  (`ps93_pos`, `ps93_neg`, `ps93_mul_neg`); the interface `cf95_mem_Ioo_iff`, `sub_two_lt_two_mul_sub_two`.
* **Aux. lemma 123.** (NP16.2) `np162_left`, `np162_right`, `np161_ne_zero`, `aux123_outside_sector`,
  `aux123_ps92` (the shift `n = 1` maps `(A, 3A)` to the canonical `(3A, A)`).
* **Lemma 7.25 / Aux. lemma 131.** The angles (RS13.6) = (CS13.3) `rs136Theta1`, `rs136Theta2`, inverting (CF9.5)
  (`cf95RhoL_rs136Theta1`, `cf95RhoR_rs136Theta2`); `rs136_mem_Ioo` (Lemma 7.25: both strictly inside
  `(−π/2, π/2)`); `cs131_iff` ((CS13.1) iff `−π/2 ≤ θ₁ < θ₂ ≤ π/2`, `θ₁ < π/2`, `θ₂ > −π/2`) and
  `cs131_angle_gap` (`0 < θ₂ − θ₁ ≤ π`, so not in `2πℤ`); (7.3) `eq73_strip_weights`.
* **Lemmas 7.27–7.28.** `lemma727_side_sums`, `lemma728_side_sums` (both cumulative side weights exceed `−2`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set
open scoped Real
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec7

open DerivLog

/-- `A = κ'/2 − 2` for `κ' = 16/κ` (supplement §4, p. 463). -/
def counterflowA (κ : ℝ) : ℝ := 16 / κ / 2 - 2

theorem counterflowA_pos {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) : 0 < counterflowA κ := by
  have : 4 < 16 / κ := by rw [lt_div_iff₀ hκ]; linarith
  unfold counterflowA; linarith

theorem cf95RhoL_eq (κ θ : ℝ) : cf95RhoL κ θ = (1 / 2 - θ / π) * counterflowA κ - 2 := rfl

theorem cf95RhoR_eq (κ θ : ℝ) : cf95RhoR κ θ = (1 / 2 + θ / π) * counterflowA κ - 2 := rfl

/-! ### Aux. lemma 120: the inversion `m(z) = −1/z` -/

/-- `Log(−1/w) = iπ − Log w` in `ℍ` (Aux. lemma 120 proof; from (FD12.2) `neg_derivLog_neg_inv_eq`). -/
theorem log_neg_inv_of_mem_H {w : ℂ} (hw : w ∈ H) : log (-w⁻¹) = π * I - log w := by
  have h := neg_derivLog_neg_inv_eq hw
  have : (2 : ℂ) * log (-w⁻¹) = 2 * (π * I - log w) := by linear_combination h
  exact mul_left_cancel₀ two_ne_zero this

/-- Boundary values of `Im L_{m⁻¹}(x) = Im(2πi − 2 Log x)`: `0` on `ℝ₋`, `2π` on `ℝ₊`. -/
theorem im_inv_lift_of_neg {x : ℝ} (hx : x < 0) : (2 * π * I - 2 * log x).im = 0 := by
  simp [log_im, arg_ofReal_of_neg hx]

theorem im_inv_lift_of_pos {x : ℝ} (hx : 0 < x) : (2 * π * I - 2 * log x).im = 2 * π := by
  simp [log_im, arg_ofReal_of_nonneg hx.le]

variable {κ θ₁ θ₂ c : ℝ}

/-- (IF9.1): the initial heights of the reversed-coordinate field `F^ψ_c`, `ψ = m ∘ φ`: `λ + θ₁χ + c` on `ℝ₋` and
`−λ + θ₂χ + 2πχ + c` on `ℝ₊`. -/
def if91Heights (κ θ₁ θ₂ c : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then sleLambda κ + θ₁ * chiC κ + c else -sleLambda κ + θ₂ * chiC κ + 2 * π * chiC κ + c

/-- **(IF9.1)**. The pocket coordinate `φ` has the flow-oriented word `cf92Lower κ θ₁ θ₂` (`λ − θ₂χ` on `ℝ₋`,
`−λ − θ₁χ` on `ℝ₊`). With the compatible inverse lift `L_{m⁻¹}(w) = 2πi − 2 Log w` (IF9.2), the transformed `h`-heights
are `coordChange χ m⁻¹ L_{m⁻¹} h^φ` (coordinate rule (1.4)), and negating and adding `c` gives (IF9.1) at every
real `x ≠ 0`. -/
theorem if91Heights_eq_coordChange {x : ℝ} (hx : x ≠ 0) :
    -coordChange (chiC κ) (fun w => -w⁻¹) (fun w => 2 * π * I - 2 * log w)
        (fun z => cf92Lower κ θ₁ θ₂ z.re) x + c = if91Heights κ θ₁ θ₂ c x := by
  simp only [coordChange]
  have hre : (-((x : ℂ)⁻¹)).re = -x⁻¹ := by
    rw [← ofReal_inv, ← ofReal_neg, ofReal_re]
  rw [hre]
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · have : 0 < -x⁻¹ := neg_pos.2 (inv_lt_zero.2 hlt)
    rw [im_inv_lift_of_neg hlt, cf92Lower, ite_eq_right (not_lt.2 this.le), if91Heights,
      ite_eq_left hlt]
    ring
  · have : -x⁻¹ < 0 := neg_neg_iff_pos.2 (inv_pos.2 hgt)
    rw [im_inv_lift_of_pos hgt, cf92Lower, ite_eq_left this, if91Heights,
      ite_eq_right (not_lt.2 hgt.le)]
    ring

/-- A change `L_m ↦ L_m + 2πin` of the forward branch changes the inverse lift by `−2πin` and the transformed
`h`-heights by `+2πnχ` (hence `F^ψ_c` by `−2πnχ`). -/
theorem coordChange_sub_int_lift (X : ℝ) (ψ L : ℂ → ℂ) (h : ℂ → ℝ) (n : ℤ) (z : ℂ) :
    coordChange X ψ (fun w => L w - 2 * π * I * n) h z = coordChange X ψ L h z + 2 * π * n * X := by
  simp only [coordChange, sub_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, intCast_re,
    intCast_im, re_ofNat, im_ofNat]
  ring

/-- For `c = −πχ` the reversed heights on `ℝ₋` are the (CF9.4) exterior height `−λ'(1 + ρ_L)`. -/
theorem if91Heights_centered_neg (hκ : 0 < κ) {x : ℝ} (hx : x < 0) :
    if91Heights κ θ₁ θ₂ (-(π * chiC κ)) x = -sleLambda (16 / κ) * (1 + cf95RhoL κ θ₁) := by
  rw [if91Heights, ite_eq_left hx, ← cf95_left_height hκ]; ring

/-- For `c = −πχ` the reversed heights on `ℝ₊` are the (CF9.4) exterior height `λ'(1 + ρ_R)`. -/
theorem if91Heights_centered_pos (hκ : 0 < κ) {x : ℝ} (hx : 0 < x) :
    if91Heights κ θ₁ θ₂ (-(π * chiC κ)) x = sleLambda (16 / κ) * (1 + cf95RhoR κ θ₂) := by
  rw [if91Heights, ite_eq_right (not_lt.2 hx.le), ← cf95_right_height hκ]; ring

/-- The centred reversed word is the (CF9.4) word with its driver intervals removed. -/
theorem if91Heights_centered_eq_cf94 (hκ : 0 < κ) (q : ℝ) (hq : 0 < q) {x y : ℝ} (hx : x < 0) (hy : y < -1)
    {x' y' : ℝ} (hx' : 0 < x') (hy' : q < y') :
    if91Heights κ θ₁ θ₂ (-(π * chiC κ)) x = cf94Heights κ θ₁ θ₂ q (-(π * chiC κ)) y ∧
      if91Heights κ θ₁ θ₂ (-(π * chiC κ)) x' = cf94Heights κ θ₁ θ₂ q (-(π * chiC κ)) y' := by
  rw [if91Heights_centered_neg hκ hx, if91Heights_centered_pos hκ hx',
    (cf94Heights_centered hκ hq).1 hy, (cf94Heights_centered hκ hq).2.2.2 hy']
  exact ⟨rfl, rfl⟩

/-- Admissibility of the left seed weight: `ρ_L > −2` iff `θ₁ < π/2`. -/
theorem neg_two_lt_cf95RhoL_iff (hκ : 0 < κ) (hκ4 : κ < 4) : -2 < cf95RhoL κ θ₁ ↔ θ₁ < π / 2 := by
  have hA := counterflowA_pos hκ hκ4
  have hπ := Real.pi_pos
  rw [cf95RhoL_eq]
  constructor
  · intro h
    have : θ₁ / π < 1 / 2 := by nlinarith
    rwa [div_lt_iff₀ hπ, show 1 / 2 * π = π / 2 by ring] at this
  · intro h
    have : θ₁ / π < 1 / 2 := by rw [div_lt_iff₀ hπ]; linarith
    nlinarith

/-- Admissibility of the right seed weight: `ρ_R > −2` iff `θ₂ > −π/2`. -/
theorem neg_two_lt_cf95RhoR_iff (hκ : 0 < κ) (hκ4 : κ < 4) : -2 < cf95RhoR κ θ₂ ↔ -(π / 2) < θ₂ := by
  have hA := counterflowA_pos hκ hκ4
  have hπ := Real.pi_pos
  rw [cf95RhoR_eq]
  constructor
  · intro h
    have : -(1 / 2) < θ₂ / π := by nlinarith
    rwa [lt_div_iff₀ hπ, show -(1 / 2) * π = -(π / 2) by ring] at this
  · intro h
    have : -(1 / 2) < θ₂ / π := by rw [lt_div_iff₀ hπ]; linarith
    nlinarith

/-- **Aux. lemma 120, admissibility**: for `−π/2 < θ₁, θ₂ < π/2` both centred seed weights exceed `−2`. -/
theorem if91_admissible (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ < π / 2) (hθ₂ : -(π / 2) < θ₂) :
    -2 < cf95RhoL κ θ₁ ∧ -2 < cf95RhoR κ θ₂ :=
  ⟨(neg_two_lt_cf95RhoL_iff hκ hκ4).2 hθ₁, (neg_two_lt_cf95RhoR_iff hκ hκ4).2 hθ₂⟩

/-- **Aux. lemma 120, the unshifted frame**: for `c = 0` and every integer branch change `L_m ↦ L_m + 2πin`
(which shifts both heights of (IF9.1) by `−2πnχ`), at least one formal seed weight is `< −2`. -/
theorem if91_unshifted_obstruction (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : -(π / 2) < θ₁)
    (hθ₂ : θ₂ < π / 2) (n : ℤ) :
    Sec4.cumWeightLeft (16 / κ) (if91Heights κ θ₁ θ₂ 0 (-1) - 2 * π * n * chiC κ) < -2 ∨
      Sec4.cumWeightRight (16 / κ) (if91Heights κ θ₁ θ₂ 0 1 - 2 * π * n * chiC κ) < -2 := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hl' := Sec4.sleLambda_sixteen_div_pos hκ
  have hlam := Sec4.sleLambda_sixteen_div_eq_sub hκ
  simp only [if91Heights, ite_eq_left (show (-1 : ℝ) < 0 by norm_num),
    ite_eq_right (show ¬ (1 : ℝ) < 0 by norm_num), add_zero, Sec4.cumWeightLeft,
    Sec4.cumWeightRight]
  rcases le_or_gt n 0 with hn | hn
  · left
    have hn' : (n : ℝ) ≤ 0 := by exact_mod_cast hn
    have h1 : sleLambda (16 / κ) < sleLambda κ + θ₁ * chiC κ - 2 * π * n * chiC κ := by
      have hθχ : -(π / 2) * chiC κ < θ₁ * chiC κ := mul_lt_mul_of_pos_right hθ₁ hχ
      have h2 : 0 ≤ 2 * π * chiC κ := mul_nonneg (by positivity) hχ.le
      have : 2 * π * n * chiC κ ≤ 0 := by nlinarith
      linarith
    have := (one_lt_div hl').2 h1
    rw [neg_div]; linarith
  · right
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : -sleLambda κ + θ₂ * chiC κ + 2 * π * chiC κ - 2 * π * n * chiC κ <
        -sleLambda (16 / κ) := by
      have hθχ : θ₂ * chiC κ < π / 2 * chiC κ := mul_lt_mul_of_pos_right hθ₂ hχ
      have h2 : 0 ≤ 2 * π * chiC κ := mul_nonneg (by positivity) hχ.le
      have : 2 * π * chiC κ ≤ 2 * π * n * chiC κ := by nlinarith
      linarith
    have : (-sleLambda κ + θ₂ * chiC κ + 2 * π * chiC κ - 2 * π * n * chiC κ) / sleLambda (16 / κ) < -1 := by
      rw [div_lt_iff₀ hl']; linarith
    linarith

/-! ### Aux. lemma 121: finite force words of a framed incoming pocket -/

/-- (FW9.1)–(FW9.2) at the initial extremal angles: `R_L(−π/2) = R_R(π/2) = A − 2`. -/
theorem cf95RhoL_neg_half_pi (κ : ℝ) : cf95RhoL κ (-(π / 2)) = counterflowA κ - 2 := by
  have := Real.pi_pos.ne'
  rw [cf95RhoL_eq]; field_simp; ring

theorem cf95RhoR_half_pi (κ : ℝ) : cf95RhoR κ (π / 2) = counterflowA κ - 2 := by
  have := Real.pi_pos.ne'
  rw [cf95RhoR_eq]; field_simp; ring

/-- The jump weight of a left mark where the incoming-right angle changes from `θ` (seed side) to `θ'`:
`R_L(θ') − R_L(θ) = (θ − θ')/π · A`. -/
theorem cf95RhoL_sub (κ θ θ' : ℝ) : cf95RhoL κ θ' - cf95RhoL κ θ = (θ - θ') / π * counterflowA κ := by
  rw [cf95RhoL_eq, cf95RhoL_eq]; ring

/-- The jump weight of a right mark where the incoming-left angle changes from `θ` to `θ'`:
`R_R(θ') − R_R(θ) = (θ' − θ)/π · A`. -/
theorem cf95RhoR_sub (κ θ θ' : ℝ) : cf95RhoR κ θ' - cf95RhoR κ θ = (θ' - θ) / π * counterflowA κ := by
  rw [cf95RhoR_eq, cf95RhoR_eq]; ring

/-- Telescoping: along a schedule `φ 0, …, φ m` (from the seed outward), the jump weights sum to the last
cumulative value minus the seed value. -/
theorem sum_cf95RhoL_jumps (κ : ℝ) (φ : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (cf95RhoL κ (φ (i + 1)) - cf95RhoL κ (φ i)) =
      cf95RhoL κ (φ m) - cf95RhoL κ (φ 0) :=
  Finset.sum_range_sub (fun i => cf95RhoL κ (φ i)) m

theorem sum_cf95RhoR_jumps (κ : ℝ) (φ : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (cf95RhoR κ (φ (i + 1)) - cf95RhoR κ (φ i)) =
      cf95RhoR κ (φ m) - cf95RhoR κ (φ 0) :=
  Finset.sum_range_sub (fun i => cf95RhoR κ (φ i)) m

/-- **(FW9.3), left**: for the incoming-right schedule `(−π/2, θ₁)`, the second left mark has weight
`r_L^{(2)} = (1/2 + θ₁/π) A`, and `r_L^{(1)} + r_L^{(2)} = A − 2`. -/
theorem fw93_left (κ θ₁ : ℝ) :
    cf95RhoL κ (-(π / 2)) - cf95RhoL κ θ₁ = (1 / 2 + θ₁ / π) * counterflowA κ ∧
      cf95RhoL κ θ₁ + (cf95RhoL κ (-(π / 2)) - cf95RhoL κ θ₁) = counterflowA κ - 2 := by
  refine ⟨?_, by rw [add_sub_cancel, cf95RhoL_neg_half_pi]⟩
  rw [cf95RhoL_neg_half_pi, cf95RhoL_eq]; ring

/-- **(FW9.3), right**: for the incoming-left schedule `(π/2, θ₂)`, `r_R^{(2)} = (1/2 − θ₂/π) A` and
`r_R^{(1)} + r_R^{(2)} = A − 2`. -/
theorem fw93_right (κ θ₂ : ℝ) :
    cf95RhoR κ (π / 2) - cf95RhoR κ θ₂ = (1 / 2 - θ₂ / π) * counterflowA κ ∧
      cf95RhoR κ θ₂ + (cf95RhoR κ (π / 2) - cf95RhoR κ θ₂) = counterflowA κ - 2 := by
  refine ⟨?_, by rw [add_sub_cancel, cf95RhoR_half_pi]⟩
  rw [cf95RhoR_half_pi, cf95RhoR_eq]; ring

/-- **Aux. lemma 121, admissibility**: for strict final angles all four relevant cumulative values (the two seed
weights and the two outer totals `A − 2`) are greater than `−2`. -/
theorem fw93_admissible (hκ : 0 < κ) (hκ4 : κ < 4) (hθ₁ : θ₁ ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : θ₂ ∈ Ioo (-(π / 2)) (π / 2)) :
    -2 < cf95RhoL κ θ₁ ∧ -2 < cf95RhoR κ θ₂ ∧ -2 < cf95RhoL κ (-(π / 2)) ∧
      -2 < cf95RhoR κ (π / 2) := by
  have hA := counterflowA_pos hκ hκ4
  refine ⟨(neg_two_lt_cf95RhoL_iff hκ hκ4).2 hθ₁.2, (neg_two_lt_cf95RhoR_iff hκ hκ4).2 hθ₂.1, ?_, ?_⟩
  · rw [cf95RhoL_neg_half_pi]; linarith
  · rw [cf95RhoR_half_pi]; linarith

/-- The (CF9.5) weights of strict angles lie in `(−2, A − 2)` (Aux. lemma 122, "Interface with the Jordan-pocket
calculation"), and conversely. -/
theorem cf95RhoL_mem_Ioo_iff (hκ : 0 < κ) (hκ4 : κ < 4) :
    cf95RhoL κ θ₁ ∈ Ioo (-2) (counterflowA κ - 2) ↔ θ₁ ∈ Ioo (-(π / 2)) (π / 2) := by
  have hA := counterflowA_pos hκ hκ4
  have hπ := Real.pi_pos
  have key : cf95RhoL κ θ₁ < counterflowA κ - 2 ↔ -(π / 2) < θ₁ := by
    rw [cf95RhoL_eq]
    constructor
    · intro h
      have : -(1 / 2) < θ₁ / π := by nlinarith
      rwa [lt_div_iff₀ hπ, show -(1 / 2) * π = -(π / 2) by ring] at this
    · intro h
      have : -(1 / 2) < θ₁ / π := by rw [lt_div_iff₀ hπ]; linarith
      nlinarith
  rw [mem_Ioo, mem_Ioo, neg_two_lt_cf95RhoL_iff hκ hκ4, key]
  exact and_comm

theorem cf95RhoR_mem_Ioo_iff (hκ : 0 < κ) (hκ4 : κ < 4) :
    cf95RhoR κ θ₂ ∈ Ioo (-2) (counterflowA κ - 2) ↔ θ₂ ∈ Ioo (-(π / 2)) (π / 2) := by
  have hA := counterflowA_pos hκ hκ4
  have hπ := Real.pi_pos
  have key : cf95RhoR κ θ₂ < counterflowA κ - 2 ↔ θ₂ < π / 2 := by
    rw [cf95RhoR_eq]
    constructor
    · intro h
      have : θ₂ / π < 1 / 2 := by nlinarith
      rwa [div_lt_iff₀ hπ, show 1 / 2 * π = π / 2 by ring] at this
    · intro h
      have : θ₂ / π < 1 / 2 := by rw [div_lt_iff₀ hπ]; linarith
      nlinarith
  rw [mem_Ioo, mem_Ioo, neg_two_lt_cf95RhoR_iff hκ hκ4, key]

/-! ### Aux. lemma 122: the lattice discrepancy and the shifted seed weights -/

section Phase

variable {k : ℝ}

/-- With `χ = −χ(k) > 0` and `Λ = π/√k`: `πχ = AΛ`, `A = k/2 − 2` (Aux. lemma 122). -/
theorem pi_mul_neg_chiC_eq (hk : 0 < k) : π * -chiC k = (k / 2 - 2) * sleLambda k := by
  have := Sec4.pi_mul_chiC hk
  linarith

theorem neg_chiC_pos (hk4 : 4 < k) : 0 < -chiC k := by
  have hk : 0 < k := by linarith
  have h := pi_mul_neg_chiC_eq hk
  have hl := Sec4.sleLambda_pos hk
  have : 0 < π * -chiC k := by rw [h]; exact mul_pos (by linarith) hl
  exact pos_of_mul_pos_right this Real.pi_pos.le

/-- **(PS9.2), left**: subtracting the lattice constant `2πnχ` from the left seed height `−Λ(1 + r_L)` gives
the canonical height of weight `r_L + 2An`. -/
theorem ps92_left (hk : 0 < k) (rL : ℝ) (n : ℤ) :
    -sleLambda k * (1 + rL) - 2 * π * n * -chiC k = -sleLambda k * (1 + (rL + 2 * (k / 2 - 2) * n)) := by
  have h := pi_mul_neg_chiC_eq hk
  have : 2 * π * n * -chiC k = 2 * n * ((k / 2 - 2) * sleLambda k) := by rw [← h]; ring
  rw [this]; ring

/-- **(PS9.2), right**: `Λ(1 + r_R) − 2πnχ = Λ(1 + (r_R − 2An))`. -/
theorem ps92_right (hk : 0 < k) (rR : ℝ) (n : ℤ) :
    sleLambda k * (1 + rR) - 2 * π * n * -chiC k = sleLambda k * (1 + (rR - 2 * (k / 2 - 2) * n)) := by
  have h := pi_mul_neg_chiC_eq hk
  have : 2 * π * n * -chiC k = 2 * n * ((k / 2 - 2) * sleLambda k) := by rw [← h]; ring
  rw [this]; ring

/-- **(PS9.3)**, `n > 0`: `a = r_L(n) + 2 > 0` and `b = r_R(n) + 2 < 0`, for seed weights in `(−2, 2A − 2)`
(only `r_L > −2` and `r_R < 2A − 2` are used). -/
theorem ps93_pos (hk4 : 4 < k) {rL rR : ℝ} (hL : -2 < rL) (hR : rR < 2 * (k / 2 - 2) - 2) {n : ℤ}
    (hn : 0 < n) :
    0 < rL + 2 * (k / 2 - 2) * n + 2 ∧ rR - 2 * (k / 2 - 2) * n + 2 < 0 := by
  have hA : 0 < k / 2 - 2 := by linarith
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  constructor <;> nlinarith

/-- **(PS9.3)**, reflected, `n < 0`: `a < 0 < b`. -/
theorem ps93_neg (hk4 : 4 < k) {rL rR : ℝ} (hL : rL < 2 * (k / 2 - 2) - 2) (hR : -2 < rR) {n : ℤ}
    (hn : n < 0) :
    rL + 2 * (k / 2 - 2) * n + 2 < 0 ∧ 0 < rR - 2 * (k / 2 - 2) * n + 2 := by
  have hA : 0 < k / 2 - 2 := by linarith
  have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn
  constructor <;> nlinarith

/-- For a nonzero lattice integer the two shifted seed gaps `a = r_L(n) + 2`, `b = r_R(n) + 2` have opposite
strict signs (the entrance configuration excluded by Aux. lemma 104); in particular neither shifted weight is `−2`. -/
theorem ps93_mul_neg (hk4 : 4 < k) {rL rR : ℝ} (hL : rL ∈ Ioo (-2) (2 * (k / 2 - 2) - 2))
    (hR : rR ∈ Ioo (-2) (2 * (k / 2 - 2) - 2)) {n : ℤ} (hn : n ≠ 0) :
    (rL + 2 * (k / 2 - 2) * n + 2) * (rR - 2 * (k / 2 - 2) * n + 2) < 0 := by
  rcases lt_or_gt_of_ne hn with h | h
  · obtain ⟨h1, h2⟩ := ps93_neg hk4 hL.2 hR.1 h
    exact mul_neg_of_neg_of_pos h1 h2
  · obtain ⟨h1, h2⟩ := ps93_pos hk4 hL.1 hR.2 h
    exact mul_neg_of_pos_of_neg h1 h2

/-- The extremal outer-boundary weight `A − 2` lies inside the proved range `(−2, 2A − 2)` (Aux. lemma 122,
interface). -/
theorem sub_two_mem_Ioo (hk4 : 4 < k) : k / 2 - 2 - 2 ∈ Ioo (-2) (2 * (k / 2 - 2) - 2) := by
  constructor <;> linarith

end Phase

/-! ### Aux. lemma 123: a coherent nonzero phase outside the bounded seed sector -/

section NonzeroPhase

variable {k : ℝ}

/-- `d = 2πχ = 2AΛ` (Aux. lemma 123). -/
theorem np161_eq (hk : 0 < k) : 2 * π * -chiC k = 2 * (k / 2 - 2) * sleLambda k := by
  have h := pi_mul_neg_chiC_eq hk
  linear_combination 2 * h

theorem np161_ne_zero (hk4 : 4 < k) : 2 * π * -chiC k ≠ 0 :=
  (mul_pos (mul_pos two_pos Real.pi_pos) (neg_chiC_pos hk4)).ne'

/-- **(NP16.2), left**: `−Λ(1 + 3A) + d = −Λ(1 + A)`. -/
theorem np162_left (hk : 0 < k) :
    -sleLambda k * (1 + 3 * (k / 2 - 2)) + 2 * π * -chiC k = -sleLambda k * (1 + (k / 2 - 2)) := by
  rw [np161_eq hk]; ring

/-- **(NP16.2), right**: `Λ(1 + A) + d = Λ(1 + 3A)`. -/
theorem np162_right (hk : 0 < k) :
    sleLambda k * (1 + (k / 2 - 2)) + 2 * π * -chiC k = sleLambda k * (1 + 3 * (k / 2 - 2)) := by
  rw [np161_eq hk]; ring

/-- The weights `(A, 3A)` are admissible, the canonical weights `(3A, A)` are at least `k/2 − 2` (the
hypothesis of Aux. lemma 7), and `3A > 2A − 2`: the example lies outside the bounded seed sector. -/
theorem aux123_outside_sector (hk4 : 4 < k) :
    -2 < k / 2 - 2 ∧ -2 < 3 * (k / 2 - 2) ∧ k / 2 - 2 ≤ 3 * (k / 2 - 2) ∧
      2 * (k / 2 - 2) - 2 < 3 * (k / 2 - 2) := by
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The (PS9.2) shift with `n = 1` takes the observed word `(A, 3A)` to the canonical `(3A, A)`, and (PS9.3) fails
for it: `b = r_R(1) + 2 > 0`. -/
theorem aux123_ps92 (hk4 : 4 < k) :
    (k / 2 - 2) + 2 * (k / 2 - 2) * ((1 : ℤ) : ℝ) = 3 * (k / 2 - 2) ∧
      3 * (k / 2 - 2) - 2 * (k / 2 - 2) * ((1 : ℤ) : ℝ) = k / 2 - 2 ∧
      0 < 3 * (k / 2 - 2) - 2 * (k / 2 - 2) * ((1 : ℤ) : ℝ) + 2 := by
  push_cast
  refine ⟨by ring, by ring, by linarith⟩

end NonzeroPhase

/-! ### Lemma 7.25 (RS13.6), Aux. lemma 131 (CS13.1)–(CS13.3) and (7.3) -/

/-- (RS13.6) = (CS13.3), first angle: `θ₁ = π(1/2 − (ρ_L + 2)/A)`. -/
def rs136Theta1 (κ ρL : ℝ) : ℝ := π * (1 / 2 - (ρL + 2) / counterflowA κ)

/-- (RS13.6) = (CS13.3), second angle: `θ₂ = π((ρ_R + 2)/A − 1/2)`. -/
def rs136Theta2 (κ ρR : ℝ) : ℝ := π * ((ρR + 2) / counterflowA κ - 1 / 2)

/-- (RS13.6) inverts (CF9.5): the angle `θ₁` produces the seed weight `ρ_L`. -/
theorem cf95RhoL_rs136Theta1 (hκ : 0 < κ) (hκ4 : κ < 4) (ρL : ℝ) :
    cf95RhoL κ (rs136Theta1 κ ρL) = ρL := by
  have hA := (counterflowA_pos hκ hκ4).ne'
  have hπ := Real.pi_pos.ne'
  rw [cf95RhoL_eq, rs136Theta1]; field_simp; ring

theorem cf95RhoR_rs136Theta2 (hκ : 0 < κ) (hκ4 : κ < 4) (ρR : ℝ) :
    cf95RhoR κ (rs136Theta2 κ ρR) = ρR := by
  have hA := (counterflowA_pos hκ hκ4).ne'
  have hπ := Real.pi_pos.ne'
  rw [cf95RhoR_eq, rs136Theta2]; field_simp; ring

theorem rs136Theta1_cf95RhoL (hκ : 0 < κ) (hκ4 : κ < 4) (θ : ℝ) : rs136Theta1 κ (cf95RhoL κ θ) = θ := by
  have hA := (counterflowA_pos hκ hκ4).ne'
  have hπ := Real.pi_pos.ne'
  rw [cf95RhoL_eq, rs136Theta1]; field_simp; ring

theorem rs136Theta2_cf95RhoR (hκ : 0 < κ) (hκ4 : κ < 4) (θ : ℝ) : rs136Theta2 κ (cf95RhoR κ θ) = θ := by
  have hA := (counterflowA_pos hκ hκ4).ne'
  have hπ := Real.pi_pos.ne'
  rw [cf95RhoR_eq, rs136Theta2]; field_simp; ring

/-- **Lemma 7.25, angle choice**: for `ρ_L, ρ_R ∈ (−2, κ'/2 − 4)` both angles (RS13.6) are strictly between
`−π/2` and `π/2`. -/
theorem rs136_mem_Ioo (hκ : 0 < κ) (hκ4 : κ < 4) {ρL ρR : ℝ}
    (hL : ρL ∈ Ioo (-2) (counterflowA κ - 2)) (hR : ρR ∈ Ioo (-2) (counterflowA κ - 2)) :
    rs136Theta1 κ ρL ∈ Ioo (-(π / 2)) (π / 2) ∧ rs136Theta2 κ ρR ∈ Ioo (-(π / 2)) (π / 2) := by
  refine ⟨(cf95RhoL_mem_Ioo_iff hκ hκ4).1 ?_, (cf95RhoR_mem_Ioo_iff hκ hκ4).1 ?_⟩
  · rwa [cf95RhoL_rs136Theta1 hκ hκ4]
  · rwa [cf95RhoR_rs136Theta2 hκ hκ4]

/-- **Aux. lemma 131, (CS13.1) ⟺ angle order**: with `d = A − 2`, the conditions `−2 < r_L, r_R ≤ d` and
`r_L + r_R > d − 2` are exactly `−π/2 ≤ θ₁ < θ₂ ≤ π/2` together with `θ₁ < π/2` and `θ₂ > −π/2`. -/
theorem cs131_iff (hκ : 0 < κ) (hκ4 : κ < 4) {rL rR : ℝ} :
    (-2 < rL ∧ rL ≤ counterflowA κ - 2 ∧ -2 < rR ∧ rR ≤ counterflowA κ - 2 ∧
        counterflowA κ - 2 - 2 < rL + rR) ↔
      (-(π / 2) ≤ rs136Theta1 κ rL ∧ rs136Theta1 κ rL < rs136Theta2 κ rR ∧ rs136Theta2 κ rR ≤ π / 2 ∧
        rs136Theta1 κ rL < π / 2 ∧ -(π / 2) < rs136Theta2 κ rR) := by
  have hA := counterflowA_pos hκ hκ4
  have hπ := Real.pi_pos
  set A := counterflowA κ
  have e1 : rs136Theta1 κ rL = π / 2 - π * ((rL + 2) / A) := by rw [rs136Theta1]; ring
  have e2 : rs136Theta2 κ rR = π * ((rR + 2) / A) - π / 2 := by rw [rs136Theta2]; ring
  rw [e1, e2]
  have u1 : rL ≤ A - 2 ↔ (rL + 2) / A ≤ 1 := by rw [div_le_one hA]; constructor <;> intro h <;> linarith
  have u2 : -2 < rL ↔ 0 < (rL + 2) / A := by
    rw [div_pos_iff_of_pos_right hA]; constructor <;> intro h <;> linarith
  have v1 : rR ≤ A - 2 ↔ (rR + 2) / A ≤ 1 := by rw [div_le_one hA]; constructor <;> intro h <;> linarith
  have v2 : -2 < rR ↔ 0 < (rR + 2) / A := by
    rw [div_pos_iff_of_pos_right hA]; constructor <;> intro h <;> linarith
  have w : A - 2 - 2 < rL + rR ↔ 1 < (rL + 2) / A + (rR + 2) / A := by
    rw [← add_div, lt_div_iff₀ hA]; constructor <;> intro h <;> linarith
  rw [u1, u2, v1, v2, w]
  set u := (rL + 2) / A
  set v := (rR + 2) / A
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- **Aux. lemma 131**: under (CS13.1), `0 < θ₂ − θ₁ ≤ π`; hence `θ₂ − θ₁ ∉ 2πℤ` (the two constant-angle incoming
paths cannot share a terminal subarc). -/
theorem cs131_angle_gap (hκ : 0 < κ) (hκ4 : κ < 4) {rL rR : ℝ} (hL : -2 < rL)
    (hL' : rL ≤ counterflowA κ - 2) (hR : -2 < rR) (hR' : rR ≤ counterflowA κ - 2)
    (hS : counterflowA κ - 2 - 2 < rL + rR) :
    0 < rs136Theta2 κ rR - rs136Theta1 κ rL ∧ rs136Theta2 κ rR - rs136Theta1 κ rL ≤ π ∧
      ∀ n : ℤ, rs136Theta2 κ rR - rs136Theta1 κ rL ≠ 2 * π * n := by
  obtain ⟨h1, h2, h3, -, -⟩ := (cs131_iff hκ hκ4).1 ⟨hL, hL', hR, hR', hS⟩
  have hπ := Real.pi_pos
  refine ⟨by linarith, by linarith, fun n hn => ?_⟩
  have hpos : 0 < (n : ℝ) := by nlinarith
  have hlt : (n : ℝ) ≤ 1 / 2 := by nlinarith
  have h0 : 0 < n := by exact_mod_cast hpos
  have : (1 : ℝ) ≤ n := by exact_mod_cast h0
  linarith

/-- **(7.3)**: with the angles (RS13.6), the strip-side labels are interchanged relative to the half-plane seed
labels: `ρ^{1,L}_strip = (1/2 + θ₂/π)A − 2 = ρ_R`, `ρ^{1,R}_strip = (1/2 − θ₁/π)A − 2 = ρ_L`, and when both change
marks are present each side total is `d = A − 2`. -/
theorem eq73_strip_weights (hκ : 0 < κ) (hκ4 : κ < 4) (ρL ρR : ℝ) :
    (1 / 2 + rs136Theta2 κ ρR / π) * counterflowA κ - 2 = ρR ∧
      (1 / 2 - rs136Theta1 κ ρL / π) * counterflowA κ - 2 = ρL ∧
      cf95RhoR κ (rs136Theta2 κ ρR) + (cf95RhoR κ (π / 2) - cf95RhoR κ (rs136Theta2 κ ρR)) =
        counterflowA κ - 2 ∧
      cf95RhoL κ (rs136Theta1 κ ρL) + (cf95RhoL κ (-(π / 2)) - cf95RhoL κ (rs136Theta1 κ ρL)) =
        counterflowA κ - 2 :=
  ⟨cf95RhoR_rs136Theta2 hκ hκ4 ρR, cf95RhoL_rs136Theta1 hκ hκ4 ρL, (fw93_right κ _).2,
    (fw93_left κ _).2⟩

/-! ### Lemmas 7.27–7.28 -/

/-- **Lemma 7.27** (`c = k/2 − 2`, `k > 4`): if `r₁ ∈ (−2, c)` and `r₁ + r₂ ≥ c`, both cumulative side weights
exceed `−2`, so Lemma 7.26 applies. -/
theorem lemma727_side_sums {k r₁ r₂ : ℝ} (hk4 : 4 < k) (h1 : r₁ ∈ Ioo (-2) (k / 2 - 2))
    (h2 : k / 2 - 2 ≤ r₁ + r₂) : -2 < r₁ ∧ -2 < r₁ + r₂ :=
  ⟨h1.1, by linarith⟩

/-- **Lemma 7.28**: if `r₁ ≥ c` and `r₁ + r₂ ∈ (−2, c)`, both cumulative side weights exceed `−2`. -/
theorem lemma728_side_sums {k r₁ r₂ : ℝ} (hk4 : 4 < k) (h1 : k / 2 - 2 ≤ r₁)
    (h2 : r₁ + r₂ ∈ Ioo (-2) (k / 2 - 2)) : -2 < r₁ ∧ -2 < r₁ + r₂ :=
  ⟨by linarith, h2.1⟩

end Sec7

end InteractingSLE
