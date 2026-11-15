/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Counterflow

/-!
# §4.2: boundary heights of the reverse counterflow's parameter field

Packet PROVE-SEC4-B2 ((FD11.5)–(FD11.7), Aux. lemma 1, pp. 13–14; Remark 4.8 (b), p. 119; Proposition 4.11, p. 121).

The parameter field of `CF_d(h_𝒮 + αχ)` in the chart `M_q` (`IsStripCounterflowDriver`) is
`h′ = (−h − (α + π)χ) ∘ M_q⁻¹ + χ(κ′) Im L_{M_q} ∘ M_q⁻¹` with `Im L_{M_q}(w) = −2 arg w` and `χ(κ′) = −χ`. On `∂ℍ`,
`M_q⁻¹(x) = −(1 + q)/(x + 1)` is negative for `x > −1` (boundary argument `π`) and positive for `x < −1` (argument
`0`), so its boundary data are `stripCounterflowData κ α q bL bU` (FD11.6 for the strip field `h_𝒮` with lower data
`bL` and upper data `bU`; `(q, ∞)` ↔ lower-left, `(0, q)` ↔ upper-left of `z₀`, `(−1, 0)` ↔ upper-right of `z₀`,
`(−∞, −1)` ↔ lower-right of `0`).

* `stripCounterflowData`; its four pieces `stripCounterflowData_of_lt_neg_one`, `…_of_mem_Ioo_neg_one_zero`,
  `…_of_mem_Ioo_zero`, `…_of_lt`.
* `stripCounterflowData_bounds_of_isProp411Data`: for the data class of Proposition 4.11 and `α = −π/2`, the
  parameter field's heights are at most `−λ(κ′) + πχ(κ′)` on `(−∞, 0)` and at least `λ(κ′) − πχ(κ′)` on `(0, ∞)`
  (off the marks): the non-boundary-hitting bounds of Lemma 4.3/Remark 4.1 for parameter `κ′`, i.e. (FD11.7)'s side
  partial sums at least `κ′/2 − 2` — Remark 4.8's condition (b) "the boundary data of `h − π/2 χ` … is at most
  `−λ′ − πχ` to the left of `z₀` and at least `λ′ + πχ` to the right of `z₀`".
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped Real
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec4

/-- Boundary data, at `x ∈ ℝ` (off `−1`, `0`, `q`), of the parameter field of `CF_d(h_𝒮 + αχ)` in the chart `M_q`:
`−g(M_q⁻¹ x) − (α + π)χ + χ(κ′)·(−2 arg M_q⁻¹ x)` with `g = stripHData κ bL bU` and boundary argument `π` for
`x > −1`, `0` for `x < −1` (`χ(κ′) = −χ`). -/
def stripCounterflowData (κ α q : ℝ) (bL bU : ℝ → ℝ) (x : ℝ) : ℝ :=
  -stripHData κ bL bU (-(1 + q) / (x + 1)) - (α + π) * chiC κ +
    if -1 < x then 2 * (π * chiC κ) else 0

variable {κ α q : ℝ} {bL bU : ℝ → ℝ}

/-- `(−∞, −1)`: the lower line right of `0`. -/
theorem stripCounterflowData_of_lt_neg_one (hq : 0 < q) {x : ℝ} (hx : x < -1) :
    stripCounterflowData κ α q bL bU x =
      -bL (Real.log ((x - q) / (x + 1)) / π) - (α + π) * chiC κ := by
  have hx1 : x + 1 < 0 := by linarith
  have hw : -1 < -(1 + q) / (x + 1) := by
    rw [lt_div_iff_of_neg hx1]; linarith
  have hne : x + 1 ≠ 0 := hx1.ne
  have hw1 : -(1 + q) / (x + 1) + 1 = (x - q) / (x + 1) := by field_simp; ring
  rw [stripCounterflowData, stripHData_of_lt hw, hw1, ite_eq_right (by linarith : ¬ (-1 < x))]
  ring

/-- `(−1, 0)`: the upper line right of `z₀`. -/
theorem stripCounterflowData_of_mem_Ioo_neg_one_zero (hq : 0 < q) {x : ℝ} (hx : x ∈ Ioo (-1) 0) :
    stripCounterflowData κ α q bL bU x =
      -bU (Real.log ((q - x) / (x + 1)) / π) - α * chiC κ := by
  have hx1 : 0 < x + 1 := by linarith [hx.1]
  have hw : -(1 + q) / (x + 1) < -1 := by
    rw [div_lt_iff₀ hx1]; nlinarith [hx.2]
  have hne : x + 1 ≠ 0 := hx1.ne'
  have hw1 : -(-(1 + q) / (x + 1)) - 1 = (q - x) / (x + 1) := by field_simp; ring
  rw [stripCounterflowData, stripHData_of_lt_neg_one hw, hw1, ite_eq_left hx.1]
  ring

/-- `(0, q)`: the upper line left of `z₀`. -/
theorem stripCounterflowData_of_mem_Ioo_zero {x : ℝ} (hx : x ∈ Ioo 0 q) :
    stripCounterflowData κ α q bL bU x =
      -bU (Real.log ((q - x) / (x + 1)) / π) - α * chiC κ := by
  have hx1 : 0 < x + 1 := by linarith [hx.1]
  have hw : -(1 + q) / (x + 1) < -1 := by
    rw [div_lt_iff₀ hx1]; linarith [hx.2]
  have hne : x + 1 ≠ 0 := hx1.ne'
  have hw1 : -(-(1 + q) / (x + 1)) - 1 = (q - x) / (x + 1) := by field_simp; ring
  rw [stripCounterflowData, stripHData_of_lt_neg_one hw, hw1,
    ite_eq_left (by linarith [hx.1] : -1 < x)]
  ring

/-- `(q, ∞)`: the lower line left of `0`. -/
theorem stripCounterflowData_of_lt (hq : 0 < q) {x : ℝ} (hx : q < x) :
    stripCounterflowData κ α q bL bU x =
      -bL (Real.log ((x - q) / (x + 1)) / π) + (π - α) * chiC κ := by
  have hx1 : 0 < x + 1 := by linarith
  have hw : -1 < -(1 + q) / (x + 1) := by
    rw [lt_div_iff₀ hx1]; linarith
  have hne : x + 1 ≠ 0 := hx1.ne'
  have hw1 : -(1 + q) / (x + 1) + 1 = (x - q) / (x + 1) := by field_simp; ring
  rw [stripCounterflowData, stripHData_of_lt hw, hw1, ite_eq_left (by linarith : -1 < x)]
  ring

/-- **The counterflow's parameter field is non-boundary-hitting for the data of Proposition 4.11** (`α = −π/2`,
`q = e^{πx₀}`, `0 < κ`, `κ′ = 16/κ`): its heights are at most `−λ(κ′) + πχ(κ′) = −λ′ − πχ` on `(−∞, 0)` and at
least `λ(κ′) − πχ(κ′) = λ′ + πχ` on `(0, ∞)`, off the marks `−1` and `q`. -/
theorem stripCounterflowData_bounds_of_isProp411Data (hκ : 0 < κ) {x₀ : ℝ}
    {JL JU : Finset ℝ} (h : IsProp411Data κ x₀ bL bU JL JU) :
    (∀ x < 0, x ≠ -1 → stripCounterflowData κ (-(π / 2)) (Real.exp (π * x₀)) bL bU x ≤
        -sleLambda (16 / κ) + π * chiC (16 / κ)) ∧
      ∀ x, 0 < x → x ≠ Real.exp (π * x₀) →
        sleLambda (16 / κ) - π * chiC (16 / κ) ≤
          stripCounterflowData κ (-(π / 2)) (Real.exp (π * x₀)) bL bU x := by
  obtain ⟨-, -, hLl, hLr, hUl, hUr⟩ := h
  set q := Real.exp (π * x₀) with hqdef
  have hq : 0 < q := Real.exp_pos _
  have hπ := Real.pi_pos
  have hlam := sleLambda_sixteen_div_eq_sub hκ
  have hchi := chiC_sixteen_div hκ
  -- positions of the four preimages relative to the strip marks
  have hlogq : Real.log q = π * x₀ := Real.log_exp _
  refine ⟨fun x hx hx1 => ?_, fun x hx hxq => ?_⟩
  · rcases lt_or_gt_of_ne hx1 with hlt | hgt
    · -- lower line right of `0`: `bL ≥ λ`
      rw [stripCounterflowData_of_lt_neg_one hq hlt, hlam, hchi]
      have hpos : 0 < (x - q) / (x + 1) := div_pos_of_neg_of_neg (by linarith) (by linarith)
      have h1 : 1 < (x - q) / (x + 1) := by
        rw [lt_div_iff_of_neg (by linarith)]; linarith
      have := hLr _ (div_pos (Real.log_pos h1) hπ)
      nlinarith
    · -- upper line right of `z₀`: `bU ≥ λ + πχ`
      rw [stripCounterflowData_of_mem_Ioo_neg_one_zero hq ⟨hgt, hx⟩, hlam, hchi]
      have hx1' : 0 < x + 1 := by linarith
      have hgt' : q < (q - x) / (x + 1) := by
        rw [lt_div_iff₀ hx1']; nlinarith
      have hlt : x₀ < Real.log ((q - x) / (x + 1)) / π := by
        rw [lt_div_iff₀ hπ, mul_comm, ← hlogq]
        exact Real.log_lt_log hq hgt'
      have := hUr _ hlt
      nlinarith
  · rcases lt_or_gt_of_ne hxq with hlt | hgt
    · -- upper line left of `z₀`: `bU ≤ −λ`
      rw [stripCounterflowData_of_mem_Ioo_zero ⟨hx, hlt⟩, hlam, hchi]
      have hx1' : 0 < x + 1 := by linarith
      have hpos : 0 < (q - x) / (x + 1) := div_pos (by linarith) hx1'
      have hlt' : (q - x) / (x + 1) < q := by
        rw [div_lt_iff₀ hx1']; nlinarith
      have hlt2 : Real.log ((q - x) / (x + 1)) / π < x₀ := by
        rw [div_lt_iff₀ hπ, mul_comm, ← hlogq]
        exact Real.log_lt_log hpos hlt'
      have := hUl _ hlt2
      nlinarith
    · -- lower line left of `0`: `bL ≤ −λ + πχ`
      rw [stripCounterflowData_of_lt hq hgt, hlam, hchi]
      have hx1' : 0 < x + 1 := by linarith
      have hpos : 0 < (x - q) / (x + 1) := div_pos (by linarith) hx1'
      have hlt1 : (x - q) / (x + 1) < 1 := by
        rw [div_lt_one hx1']; linarith
      have := hLl _ (div_neg_of_neg_of_pos (Real.log_neg hpos hlt1) hπ)
      nlinarith

end Sec4

end InteractingSLE
