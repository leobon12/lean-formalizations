/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.StripMaps
import InteractingSLE.Spec.Sec4.Heights

/-!
# Transformed boundary heights in the explicit strip charts (Lemmas 4.3, 4.5, Aux. lemma 22)

Packet PROVE-SEC4-A (specification §4.1, `source/spec/p097-144.md` L211–L470).

Under the coordinate rule (1.4) (`InteractingSLE.coordChange`), a strip boundary height `h` at `z` becomes the
half-plane height `h + X · arg ψ'(z)` at `ψ(z)`, with the branch of `arg ψ'` given by the chart's lift
(`Spec/Sec4/StripMaps.lean`). This file records, for each chart of §4.1, the inequalities the proofs feed into the
height-to-weight conversion (`le_cumWeightLeft_iff`, `le_cumWeightRight_iff`, `hasAdmissiblePartialSums_iff`):

* `coordChange_apply_add`: the transformed height at `ψ z` is `h z + X Im L(z)`;
* Lemma 4.3 (`e^{πz} − 1`): an upper height `a ≤ −Λ` becomes at most `−(1 + c) Λ`;
* Lemma 4.5 (`stripQ q`): upper heights `≤ −Λ` left of `z₀` become at most `−Λ + π X`, upper heights `≥ Λ`
  right of `z₀` become at least `Λ − π X`;
* Aux. lemma 22 (UC11, UC12): the heights on `I` are unchanged; outside `I` the same two inequalities hold;
  the all-upper-positive alternative (`1 − e^{−πz}`) turns heights `≥ Λ` into heights `≥ Λ − π X`.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped Real
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Sec4

/-- The coordinate rule (1.4) read at the image point: if `u_𝒮 = u_ℍ ∘ ψ − X Im L` then
`u_ℍ(ψ z) = u_𝒮(z) + X Im L(z)`. -/
theorem coordChange_apply_add (X : ℝ) (ψ L : ℂ → ℂ) (uH : ℂ → ℝ) (z : ℂ) :
    uH (ψ z) = coordChange X ψ L uH z + X * (L z).im := by
  simp only [coordChange]; ring

variable {k : ℝ}

/-- Lemma 4.3, first case, in the chart `e^{πz} − 1`: an upper height `a ≤ −Λ` becomes
`a + X · π ≤ −(1 + c) Λ`. -/
theorem expChart_upper_height_le (hk : 0 < k) {a : ℝ} (ha : a ≤ -sleLambda k) (x : ℝ) :
    a + chiC k * (derivLogExpChart (x + I)).im ≤ -((1 + (k / 2 - 2)) * sleLambda k) := by
  rw [im_derivLogExpChart_upper, mul_comm]
  exact add_pi_mul_chiC_le_of_le_neg hk ha

/-- Lemma 4.5: an upper-left height `a ≤ −Λ` (left of `z₀`) becomes at most `−Λ + π X`. -/
theorem stripQ_upper_left_height_le {q x a : ℝ} (hx : Real.exp (π * x) < q)
    (ha : a ≤ -sleLambda k) :
    a + chiC k * (derivLogStripQ q (x + I)).im ≤ -sleLambda k + π * chiC k := by
  rw [im_derivLogStripQ_upper_left hx]; nlinarith

/-- Lemma 4.5: an upper-right height `b ≥ Λ` (right of `z₀`) becomes at least `Λ − π X`. -/
theorem stripQ_upper_right_height_ge {q x b : ℝ} (hx : q < Real.exp (π * x))
    (hb : sleLambda k ≤ b) :
    sleLambda k - π * chiC k ≤ b + chiC k * (derivLogStripQ q (x + I)).im := by
  rw [im_derivLogStripQ_upper_right hx]; nlinarith

/-- Lower heights are unchanged in Lemma 4.5's chart. -/
theorem stripQ_lower_height {q : ℝ} (hq : 0 < q) (x h : ℝ) :
    h + chiC k * (derivLogStripQ q x).im = h := by
  rw [im_derivLogStripQ_lower hq, mul_zero, add_zero]

/-- Aux. lemma 22 (UC11): heights on `I` are unchanged. -/
theorem spanChart_mid_height {r₀ r₁ x : ℝ} (hx₀ : r₀ < Real.exp (π * x)) (hx₁ : Real.exp (π * x) < r₁)
    (h : ℝ) : h + chiC k * (derivLogSpanChart r₀ r₁ (x + I)).im = h := by
  rw [im_derivLogSpanChart_upper_mid hx₀ hx₁, mul_zero, add_zero]

/-- Aux. lemma 22 (UC11): an upper height `≤ −Λ` left of `I` becomes a new lower-left height `≤ −Λ + π X`. -/
theorem spanChart_left_height_le {r₀ r₁ x a : ℝ} (h : r₀ < r₁) (hx : Real.exp (π * x) < r₀)
    (ha : a ≤ -sleLambda k) :
    a + chiC k * (derivLogSpanChart r₀ r₁ (x + I)).im ≤ -sleLambda k + π * chiC k := by
  rw [im_derivLogSpanChart_upper_left h hx]; nlinarith

/-- Aux. lemma 22 (UC11): an upper height `≥ Λ` right of `I` becomes a new lower-right height `≥ Λ − π X`. -/
theorem spanChart_right_height_ge {r₀ r₁ x b : ℝ} (h : r₀ < r₁) (hx : r₁ < Real.exp (π * x))
    (hb : sleLambda k ≤ b) :
    sleLambda k - π * chiC k ≤ b + chiC k * (derivLogSpanChart r₀ r₁ (x + I)).im := by
  rw [im_derivLogSpanChart_upper_right h hx]; nlinarith

/-- Aux. lemma 22 (UC12, `u = −∞`): an upper height `≥ Λ` right of `I` becomes at least `Λ − π X`. -/
theorem spanChartLeft_right_height_ge {r₁ x b : ℝ} (hx : r₁ < Real.exp (π * x)) (hb : sleLambda k ≤ b) :
    sleLambda k - π * chiC k ≤ b + chiC k * (derivLogSpanChartLeft r₁ (x + I)).im := by
  rw [im_derivLogSpanChartLeft_upper_right hx]; nlinarith

/-- Aux. lemma 22 (UC12, `v = +∞`): an upper height `≤ −Λ` left of `I` becomes at most `−Λ + π X`. -/
theorem spanChartRight_left_height_le {r₀ x a : ℝ} (hx : Real.exp (π * x) < r₀) (ha : a ≤ -sleLambda k) :
    a + chiC k * (derivLogSpanChartRight r₀ (x + I)).im ≤ -sleLambda k + π * chiC k := by
  rw [im_derivLogSpanChartRight_upper_left hx]; nlinarith

/-- Aux. lemma 22, all upper heights `≥ Λ`, chart `1 − e^{−πz}`: they become at least `Λ − π X` on `(1, ∞)`. -/
theorem leftEndChart_upper_height_ge {b : ℝ} (hb : sleLambda k ≤ b) (x : ℝ) :
    sleLambda k - π * chiC k ≤ b + chiC k * (derivLogLeftEndChart (x + I)).im := by
  rw [im_derivLogLeftEndChart_upper]; nlinarith

end Sec4

end InteractingSLE
