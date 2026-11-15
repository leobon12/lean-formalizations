/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.Aux22Hit

/-!
# Remark 4.10: the exposed left interval is one strictly critical span

Packet PROVE-SEC4-B5 (specification §4.2, Remark 4.10, `source/spec/p097-144.md#rem-4.10`, pp. 120–121): "At a
positive counterflow stopping time strictly before its first lower-boundary contact, the actual centered coupling of
`h − πχ/2`, with the inherited stopped-strip lift, gives the following new upper heights for the transported flow
background: `−λ′ + πχ/2 = −λ + πχ ∈ (−λ, λ)` on the exposed left side, `λ′ + πχ/2 = λ` on the exposed right side. The
untouched upper data retain their stated outer inequalities. The exposed left interval is therefore one strictly
critical span, with heights at most `−λ` to its left and at least `λ` to its right. The lower data retain the
non-hitting inequalities. Aux. lemma 22 gives an actual first contact in that left interval."

* `isAux22SpanData_rem410`: the deterministic step — mapped data of this shape (lower data of Proposition 4.11; upper
  data at most `−λ` left of the exposed left interval `(u, v)`, equal to `−λ + πχ` on it, at least `λ` to its right)
  satisfy the hypotheses of Aux. lemma 22 with the finite span `(u, v)`;
* `ae_hasFirstUpperEndpointIn_rem410_of_aux22Hit`: the actual first contact in the exposed left interval, from the
  named `Aux22HitStatement κ`.

The mapping of the flow background through the counterflow prefix (the "actual centered coupling of `h − πχ/2`" in
the chart of `𝒮 ∖ η′([0, τ′])`) is the converse cross-conditioning carrier (a flow line after a counterflow segment),
which is not landed (`planning/handoffs/PROVE-SEC5-E.md`, "What remains" 4).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Real NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Sec4

/-- **Remark 4.10, the span** (`0 < κ < 4`). Lower data of Proposition 4.11 (at most `−λ + πχ` left of `0`, at least
`λ` right of `0`) and upper data at most `−λ` left of `u`, equal to the exposed-left height `−λ + πχ` on `(u, v)` and at
least `λ` right of `v` satisfy the hypotheses of Aux. lemma 22's hitting case with the finite span `(u, v)`. -/
theorem isAux22SpanData_rem410 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {u v : ℝ} {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ} (hbL : IsPiecewiseConstantBoundaryData bL JL)
    (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda κ + π * chiC κ)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda κ ≤ bL x)
    (hleft : ∀ x : ℝ, x ∉ JU → x < u → bU x ≤ -sleLambda κ)
    (hspan : ∀ x : ℝ, x ∉ JU → u < x → x < v → bU x = -sleLambda κ + π * chiC κ)
    (hright : ∀ x : ℝ, x ∉ JU → v < x → sleLambda κ ≤ bU x) :
    IsAux22SpanData κ (u : EReal) (v : EReal) bL bU JL JU := by
  have hχ := chiC_pos hκ hκ4
  have hI : -sleLambda κ + π * chiC κ ∈ Ioo (-sleLambda κ) (sleLambda κ) := by
    have h1 := fig46_upper_left_mem_Ioo hκ hκ4
    rw [show π / 2 * chiC κ = π * chiC κ / 2 by ring, rem410_upper_left_eq hκ] at h1
    exact h1
  refine ⟨hbL, hbU, Or.inr ⟨hlowL, fun x hx hxJ => ?_⟩, fun x hxJ hux hxv => ?_,
    fun x hxJ hxu => hleft x hxJ (by exact_mod_cast hxu), fun x hxJ hvx => hright x hxJ (by exact_mod_cast hvx)⟩
  · have := hlowR x hx hxJ
    nlinarith [Real.pi_pos]
  · rw [hspan x hxJ (by exact_mod_cast hux) (by exact_mod_cast hxv)]
    exact ⟨hI.1, hI.2⟩

/-- **Remark 4.10, the actual first contact in the exposed left interval** (conditional helper: Aux. lemma 22's
hitting case, named). For a strip flow line whose (mapped) data have the shape of `isAux22SpanData_rem410`, almost
surely the trace has an actual first upper endpoint in the exposed left interval `(u, v) + i`. -/
theorem ae_hasFirstUpperEndpointIn_rem410_of_aux22Hit {κ : ℝ} (h22 : Aux22HitStatement.{u} κ) (hκ : 0 < κ)
    (hκ4 : κ < 4) {u v : ℝ} (huv : u < v) {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hbL : IsPiecewiseConstantBoundaryData bL JL) (hbU : IsPiecewiseConstantBoundaryData bU JU)
    (hlowL : ∀ x : ℝ, x < 0 → x ∉ JL → bL x ≤ -sleLambda κ + π * chiC κ)
    (hlowR : ∀ x : ℝ, 0 < x → x ∉ JL → sleLambda κ ≤ bL x)
    (hleft : ∀ x : ℝ, x ∉ JU → x < u → bU x ≤ -sleLambda κ)
    (hspan : ∀ x : ℝ, x ∉ JU → u < x → x < v → bU x = -sleLambda κ + π * chiC κ)
    (hright : ∀ x : ℝ, x ∉ JU → v < x → sleLambda κ ≤ bU x) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hfl : IsStripFlowLine κ bL bU JL JU P h η ζ) :
    ∀ᵐ ω ∂P, HasFirstUpperEndpointIn (u : EReal) (v : EReal) (η ω) (ζ ω) :=
  h22 u v bL bU JL JU P h η ζ (by exact_mod_cast huv)
    (isAux22SpanData_rem410 hκ hκ4 hbL hbU hlowL hlowR hleft hspan hright) hfl

end Sec4

end InteractingSLE
