/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Carrier

/-!
# §5.1: monotonicity of flow lines in the strip carriers — Proposition 5.1 stated, Proposition 5.5 deduced

Packet PROVE-SEC5-C (specification §5.1, `source/spec/p097-144.md` L699–L838, pp. 128–136).

* `Prop51Statement`: the exact statement of **Proposition 5.1** on the §5 carriers (`Carrier.lean`), in the frame `α`
  (the field `h + αχ` has the data of Figure 5.1; `α = 0` is the printed statement, and Proposition 5.5 applies it to
  `h + (θ₁ − π/2)χ`). Not proved here: its proof needs Lemma 5.4 (hence Lemma 5.2 / Aux. lemma 26) and Aux. lemma 22's
  actual first-endpoint statement for the conditional field after mapping out the counterflow prefix (see the
  handoff, "What remains").
* `prop55_of_prop51` (conditional helper, distinct name): **the proof of Proposition 5.5** from Proposition 5.1 (as
  `Prop51Statement`) and Proposition 4.11's containment of `η_{θ₁}` in the counterflow `η'_{θ₁}` of
  `h + (θ₁ − π/2)χ`, with the convenient upper data `a' ≥ λ' + (θ₁ + π/2)χ`, `b' ≥ λ' + (3π/2 − θ₁)χ` of the proof
  ("by Proposition 3.4, it suffices to prove this result with any choice of `a', b'`"; the transfer to arbitrary
  `a', b'` by Proposition 3.4 is not done). The height arithmetic is SEC5-A's `prop55_reduction`; the planar step is
  `LiesRightOf.mono`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Sec5

open Sec4 (stripHData stripHJumps IsStripCounterflowDriver)

/-- **Proposition 5.1** (pp. 128–129), on the §5 carriers, in the frame `α`. Let `0 < κ < 4`, let `h` be (the
`E`-image of) a strip field such that `h + αχ` has the data of Figure 5.1 (`−a`, `b` on `∂_L𝒮` around `0`; `−a'`,
`b'` on `∂_U𝒮` around `z₀ = x₀ + i`), with `a', b' ≥ λ' + πχ` and `a, b ≥ λ'`. Let `η'` be the counterflow line of
`h + αχ` starting at `z₀` (driver `W'` in the chart `M_q`, `q = e^{πx₀}`, a continuous generating trace `γ'`), fix `θ`
with (5.1), and let `η_θ` be the flow line of `h + αχ + θχ` from `0` (trace `η` with lifetime `ζ`, in the chart `E`).
If `θ > π/2`, `η_θ` almost surely passes to the left of `η'` (no point of `η'` is strictly on the left of `η_θ`); if
`θ < −π/2`, it passes to the right of `η'`. -/
def Prop51Statement : Prop :=
  ∀ ⦃κ : ℝ⦄, 0 < κ → κ < 4 → ∀ (α x₀ a b a' b' θ : ℝ), IsFig51Bounds κ a b a' b' → Eq51 κ a b θ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      IsFig51Field κ α x₀ a b a' b' P h →
      IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ →
      IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ' →
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω)) →
      (π / 2 < θ → ∀ᵐ ω ∂P,
          LiesRightOf (stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) (ζ' ω)) (pathRange (η ω) (ζ ω))) ∧
        (θ < -(π / 2) → ∀ᵐ ω ∂P,
          LiesLeftOf (stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) (ζ' ω)) (pathRange (η ω) (ζ ω)))

/-- The data of `h + αχ` in the frame `α` with parameters `(a − αχ, b + αχ)` are the data `(a, b)` of `h`. -/
theorem fig51LowerFrame_shift (κ α a b : ℝ) :
    fig51LowerFrame κ α (a - α * chiC κ) (b + α * chiC κ) = fig51Lower a b := by
  rw [fig51LowerFrame_eq]; congr 1 <;> ring

theorem fig51UpperFrame_shift (κ α x₀ a' b' : ℝ) :
    fig51UpperFrame κ α x₀ (a' - α * chiC κ) (b' + α * chiC κ) = fig51Upper x₀ a' b' := by
  rw [fig51UpperFrame_eq]; congr 1 <;> ring

/-- **Proposition 5.5 from Proposition 5.1 and Proposition 4.11's containment** (conditional helper; proof of
Proposition 5.5, pp. 135–136, with the convenient upper data of that proof). Let `h` have the data of Figure 5.1, fix
`θ₁ < θ₂` with (5.2), `(λ − b)/χ ≤ θ₁ < θ₂ ≤ (a + πχ − λ)/χ`, and take `a' ≥ λ' + (θ₁ + π/2)χ`,
`b' ≥ λ' + (3π/2 − θ₁)χ`. Let `η₂` be the angle-`θ₂` flow line of `h` from `0`, `η'_{θ₁}` the counterflow line of
`h + (θ₁ − π/2)χ` from `z₀` (trace `γ'`), and let `η₁` be the angle-`θ₁` flow line, contained in `η'_{θ₁}`
(Proposition 4.11: "`η_{θ₁}` is contained in the left boundary of `η'_{θ₁}`", hypothesis `h411`). Then almost surely
`η₂` lies to the left of `η₁`: no point of `η₁` is strictly on the left of `η₂`. -/
theorem prop55_of_prop51 (h51 : Prop51Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {x₀ a b a' b' θ₁ θ₂ : ℝ} (h1 : (sleLambda κ - b) / chiC κ ≤ θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ ≤ (a + π * chiC κ - sleLambda κ) / chiC κ)
    (ha' : sleLambda (16 / κ) + (θ₁ + π / 2) * chiC κ ≤ a')
    (hb' : sleLambda (16 / κ) + (3 * π / 2 - θ₁) * chiC κ ≤ b')
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsFig51Field κ 0 x₀ a b a' b' P h)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₂ : IsStripFlowLineAt κ 0 θ₂ (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} P h η₂ ζ₂)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ (θ₁ - π / 2) (Real.exp (π * x₀)) P h W' ζ')
    (hγ' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (h411 : ∀ᵐ ω ∂P, pathRange (η₁ ω) (ζ₁ ω) ⊆ stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) (ζ' ω)) :
    ∀ᵐ ω ∂P, LiesRightOf (pathRange (η₁ ω) (ζ₁ ω)) (pathRange (η₂ ω) (ζ₂ ω)) := by
  set α : ℝ := θ₁ - π / 2 with hα
  have hχ := Sec4.chiC_pos hκ hκ4
  obtain ⟨⟨hA', hB', hA, hB⟩, hθ', hlo, hhi⟩ := prop55_reduction hκ hκ4 h1 h12 h2 ha' hb'
  -- the field `h + αχ` has the data of Figure 5.1 with the shifted parameters
  have hh' : IsFig51Field κ α x₀ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ)
      P h := by
    unfold IsFig51Field
    rw [fig51LowerFrame_shift, fig51UpperFrame_shift]
    unfold IsFig51Field at hh
    rwa [fig51LowerFrame_zero, fig51UpperFrame_zero] at hh
  -- `η₂` is the flow line of `h + αχ` with the relative angle `θ₂ − α = θ₂ − θ₁ + π/2`
  have hη₂' : IsStripFlowLineAt κ α (θ₂ - α) (fig51LowerFrame κ α (a - α * chiC κ) (b + α * chiC κ))
      (fig51UpperFrame κ α x₀ (a' - α * chiC κ) (b' + α * chiC κ)) {0} {x₀} P h η₂ ζ₂ := by
    rw [fig51LowerFrame_shift, fig51UpperFrame_shift]
    unfold IsStripFlowLineAt at hη₂ ⊢
    rwa [show α + (θ₂ - α) = 0 + θ₂ by ring]
  have hrel : θ₂ - α = θ₂ - θ₁ + π / 2 := by rw [hα]; ring
  have hbounds : IsFig51Bounds κ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ) :=
    ⟨hA, hB, hA', hB'⟩
  have heq51 : Eq51 κ (a - α * chiC κ) (b + α * chiC κ) (θ₂ - α) := by
    rw [hrel]
    exact ⟨(div_le_iff₀ hχ).1 hlo, (le_div_iff₀ hχ).1 hhi⟩
  have hgt : π / 2 < θ₂ - α := by rw [hrel]; exact hθ'
  have h5 := (h51 hκ hκ4 α x₀ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ)
    (θ₂ - α) hbounds heq51 P h η₂ ζ₂ W' ζ' γ' hh' hη₂' hcf hγ').1 hgt
  filter_upwards [h5, h411] with ω h5ω h411ω
  exact h5ω.mono h411ω

end Sec5

end InteractingSLE
