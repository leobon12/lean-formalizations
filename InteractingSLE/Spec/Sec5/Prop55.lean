/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Mono
import InteractingSLE.Spec.Sec5.Prop411

/-!
# Proposition 5.5 from Proposition 5.1 with Proposition 4.11's containment discharged

Packet PROVE-SEC5-J (specification pp. 135–136, Proposition 5.5 and its proof).

**The coupling of Proposition 5.1.** The landed `Prop51Statement` (`Mono.lean`) quantifies over *every* coupling of
the flow line `η_θ` and the counterflow `η′` with `h`. Its proof (pp. 132–135) conditions on `η′([0, τ′])` and uses the
conditional law of `η_θ` in the remaining domain, which needs `η_θ` and `η′` conditionally independent given `h` (the
coupling of Lemma 4.7, Proposition 4.11 and Lemma 5.7; determination of flow lines by `h` is not available at this point
of the argument, ruling R43). `Prop51CondIndepStatement` is Proposition 5.1 for these couplings; the landed statement
implies it (`prop51CondIndepStatement_of_prop51Statement`), so every consumer may use the weaker hypothesis.

**Proposition 5.5** (convenient upper data, as in the proof: "by Proposition 3.4, it suffices to prove this result
with any choice of `a′, b′`"): `prop55_of_prop51CondIndep` is `prop55_of_prop51` with its hypothesis `h411`
(Proposition 4.11's containment) **discharged** by `ae_liesRightOf_image_of_liesRightOf_counterflow` (`Prop411.lean`,
from SEC5-I's restart inputs). Conclusion: almost surely no point of the explored segment `η_{θ₁}([0, T₁])` (any
horizon `T₁ > 0` before which `η_{θ₁}` is alive and in `ℍ`) is strictly on the left of `η_{θ₂}`.

Not done here (see the handoff): Proposition 5.1 itself; the restriction of `η_{θ₂}` to its first upper accumulation
time `τ₂` (the conclusion is with respect to the whole range of `η_{θ₂}`); and Proposition 3.4's transfer to arbitrary
upper data `a′, b′`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped Real NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Sec5

open Sec4 (IsStripCounterflowDriver)

/-- **Proposition 5.1 for conditionally independent couplings** (pp. 128–129; the coupling of Lemma 4.7 and
Proposition 4.11: `η_θ` and `η′` conditionally independent given `h`). Same data and conclusion as `Prop51Statement`,
with `h` measurable, `Ω` standard Borel (regular conditional laws) and the conditional independence of the flow line and
the counterflow driver given `h`. -/
def Prop51CondIndepStatement : Prop :=
  ∀ ⦃κ : ℝ⦄, 0 < κ → κ < 4 → ∀ (α x₀ a b a' b' θ : ℝ), IsFig51Bounds κ a b a' b' → Eq51 κ a b θ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hhm : Measurable h) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
      (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (γ' : Ω → ℝ≥0 → ℂ),
      IsFig51Field κ α x₀ a b a' b' P h →
      IsStripFlowLineAt κ α θ (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h η ζ →
      IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ' →
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω)) →
      CondIndep (MeasurableSpace.comap h inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
        (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P →
      (π / 2 < θ → ∀ᵐ ω ∂P,
          LiesRightOf (stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) (ζ' ω)) (pathRange (η ω) (ζ ω))) ∧
        (θ < -(π / 2) → ∀ᵐ ω ∂P,
          LiesLeftOf (stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) (ζ' ω)) (pathRange (η ω) (ζ ω)))

/-- The statement for all couplings implies the statement for conditionally independent ones. -/
theorem prop51CondIndepStatement_of_prop51Statement (h51 : Prop51Statement.{u}) :
    Prop51CondIndepStatement.{u} :=
  fun _ hκ hκ4 α x₀ a b a' b' θ hbd h51' _ _ _ P _ h _ η ζ W' ζ' γ' hh hη hcf htr _ =>
    h51 hκ hκ4 α x₀ a b a' b' θ hbd h51' P h η ζ W' ζ' γ' hh hη hcf htr

/-- **Proposition 5.5 with Proposition 4.11's containment discharged** (conditional helper: Proposition 5.1 for
conditionally independent couplings, and SEC5-I's counterflow restart inputs; proof of Proposition 5.5, pp. 135–136,
with the convenient upper data of that proof). Let `h` have the data of Figure 5.1, fix `θ₁ < θ₂` with (5.2), and take
`a′ ≥ λ′ + (θ₁ + π/2)χ`, `b′ ≥ λ′ + (3π/2 − θ₁)χ`. Let `η₁`, `η₂` be the flow lines of `h` with angles `θ₁`, `θ₂` from
`0`, and `η′_{θ₁}` the counterflow of `h + (θ₁ − π/2)χ` from `z₀` (trace `γ′`, infinite lifetime, continuous, avoiding
the strip end `+∞`, reaching its target), conditionally independent of each `ηᵢ` given `h`. Let `T₁ > 0` be a horizon
before which `η₁` is alive and in `ℍ`. Then almost surely no point of `η₁([0, T₁])` is strictly on the left of `η₂`. -/
theorem prop55_of_prop51CondIndep (h51 : Prop51CondIndepStatement.{u}) (hA : PartAInputsSixteenDiv)
    (hK : CrossRestart.CounterflowRestartKernelOnStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {x₀ a b a' b' θ₁ θ₂ : ℝ} (h1 : (sleLambda κ - b) / chiC κ ≤ θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ ≤ (a + π * chiC κ - sleLambda κ) / chiC κ)
    (ha' : sleLambda (16 / κ) + (θ₁ + π / 2) * chiC κ ≤ a')
    (hb' : sleLambda (16 / κ) + (3 * π / 2 - θ₁) * chiC κ ≤ b')
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hhm : Measurable h) (hh : IsFig51Field κ 0 x₀ a b a' b' P h)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsStripFlowLineAt κ 0 θ₁ (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} P h η₁ ζ₁)
    (hη₂ : IsStripFlowLineAt κ 0 θ₂ (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} P h η₂ ζ₂)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ (θ₁ - π / 2) (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci₁ : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η₁ ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hci₂ : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η₂ ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧
      Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T₁ : Ω → ℝ} (hT0 : ∀ᵐ ω ∂P, 0 < T₁ ω)
    (hT₁ : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T₁ ω → (t : ℝ≥0∞) < ζ₁ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T₁ ω → η₁ ω t ∈ H) :
    ∀ᵐ ω ∂P, LiesRightOf ((fun s : ℝ => η₁ ω s.toNNReal) '' Icc 0 (T₁ ω)) (pathRange (η₂ ω) (ζ₂ ω)) := by
  set α : ℝ := θ₁ - π / 2 with hα
  have hχ := Sec4.chiC_pos hκ hκ4
  obtain ⟨⟨hA', hB', hA0, hB0⟩, hθ', hlo, hhi⟩ := prop55_reduction hκ hκ4 h1 h12 h2 ha' hb'
  -- the field `h + αχ` has the data of Figure 5.1 with the shifted parameters
  have hh' : IsFig51Field κ α x₀ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ)
      P h := by
    unfold IsFig51Field
    rw [fig51LowerFrame_shift, fig51UpperFrame_shift]
    unfold IsFig51Field at hh
    rwa [fig51LowerFrame_zero, fig51UpperFrame_zero] at hh
  have hbounds : IsFig51Bounds κ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ) :=
    ⟨hA0, hB0, hA', hB'⟩
  -- `η₂` is the flow line of `h + αχ` with the relative angle `θ₂ − α`
  have hη₂' : IsStripFlowLineAt κ α (θ₂ - α) (fig51LowerFrame κ α (a - α * chiC κ) (b + α * chiC κ))
      (fig51UpperFrame κ α x₀ (a' - α * chiC κ) (b' + α * chiC κ)) {0} {x₀} P h η₂ ζ₂ := by
    rw [fig51LowerFrame_shift, fig51UpperFrame_shift]
    unfold IsStripFlowLineAt at hη₂ ⊢
    rwa [show α + (θ₂ - α) = 0 + θ₂ by ring]
  -- `η₁` is the flow line of `h + αχ` with the relative angle `π/2`
  have hη₁' : IsStripFlowLineAt κ α (π / 2) (fig51LowerFrame κ α (a - α * chiC κ) (b + α * chiC κ))
      (fig51UpperFrame κ α x₀ (a' - α * chiC κ) (b' + α * chiC κ)) {0} {x₀} P h η₁ ζ₁ := by
    rw [fig51LowerFrame_shift, fig51UpperFrame_shift]
    unfold IsStripFlowLineAt at hη₁ ⊢
    rwa [show α + π / 2 = 0 + θ₁ by rw [hα]; ring]
  have hrel : θ₂ - α = θ₂ - θ₁ + π / 2 := by rw [hα]; ring
  have heq51 : Eq51 κ (a - α * chiC κ) (b + α * chiC κ) (θ₂ - α) := by
    rw [hrel]
    exact ⟨(div_le_iff₀ hχ).1 hlo, (le_div_iff₀ hχ).1 hhi⟩
  have hgt : π / 2 < θ₂ - α := by rw [hrel]; exact hθ'
  -- Proposition 5.1: the counterflow lies to the right of `η₂`
  have h5 := (h51 hκ hκ4 α x₀ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ)
    (θ₂ - α) hbounds heq51 P h hhm η₂ ζ₂ W' ζ' γ' hh' hη₂' hcf htr' hci₂).1 hgt
  have h5' : ∀ᵐ ω ∂P, LiesRightOf (stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) ⊤)
      (pathRange (η₂ ω) (ζ₂ ω)) := by
    filter_upwards [h5, hγ] with ω h5ω hγω
    rwa [hγω.1] at h5ω
  -- Proposition 4.11's containment: `η₁([0, T₁])` is in the counterflow
  exact ae_liesRightOf_image_of_liesRightOf_counterflow hA hK hκ hκ4 hbounds hhm hh' hη₁' hcf htr' hci₁
    (hγ.mono fun ω hω => hω.2) hT0 hT₁ h5'

end Sec5

end InteractingSLE
