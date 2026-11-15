/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2SrcTerminal

/-!
# The remaining terminal input in original source coordinates

The conditional box word no longer occurs in the terminal input below.
Its comparison with the original terminal heights is proved, not assumed.
Real terminal access and the bad original incident height still require a
source proof. They are not consequences of a real tip alone.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData Sec7.PocketTraversal MartChar.RealFlow
universe u

/-- Named remaining source geometry, expressed entirely using the original
boundary datum and physical terminal point. No box-word height or clock
endpoint identity is assumed here. -/
def FCK2SrcPhysicalTerminalAccess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (κ θ : ℝ) (d : PairData Ω) (b : ℝ → ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ U : Ω → ℝ≥0∞)
    (γ : Ω → ℝ≥0 → ℂ) (W : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ meetSet d → ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω →
    (γ ω T).im = 0 ∧
      ((rightImg (fun s : ℝ => -W s.toNNReal ω) 0 T = -W T ω ∧
        sleLambda κ ≤ leftLim b (η ω (ζ ω).toNNReal).re + θ * chiC κ) ∨
      (rightImg (fun s : ℝ => W s.toNNReal ω) 0 T = W T ω ∧
        rightLim b (η ω (ζ ω).toNNReal).re + θ * chiC κ ≤ -sleLambda κ))

/-- The terminal input transfers from original physical heights to the
actual supplied measurable word. The height comparison is the only input
used by this purely probabilistic adapter. -/
theorem fcCapTerminalAccess_of_physical_terminal_heights
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ θ : ℝ} {d : PairData Ω}
    {b : ℝ → ℝ} {β : Ω → BoundaryWord} {η γ : Ω → ℝ≥0 → ℂ} {ζ U : Ω → ℝ≥0∞}
    {W : ℝ≥0 → Ω → ℝ}
    (hi : ∀ᵐ ω ∂P, ω ∈ meetSet d → ∀ T : ℝ≥0, (T : ℝ≥0∞) = U ω →
      (γ ω T).im = 0 →
      leftLim (β ω).fn (γ ω T).re = leftLim b (η ω (ζ ω).toNNReal).re ∧
      rightLim (β ω).fn (γ ω T).re = rightLim b (η ω (ζ ω).toNNReal).re)
    (ha : FCK2SrcPhysicalTerminalAccess P κ θ d b η ζ U γ W) :
    FCK2CapTerminalAccess P κ θ d β U γ W := by
  filter_upwards [hi, ha] with ω hiω haω hM T hT
  obtain ⟨him, h⟩ := haω hM T hT
  obtain ⟨eL, eR⟩ := hiω hM T hT him
  rcases h with h | h
  · exact Or.inl ⟨h.1, by rw [eL]; exact h.2⟩
  · exact Or.inr ⟨h.1, by rw [eR]; exact h.2⟩

/-- Named unproved source endpoint theorem. It concerns the original flow
lines and the actual canonical drivers, with no conditional word, mean
identification, or capacity safe law among its premises. -/
def FirstContactK2PhysicalTerminalAccessStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (_hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∀ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable (W₁ t)) → (∀ t, Measurable (W₂ t)) →
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      FCK2SrcPhysicalTerminalAccess P κ θ₁ d b η₁ ζ₁ U₁ γ₁ W₁ ∧
        FCK2SrcPhysicalTerminalAccess P κ θ₂ d b η₂ ζ₂ U₂ γ₂ W₂

/-- All conditional-word and physical-terminal comparisons are discharged
on the actual source coupling. Only the named original-coordinate endpoint
access theorem is used to supply the existing terminal-access statement. -/
theorem firstContactK2TerminalAccessStatement_of_physicalTerminalAccess
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u})
    (hAccess : FirstContactK2PhysicalTerminalAccessStatement.{u}) :
    FirstContactK2TerminalAccessStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  obtain ⟨A₁, A₂⟩ := hAccess κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  have hi := ae_canon_terminal_incident_readings h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hsort hmean hcanon
  exact ⟨fcCapTerminalAccess_of_physical_terminal_heights
      (hi.mono fun _ hω hM T hT him => ((hω hM).1 T hT him).2) A₁,
    fcCapTerminalAccess_of_physical_terminal_heights
      (hi.mono fun _ hω hM T hT him => ((hω hM).2 T hT him).2) A₂⟩

end InteractingSLE.Restart.FCPlumb
