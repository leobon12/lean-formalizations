/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2CapKernels
import InteractingSLE.Spec.Restart.FCK2CapAccess

/-!
# Exact remaining source constructions for the capacity route

The two source propositions below are explicitly unproved inputs. The first
asks for forward marked kernels and censored observations, rather than a
safe law at a random inverse clock. The second asks for endpoint access and
an incident height. No frozen or source-facing statement is changed.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)
namespace InteractingSLE.Restart.FCPlumb
open LQGMetric LQGMetric.MarkovZB DomainMarkov DomainMarkov.K2 Coupling LocalSets
open RetAux79 Sec7.PocketTraversal
universe u

/-- Forward Gaussian and complement kernels for one canonical chart path.
The field and capacity filtration are the actual supplied source objects. -/
structure FCK2CapForwardInputs {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (κ θ : ℝ) (d : PairData Ω) (β : Ω → BoundaryWord)
    (Hc : Ω → DistOn upperHalfPlaneOpens) (U : Ω → ℝ≥0∞)
    (W : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ) : Prop where
  gaussian : ∀ (a : ForceWordType) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0),
    HasFCK2CapForwardKernel P (𝓕 q)
      {ω | ω ∈ fcTypeBranch κ θ (meetSet d) β a ∧ ω ∈ avoidSet W U ψ q}
      (fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) ψ : ℂ)))
      (cfAt κ W (bheProc κ a.rhoL a.rhoR W
        (geomLW W (fun ω => FCDet.typeXL κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))
        (geomRW W (fun ω => FCDet.typeXR κ θ a.nL a.nR a.rhoL a.rhoR (β ω)))) ψ 1 (fun _ => q))
  members : ∀ (q : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ QuantumZipper.H →
    ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
    HasFCK2CapForwardKernel P (𝓕 q)
      {ω | ω ∈ meetSet d ∧ (q : ℝ≥0∞) < U ω ∧
        Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) q)}
      (fun ω => Complex.exp (Complex.I *
        (Exist.flowField 0 (θ * chiC κ) (Hc ω) (lapTest (ballsOpen Fb) f + Ξ) : ℂ)))
      (fun ω => projFactor (ballsOpen Fb) f Ξ * Complex.exp
        (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) Ξ : ℂ)))

/-- Optional passage constructs both capacity safe laws from the named
forward-kernel data, with no threshold or terminal hypothesis. -/
theorem bdrySafeInputs_of_fcCapForwardInputs {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ} {d : PairData Ω}
    {β : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens}
    {U : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {W : ℝ≥0 → Ω → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} (hHc : Measurable Hc)
    (h : FCK2CapForwardInputs P κ θ d β Hc U W 𝓕) :
    FCK2BdrySafeInputs P κ θ d β Hc U γ W 𝓕 := by
  have hm := (Exist.measurable_flowField 0 (θ * chiC κ)).comp hHc
  exact ⟨fun a => hasSafeLaw_of_fcCapForwardKernels hm (h.gaussian a),
    hasSafeMembers_of_fcCapForwardKernels hm h.members⟩

/-- Named unproved source construction of the forward marked kernels. -/
def FirstContactK2ForwardKernelsStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
      (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∀ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      ∀ (hm₁ : ∀ t, Measurable (W₁ t)) (hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      (FCK2CapForwardInputs P κ θ₁ d β (hd.chartField κ h) U₁ W₁
        (fcRetainedDriverFiltration P hd W₁ hm₁)) ∧
        (FCK2CapForwardInputs P κ θ₂ d β (hd.chartField κ h) U₂ W₂
          (fcRetainedDriverFiltration P hd W₂ hm₂))

/-- Named unproved source endpoint-access and height comparison. -/
def FirstContactK2TerminalAccessStatement : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
    ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [_mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord, Measurable[retSigma d P] β →
      (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) →
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞),
      (∀ t, Measurable fun ω => γ₁ ω t) → (∀ t, Measurable fun ω => γ₂ ω t) →
      Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∀ W₁ W₂ : ℝ≥0 → Ω → ℝ,
      ∀ (_hm₁ : ∀ t, Measurable (W₁ t)) (_hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      FCK2CapTerminalAccess P κ θ₁ d β U₁ γ₁ W₁ ∧
        FCK2CapTerminalAccess P κ θ₂ d β U₂ γ₂ W₂

end InteractingSLE.Restart.FCPlumb
