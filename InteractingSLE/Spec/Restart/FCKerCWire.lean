/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCKerCGauss1
import InteractingSLE.Spec.Restart.FCThresholdDriverPremises

/-!
# Theorem 1.5's corrected forward inputs: wiring

Packet PROVE-T15-FCKER3 (R82). The Gaussian field of the first path is proved (`hasFCK2CapForwardKernel_path₁`). The
corrected statement `FirstContactK2ForwardKernelsCStatement` is reduced to the two parts not proved here, stated as
named propositions with exactly the hypotheses of the corrected statement:

* `FirstContactK2ForwardMembers₁Statement`: the member field of the first path (Aux. 77's locality at the physical
  lines, glued by `hasFCK2CapForwardMembers_of_boxMembers`);
* `FirstContactK2ForwardInputs₂Statement`: both fields for the second path (no line kernel or line mean exists for
  the second continuation; a mirrored development or a reflection is needed).

* **`firstContactK2ForwardKernelsCStatement_of_members₁_inputs₂`**, and the same from Theorems 1.2–1.3 and Lemma 7.6
  (`firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb

open LQGMetric LQGMetric.MarkovZB WangWu.ChartConst DomainMarkov DomainMarkov.K2 Coupling LocalSets
open RetAux79 Sec7.PocketTraversal

universe u

/-- **Named remaining input: the member field of the first path** of `FCK2CapForwardInputsC`, under the hypotheses of
`FirstContactK2ForwardKernelsCStatement`. -/
def FirstContactK2ForwardMembers₁Statement : Prop :=
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
      ∀ (hm₁ : ∀ t, Measurable (W₁ t)) (_hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      ∀ (q : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ QuantumZipper.H →
      ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
      HasFCK2CapForwardMembers P (fcRetainedDriverFiltration P hd W₁ hm₁ q)
        {ω | ω ∈ meetSet d ∧ (q : ℝ≥0∞) < U₁ ω ∧
          Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W₁ r.toNNReal ω) q)}
        (fun ω => Complex.exp (Complex.I *
          (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) (lapTest (ballsOpen Fb) f + Ξ) : ℂ)))
        (fun ω => Complex.exp (Complex.I * (Exist.flowField 0 (θ₁ * chiC κ) (hd.chartField κ h ω) Ξ : ℂ)))
        (projFactor (ballsOpen Fb) f Ξ)

/-- **Named remaining input: both fields for the second path** of `FirstContactK2ForwardKernelsCStatement`. -/
def FirstContactK2ForwardInputs₂Statement : Prop :=
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
      ∀ (_hm₁ : ∀ t, Measurable (W₁ t)) (hm₂ : ∀ t, Measurable (W₂ t)),
      (∀ ω, Continuous (W₁ · ω)) → (∀ ω, Continuous (W₂ · ω)) →
      (∀ ω, W₁ 0 ω = 0) → (∀ ω, W₂ 0 ω = 0) →
      (∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧
        IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) →
      FCK2CapForwardInputsC P κ θ₂ d β (hd.chartField κ h) U₂ W₂ (fcRetainedDriverFiltration P hd W₂ hm₂)

/-- **The corrected forward-kernel statement from the first path's member field and the second path's inputs**: the
first path's Gaussian field is `FCKerC.hasFCK2CapForwardKernel_path₁`. -/
theorem firstContactK2ForwardKernelsCStatement_of_members₁_inputs₂
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u})
    (hM : FirstContactK2ForwardMembers₁Statement.{u}) (h2 : FirstContactK2ForwardInputs₂Statement.{u}) :
    FirstContactK2ForwardKernelsCStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  refine ⟨⟨fun a ψ q => ?_, hM κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg⟩,
    h2 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon
    W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg⟩
  exact FCKerC.hasFCK2CapForwardKernel_path₁ h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀
    hβ hsort hmean hcanon hm₁ hc₁ hz₁ (hg.mono fun _ h hω => (h hω).1) a ψ q

/-- The same with Lemma 7.5, Lemma 7.7 and Aux. lemma 56 supplied from Theorems 1.2–1.3 and Lemma 7.6 (R48: the
consumer is Theorem 1.5, which may use Theorems 1.2–1.3). -/
theorem firstContactK2ForwardKernelsCStatement_of_thm12_thm13_lemma76
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h76 : Sec7.Lemma76Statement.{u})
    (hM : FirstContactK2ForwardMembers₁Statement.{u}) (h2 : FirstContactK2ForwardInputs₂Statement.{u}) :
    FirstContactK2ForwardKernelsCStatement.{u} :=
  firstContactK2ForwardKernelsCStatement_of_members₁_inputs₂ (lemma75Statement_of_thm12_thm13 h12 h13)
    (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76) firstContact_retainedRangeEntranceStatement hM h2

end InteractingSLE.Restart.FCPlumb
