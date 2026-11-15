/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2SourceGaussian

/-!
# The source coupling's initial Gaussian pairing laws

The first-contact counterpart of Lemma 7.6's retained R1 is the landed
`ae_condExp_cexp_chartField_eq_gaussCF_meetSet`. It conditions on the actual
retained histories. Together with the zero-time filtration identity, it
discharges `FCK2SourceData.initial_gaussian` on the original source space.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb
open LocalSets
universe u

/-- Initial conditional Gaussian pairing laws for the concrete source
filtration, from the box mean identification. This conclusion is exactly the
Gaussian field of `FCK2SourceData`, at any continuation angle. -/
theorem initialPairingGaussian_of_boxMean
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma d P] β)
    (hs : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hm : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    (W : ℝ≥0 → Ω → ℝ) (hW : ∀ t, Measurable (W t)) (h0 : ∀ ω, W 0 ω = 0) (θ : ℝ) :
    ∀ (a : RetAux79.ForceWordType) (φ : TestOn upperHalfPlaneOpens),
      ∃ (μ V : Ω → ℝ) (K C : ℝ),
        @Sec6.Prop65.IsCondGaussian Ω (fcRetainedDriverFiltration P hd W hW 0) mΩ P
          ((fcTypeBranch κ θ (meetSet d) β a).indicator
            (fun ω => Exist.flowField 0 (θ * chiC κ) (hd.chartField κ h ω) φ)) μ V K ∧
        ∀ ω, ‖μ ω‖ ≤ C := by
  rw [fcRetainedDriverFiltration_zero hd W hW h0]
  intro a φ
  exact initialPairingGaussian_of_wordCF (retSigma_le P) (hd.measurableSet_meetSet P) hβ hs
    (hd.measurable_chartField κ hh.1)
    (ae_condExp_cexp_chartField_eq_gaussCF_meetSet h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
      hζ₁ hζ₂ hae hu₀ hβ hm) hκ θ a φ

end InteractingSLE.Restart.FCPlumb
