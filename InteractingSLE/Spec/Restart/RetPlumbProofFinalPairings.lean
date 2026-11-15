/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofFinalGaussian

/-!
# Pairing integrability for every retained force-type branch

Packet PROVE-RETPLUMB. This is the original-source integrability input to K2,
derived directly from R1, without identifying its germ sigma algebra with the
capacity filtration at zero.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open LQGMetric (DistOn TestOn)
open Supp7 Sec7.Lemma76F
universe v
variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- R1 discharges all the original-source integrability obligations, one for
each test and each measurable fixed-type branch. -/
theorem retPairing_integrable_of_meanIdent
    (h75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hm : IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    (hs : ∀ᵐ ω ∂P, Sec7.Lemma76Exit.IsDisjointPair
      (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).IsSorted)
    {F : Set Ω} (hF : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] F)
    (hpair : ∀ᵐ ω ∂P, ω ∈ F → Sec7.Lemma76Exit.IsDisjointPair
      (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r) (θ : ℝ) :
    ∀ (a : ForceWordType) (φ : TestOn upperHalfPlaneOpens),
      Integrable (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ)
        (hd.chartField κ h ω) φ) (P.restrict (FCPlumb.fcTypeBranch κ θ F β a)) := by
  obtain ⟨𝒢, _, hG⟩ := exists_retInitialPairingGaussian_of_meanIdent h75 hκ hκ4 hb hh hη₁ hη₂
    hd hag hu₀ hβ hm hs hF hpair θ
  have hR := retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r
  intro a
  exact integrable_restrict_of_retInitialPairingGaussian
    ((hR _ hF).inter ((hβ.mono hR le_rfl) (measurableSet_forceTypeSet κ θ a))) (hG a)

end InteractingSLE.Restart.RetAux79
