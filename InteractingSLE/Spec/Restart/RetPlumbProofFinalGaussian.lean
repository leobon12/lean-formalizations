/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofDriverModelInputs
import InteractingSLE.Spec.Restart.FCK2SourceGaussian
import InteractingSLE.Spec.Sec7.Lemma76FR1

/-!
# Retained Gaussian pairing laws from Lemma 7.6's R1

Packet PROVE-RETPLUMB. R1 supplies the conditional word characteristic
functional. The landed fixed-type Gaussian adapter supplies bounded means and
integrability, without any independent Gaussian pairing hypothesis.
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

/-- R1 discharges the exact named Gaussian input on every fixed-type part of
an initial retained event. The conditioning sigma algebra may include the germ;
pairing integrability does not require it to equal the capacity filtration. -/
theorem exists_retInitialPairingGaussian_of_meanIdent
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
    ∃ 𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ},
      retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝒢.1 ∧
      ∀ a : ForceWordType, RetInitialPairingGaussian P 𝒢.1
        (FCPlumb.fcTypeBranch κ θ F β a)
        (fun ω => Exist.flowField 0 (θ * QuantumZipper.chiC κ) (hd.chartField κ h ω)) := by
  obtain ⟨𝒢, M, hR, _, he, hcf⟩ := exists_r1_of_meanIdent h75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hm
  refine ⟨𝒢, hR, ?_⟩
  have hβG : Measurable[𝒢.1] β := hβ.mono hR le_rfl
  have hsF : ∀ᵐ ω ∂P, ω ∈ F → (β ω).IsSorted := by
    filter_upwards [hs, hpair] with ω hsω hp hω
    exact hsω (hp hω)
  have hcF : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ F →
      P[fun ω => Complex.exp (Complex.I * (hd.chartField κ h ω φ : ℂ)) | 𝒢.1] ω =
        gaussCF (β ω) φ := by
    intro φ
    filter_upwards [hcf φ, he, hpair] with ω hc heω hp hω
    exact hc (heω.2 (hp hω))
  intro a φ
  exact FCPlumb.initialPairingGaussian_of_wordCF 𝒢.2 (hR _ hF) hβG hsF
    (hd.measurable_chartField κ hh.1) hcF hκ θ a φ

end InteractingSLE.Restart.RetAux79
