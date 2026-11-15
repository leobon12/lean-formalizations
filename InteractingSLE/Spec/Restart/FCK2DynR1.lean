/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2DynCollision
import InteractingSLE.Spec.Sec7.Lemma72DMember

/-!
# Member identities from the ordinary retained-history R1 kernel

The identities hold in the retained chart, on its measurable ordinary-pair
hull. Using them for a first-contact continuation still requires the chart
and capacity-window transfer; no ordinary-pair property is asserted for the
later first-contact lines.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal RealInnerProductSpace
open LQGMetric LQGMetric.MarkovZB

namespace InteractingSLE.Restart.FCPlumb
open LocalSets Coupling Sec7.PocketTraversal QuantumZipper.K3 QuantumZipper.Thm11Asm
universe u

/-- The word-GFF characteristic functional has the Dirichlet member factor
on every open subdomain of the half-plane. -/
theorem gaussCF_lapTest_add {c : BoundaryWord} (hc : c.IsSorted)
    {V : Opens ℂ} (hV : V ≤ upperHalfPlaneOpens)
    (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    gaussCF c (lapTest V f + Ξ) = projFactor V f Ξ * gaussCF c Ξ := by
  let M := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens c.mean
  have hmean := c.isBoundedHarmonicExtension_mean hc
  have hh : IsHarmonicDistOn M QuantumZipper.H :=
    WholeField.isHarmonicDistOn_smoothDist hmean.1
  have h0 := IsHarmonicDistOn.apply_lapTest_eq_zero QuantumZipper.isOpen_H hh hV hV f
  have eM : M (lapTest V f + Ξ) = M Ξ := by rw [map_add, h0, zero_add]
  have hMc : ContinuousOn c.mean upperHalfPlaneOpens := BoundaryWord.continuousOn_mean c
  have he (φ : TestOn upperHalfPlaneOpens) : M φ = ∫ z, c.mean z * φ z := by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply hMc]
    congr 1
    funext z
    exact mul_comm _ _
  rw [he, he] at eM
  have eV := zeroGFFTestCov_lapTest_sub_add hV QuantumZipper.isOpen_H subset_rfl hV Ξ f 0
  rw [LocalExt.lapTest_zero hV, sub_zero, LocalExt.gradFeat_zsSub_zero, sub_zero] at eV
  change QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ)
    ⇑(lapTest V f + Ξ) ⇑(lapTest V f + Ξ) = _ at eV
  simp only [gaussCF, projFactor]
  rw [eM, eV, ← Complex.exp_add]
  congr 1
  rw [show (upperHalfPlaneOpens : Set ℂ) = QuantumZipper.H from rfl]
  push_cast
  ring

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- R1 on an event suffices for its member identities on all measurable
subevents. The field need only be measurable; its pairings need not yet
be known integrable. -/
theorem setIntegral_lapTest_of_wordCF_on {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ)
    {M : Set Ω} {β : Ω → BoundaryWord} {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable[mΩ] X) (hs : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted)
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω' => Complex.exp (Complex.I * (X ω' φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ)
    {V : Opens ℂ} (hV : V ≤ upperHalfPlaneOpens) {D : Set Ω}
    (hD : MeasurableSet[𝒢] D) (hDM : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ M)
    (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens) :
    ∫ ω in D, Complex.exp (Complex.I * (X ω (lapTest V f + Ξ) : ℂ)) ∂P =
      projFactor V f Ξ * ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P := by
  let _ : MeasurableSpace Ω := mΩ
  have hint (φ : TestOn upperHalfPlaneOpens) :
      Integrable (fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX)
  rw [← setIntegral_condExp h𝒢 (hint _) hD, ← setIntegral_condExp h𝒢 (hint _) hD,
    ← integral_const_mul]
  refine setIntegral_congr_ae (h𝒢 _ hD) ?_
  filter_upwards [hcf (lapTest V f + Ξ), hcf Ξ, hs, hDM] with ω h1 h2 hsω hM hωD
  rw [h1 (hM hωD), h2 (hM hωD)]
  exact gaussCF_lapTest_add (hsω (hM hωD)) hV f Ξ

/-- The newly landed ordinary-pair R1 supplies member identities of its
retained chart field, on the same measurable hull. These are source
consequences of its mean identification, not extra member hypotheses. -/
theorem exists_r1_members_of_meanIdentOrd
    (h75 : Theorem15.Lemma75Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : Supp7.RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hβ : Measurable[Sec7.Lemma76F.retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hs : ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      (β ω).IsSorted)
    (hm : RLC.IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω),
      Sec7.Lemma76F.retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝒢.1 ∧ MeasurableSet[𝒢.1] M ∧
      (∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ω ∈ M) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ (V : Opens ℂ), V ≤ upperHalfPlaneOpens → ∀ D : Set Ω, MeasurableSet[𝒢.1] D →
        (∀ᵐ ω ∂P, ω ∈ D → ω ∈ M) → ∀ (f : zsSub (V : Set ℂ)) (Ξ : TestOn upperHalfPlaneOpens),
          ∫ ω in D, Complex.exp (Complex.I * (hd.chartField κ h ω (lapTest V f + Ξ) : ℂ)) ∂P =
            projFactor V f Ξ * ∫ ω in D, Complex.exp (Complex.I * (hd.chartField κ h ω Ξ : ℂ)) ∂P := by
  obtain ⟨𝒢, M, hR, hM, hOM, hhull, hcf⟩ :=
    RLC.exists_r1_of_meanIdentOrd h75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hβ hm
  have hβG : Measurable[𝒢.1] β := hβ.mono hR le_rfl
  have hsM := hhull {ω | (β ω).IsSorted} (hβG BoundaryWord.measurableSet_isSorted) hs
  refine ⟨𝒢, M, hR, hM, hOM, hcf, fun V hV D hD hDM f Ξ => ?_⟩
  exact setIntegral_lapTest_of_wordCF_on 𝒢.2 (hd.measurable_chartField κ hh.1)
    hsM hcf hV hD hDM f Ξ

end InteractingSLE.Restart.FCPlumb
