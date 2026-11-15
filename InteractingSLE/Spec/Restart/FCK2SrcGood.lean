/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Cap
import InteractingSLE.Spec.Supplement.GB6RelDetGood

/-!
# Good canonical codes on the source first-contact coupling

The conditional word-GFF law already suffices for goodness of the canonical
driver code. No safe law for the actual continuation, or terminal collision,
is used. The general-angle version uses a canonical flow code to realize a
reference flow under each conditional word law.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb
open Sec2.Assembly Exist.StagedLaw Supp8.GB6
universe u

/-- The GB6 good-code argument at any angle for which a canonical flow
code is supplied. The reference path is the flow code's own decoded path. -/
theorem ae_good_driverCode_of_wordGFF {κ θ : ℝ}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F)
    {G : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hG : IsCanonicalDriverCode κ θ G) {c : BoundaryWord} (hc : c.IsSorted)
    {S : Type} [MeasurableSpace S] {Q : Measure S} [IsProbabilityMeasure Q]
    {H : S → DistOn upperHalfPlaneOpens} (hH : IsGFFWithBoundaryData Q H c.fn c.jumps) :
    ∀ᵐ s ∂Q, IsGoodDrvCode (G (c, H s)) := by
  have hL : Measurable fun s => (F ((c, 0), H s)).2 :=
    measurable_snd.comp (hF.1.comp (measurable_const.prodMk hH.1))
  have hflow := hF.2.1 c 0 hc Q H (fun s => decPath (F ((c, 0), H s)))
    (fun s => (F ((c, 0), H s)).2) hH hL
    (ae_of_all _ fun _ => ⟨rfl, fun _ _ => rfl⟩)
  obtain ⟨H', 𝓕, W, VL, VR, B, htrans, hopt, -⟩ := hflow
  have hd : IsFlowLineDriver κ c.fn c.jumps θ Q H W (fun s => (F ((c, 0), H s)).2) :=
    ⟨H', 𝓕, VL, VR, B, htrans, hopt⟩
  filter_upwards [hG.2.2 c Q H W _ hd, ae_driver_zero_continuousOn hd] with s hm hW
  exact Supp8.GB6.isGoodDrvCode_of_driverCodeMatch hm hW.2

/-- Good canonical driver codes under a conditional word-GFF law on an
arbitrary source space. Only the field is disintegrated, so no regularity
event of the actual path has to be transferred through the kernel. -/
theorem ae_good_driverCode_of_word_kernel
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) {M : Set Ω} (hM : MeasurableSet[𝒢] M)
    {β : Ω → BoundaryWord} (hβ : Measurable[𝒢] β)
    (hsort : ∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable[mΩ] Hc)
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      P[fun ω => Complex.exp (Complex.I * (Hc ω φ : ℂ)) | 𝒢] ω = gaussCF (β ω) φ)
    {κ θ : ℝ}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F)
    {G : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hG : IsCanonicalDriverCode κ θ G) :
    ∀ᵐ ω ∂P, ω ∈ M → IsGoodDrvCode (G (β ω, Hc ω)) := by
  let _ : MeasurableSpace Ω := mΩ
  have hβm := hβ.mono h𝒢 le_rfl
  have hMm := h𝒢 _ hM
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hHc
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word h𝒢 hM hβ
    (w := id) measurable_id hsort hHc (H := id) measurable_id hlaw hcf
  have hgood : MeasurableSet {p : BoundaryWord × DistOn upperHalfPlaneOpens |
      IsGoodDrvCode (G p)} := hG.1 measurableSet_isGoodDrvCode
  apply Sec5.MarkovOther.ae_mem_of_compProd_eq_prod hMm hβm hHc hlaw hgood
  filter_upwards [hgff] with c hc
  exact ae_good_driverCode_of_wordGFF hF hG hc.1 hc.2

/-- On the original source coupling, the box mean identification makes
every canonical driver code good, at either continuation angle. No forward
kernel or finite-terminal input occurs in this source conclusion. -/
theorem ae_good_canonical_driver_of_boxMean
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
    (hsort : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hmean : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β) {θ : ℝ}
    {F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hF : IsCanonicalFlowCode κ θ F)
    {G : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞}
    (hG : IsCanonicalDriverCode κ θ G) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d → IsGoodDrvCode (G (β ω, hd.chartField κ h ω)) :=
  ae_good_driverCode_of_word_kernel (retSigma_le P) (hd.measurableSet_meetSet P) hβ hsort
    (hd.measurable_chartField κ hh.1)
    (ae_condExp_cexp_chartField_eq_gaussCF_meetSet h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
      hζ₁ hζ₂ hae hu₀ hβ hmean) hF hG

end InteractingSLE.Restart.FCPlumb
