/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenLawMean
import InteractingSLE.Spec.Sec5.CrossCondGenLawMart
import InteractingSLE.GFF.LocalSets.SubdomainCov

/-!
# Passing a marked union law to the relative image filtration

PROVE-CROSSCOND-GEN. The missing optional-time union kernel and the surviving-word
mean identification are named propositions with exact types below. They are not
asserted here. `CrossCondGenLawMean` supplies the union kernel at a fixed recorded
flow-side set, conditional on its own local-set mean and marked boundary datum.
Passing that kernel to the inverse relative clock, through original-boundary hits,
is the additional geometric/optional-time input.

Given these inputs, a localized tower argument proves the chart law in the raw
image filtration. It retains complementary pockets: only the test covariance on
the active component is identified, not the entire complement with one chart.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito LocalSets Sec7.Lemma71D

/-- A marked union kernel at each fixed *image* time. In the application `A t` is
the union of the stopped original flow hull and the counterflow hull, and `ℋ t`
is its field germ joined with both retained marked histories. Establishing this
at the inverse relative clock is an explicit remaining input. -/
def ImageTimeUnionHypothesis {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) (c : Ω → Chart)
    (h : Ω → DistOn upperHalfPlaneOpens) (ℋ : ℝ≥0 → MeasurableSpace Ω)
    (A : ℝ≥0 → Ω → Set ℂ) (v : ℝ≥0 → Ω → ℂ → ℝ) : Prop :=
  ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
    IsChartAvoid (W · ω) (T ω) (c ω) φ t →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | ℋ t] ω =
        Complex.exp (Complex.I * ((∫ z, v t ω z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
            (H \ relClosureH (A t ω)) φ φ) : ℝ) : ℂ)

/-- The surviving boundary word identifies the union mean on tests in the active
component. This permits extra components cut off at original-boundary contacts. -/
def ImageMeanIdentificationHypothesis {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0∞) (c : Ω → Chart) (a k : ℝ) (v : ℝ≥0 → Ω → ℂ → ℝ) : Prop :=
  ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
    IsChartAvoid (W · ω) (T ω) (c ω) φ t →
      (∫ z, v t ω z * φ z) = chartMean κ ρL ρR (W · ω)
        (fun i r => VL i r ω) (fun j r => VR j r ω) (c ω) a k φ t

/-- Pockets away from the active component do not change its test covariance.
The only geometric inputs are that the active chart domain is a relatively clopen
part of the actual union complement. -/
theorem imageCovariance_of_active_component {w : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < T}) {c : Chart} (hc : c.IsConformal)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {A : Set ℂ}
    (hsub : c.2.1 '' (H \ QuantumZipper.fwdHull (rpath w) t) ⊆ H \ relClosureH A)
    (hrest : IsOpen ((H \ relClosureH A) \ (c.2.1 '' (H \ QuantumZipper.fwdHull (rpath w) t))))
    (φ : TestOn upperHalfPlaneOpens)
    (hφ : tsupport φ ⊆ c.2.1 '' (H \ QuantumZipper.fwdHull (rpath w) t)) :
    QuantumZipper.zeroGFFTestCov (H \ relClosureH A) φ φ = chartVar w c φ t := by
  have hUo := Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath hw ht
  have hCo : IsOpen (c.2.1 '' (H \ QuantumZipper.fwdHull (rpath w) t)) :=
    SmallGammaGeodesics.CC.isOpen_image_conf hUo (hc.1.mono sdiff_subset) (hc.injOn.mono sdiff_subset)
  exact zeroGFFTestCov_eq_of_isClopen (isOpen_H_diff_relClosureH A) sdiff_subset hCo hsub hrest φ hφ

/-- On an event known in a smaller σ-algebra, a conditional kernel measurable
there descends from the larger σ-algebra. Reuses the checked set-integral criterion. -/
theorem ae_condExp_eq_on_of_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓐 ℋ : MeasurableSpace Ω}
    (hA : 𝓐 ≤ ℋ) (hH : ℋ ≤ mΩ) {E : Set Ω} (hE : MeasurableSet[𝓐] E)
    {X G : Ω → ℂ} (hX : Integrable X P)
    (hG : Measurable[𝓐] (E.indicator G))
    (hkernel : ∀ᵐ ω ∂P, ω ∈ E → P[X | ℋ] ω = G ω) :
    ∀ᵐ ω ∂P, ω ∈ E → P[X | 𝓐] ω = G ω := by
  have heq : E.indicator (P[X | ℋ]) =ᵐ[P] E.indicator G := by
    filter_upwards [hkernel] with ω hω
    by_cases h : ω ∈ E
    · simp only [indicator_of_mem h, hω h]
    · simp only [indicator_of_notMem h]
  have hGi : Integrable (E.indicator G) P :=
    (integrable_condExp.indicator ((hA.trans hH) _ hE)).congr heq
  refine WangWu.ChartConst.ae_condExp_eq_of_forall_setIntegral (mΩ := mΩ) (μ := P) (m := 𝓐) (hA.trans hH) hE hX
    hG.stronglyMeasurable hGi ?_
  intro B hB
  have hBE : MeasurableSet[ℋ] (B ∩ E) := hA _ (hB.inter hE)
  calc
    (∫ ω in B ∩ E, X ω ∂P) = ∫ ω in B ∩ E, P[X | ℋ] ω ∂P :=
      (setIntegral_condExp hH hX hBE).symm
    _ = ∫ ω in B ∩ E, G ω ∂P := by
      apply setIntegral_congr_ae (hH _ hBE)
      filter_upwards [hkernel] with ω hω hωB
      exact hω hωB.2

/-- The real Gaussian characteristic factor in complex exponential form. -/
private theorem cexp_mean_variance (m v : ℝ) :
    Complex.exp (Complex.I * (m : ℂ)) * ((Real.exp (-(1 / 2) * v) : ℝ) : ℂ) =
      Complex.exp (Complex.I * (m : ℂ) - (((1 / 2 : ℝ) * v : ℝ) : ℂ)) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The explicit characteristic function of the surviving image word. -/
def imageChar {Ω : Type*} {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (c : Ω → Chart) (a k : ℝ) (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * (chartMean κ ρL ρR (W · ω) (fun i r => VL i r ω)
    (fun j r => VR j r ω) (c ω) a k φ t : ℂ) -
      (((1 / 2 : ℝ) * chartVar (W · ω) (c ω) φ t : ℝ) : ℂ))

/-- The marked union kernel descends to the raw image filtration. -/
theorem rawChar_of_unionLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {T : Ω → WithTop ℝ≥0} {c : Ω → Chart} {a k : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {ℋ : ℝ≥0 → MeasurableSpace Ω}
    {A : ℝ≥0 → Ω → Set ℂ} {v : ℝ≥0 → Ω → ℂ → ℝ}
    (hh : Measurable h)
    (hAH : ∀ t, 𝓐 t ≤ ℋ t) (hH : ∀ t, ℋ t ≤ mΩ)
    (hAvoid : ∀ t (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[𝓐 t] {ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t})
    (hMeanMeas : ∀ t (φ : TestOn upperHalfPlaneOpens), Measurable[𝓐 t]
      ({ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t}.indicator fun ω =>
        chartMean κ ρL ρR (W · ω) (fun i r => VL i r ω) (fun j r => VR j r ω) (c ω) a k φ t))
    (hVarMeas : ∀ t (φ : TestOn upperHalfPlaneOpens), Measurable[𝓐 t]
      ({ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t}.indicator fun ω =>
        chartVar (W · ω) (c ω) φ t))
    (hUnion : ImageTimeUnionHypothesis P W (fun ω => (T ω : ℝ≥0∞)) c h ℋ A v)
    (hMean : ImageMeanIdentificationHypothesis P κ ρL ρR W VL VR
      (fun ω => (T ω : ℝ≥0∞)) c a k v)
    (hCov : ∀ t (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t →
        QuantumZipper.zeroGFFTestCov (H \ relClosureH (A t ω)) φ φ =
          chartVar (W · ω) (c ω) φ t) :
    ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓐 t] ω =
          imageChar κ ρL ρR W VL VR c a k t φ ω := by
  intro t φ
  let E := {ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t}
  let G := imageChar κ ρL ρR W VL VR c a k t φ
  have hX : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P := by
    refine Integrable.of_bound (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp
        ((LQGMetric.measurable_distOn_apply φ).comp hh)))).aestronglyMeasurable 1 ?_
    exact Eventually.of_forall fun ω => by
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hG : Measurable[𝓐 t] (E.indicator G) := by
    have he : E.indicator G = E.indicator (fun ω => Complex.exp
        (Complex.I * ((E.indicator (fun ω => chartMean κ ρL ρR (W · ω)
          (fun i r => VL i r ω) (fun j r => VR j r ω) (c ω) a k φ t)) ω : ℂ) -
          (((1 / 2 : ℝ) * (E.indicator (fun ω => chartVar (W · ω) (c ω) φ t)) ω : ℝ) : ℂ))) := by
      apply indicator_congr
      intro ω hω
      simp only [G, imageChar, indicator_of_mem hω]
    rw [he]
    exact Measurable.indicator (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (hMeanMeas t φ)).const_mul _ |>.sub
        (Complex.measurable_ofReal.comp ((hVarMeas t φ).const_mul _)))) (hAvoid t φ)
  have hker : ∀ᵐ ω ∂P, ω ∈ E → P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | ℋ t] ω = G ω := by
    filter_upwards [hUnion t φ, hMean t φ, hCov t φ] with ω hU hM hC hω
    dsimp only [G, imageChar]
    rw [hU hω, hM hω, hC hω]
    exact cexp_mean_variance _ _
  exact ae_condExp_eq_on_of_le (mΩ := mΩ) (P := P) (𝓐 := 𝓐 t) (ℋ := ℋ t)
    (hAH t) (hH t) (hAvoid t φ) hX hG hker

/-- The explicit raw characteristic function gives the clause for every bounded
harmonic representative of the current word. -/
theorem chartConst_of_rawChar {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {T : Ω → WithTop ℝ≥0} {c : Ω → Chart} {a k : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hK : IsContactWord W VL VR T) (hc : ∀ ω, (c ω).IsConformal)
    (hraw : ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝓐 t] ω =
          imageChar κ ρL ρR W VL VR c a k t φ ω) :
    IsChartCouplingCharFunConst κ ρL ρR P 𝓐 W VL VR (fun ω => (T ω : ℝ≥0∞)) c a k h := by
  intro t u hu φ
  filter_upwards [hraw t φ] with ω hω ht hsupp
  rw [hω ⟨ht, hsupp⟩]
  have hm := integral_couplingMean_eq_chartMean (κ := κ) (ρL := ρL) (ρR := ρR)
    (w := fun r => W r ω) (vL := fun i r => VL i r ω) (vR := fun j r => VR j r ω)
    (ζ := (T ω : ℝ≥0∞)) (c := c ω) (a := a) (k := k) (t := t) (φ := φ)
    (hc ω) (hK.contW ω) ⟨ht, hsupp⟩
    (fun i => hK.ordL ω t i ht) (fun j => hK.ordR ω t j ht) (hu ω)
  change Complex.exp (Complex.I * (chartMean κ ρL ρR (W · ω)
    (fun i r => VL i r ω) (fun j r => VR j r ω) (c ω) a k φ t : ℂ) - _) = _
  congr 3
  exact congrArg Complex.ofReal hm.symm

/-- The optional marked union kernel and surviving-word mean imply the chart law. -/
theorem chartConst_of_unionLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {κ : ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {T : Ω → WithTop ℝ≥0} {c : Ω → Chart} {a k : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {ℋ : ℝ≥0 → MeasurableSpace Ω}
    {A : ℝ≥0 → Ω → Set ℂ} {v : ℝ≥0 → Ω → ℂ → ℝ}
    (hK : IsContactWord W VL VR T) (hc : ∀ ω, (c ω).IsConformal) (hh : Measurable h)
    (hAH : ∀ t, 𝓐 t ≤ ℋ t) (hH : ∀ t, ℋ t ≤ mΩ)
    (hAvoid : ∀ t (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[𝓐 t] {ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t})
    (hMeanMeas : ∀ t (φ : TestOn upperHalfPlaneOpens), Measurable[𝓐 t]
      ({ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t}.indicator fun ω =>
        chartMean κ ρL ρR (W · ω) (fun i r => VL i r ω) (fun j r => VR j r ω) (c ω) a k φ t))
    (hVarMeas : ∀ t (φ : TestOn upperHalfPlaneOpens), Measurable[𝓐 t]
      ({ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t}.indicator fun ω =>
        chartVar (W · ω) (c ω) φ t))
    (hUnion : ImageTimeUnionHypothesis P W (fun ω => (T ω : ℝ≥0∞)) c h ℋ A v)
    (hMean : ImageMeanIdentificationHypothesis P κ ρL ρR W VL VR
      (fun ω => (T ω : ℝ≥0∞)) c a k v)
    (hCov : ∀ t (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
      IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ t →
        QuantumZipper.zeroGFFTestCov (H \ relClosureH (A t ω)) φ φ =
          chartVar (W · ω) (c ω) φ t) :
    IsChartCouplingCharFunConst κ ρL ρR P 𝓐 W VL VR (fun ω => (T ω : ℝ≥0∞)) c a k h := by
  exact chartConst_of_rawChar hK hc
    (rawChar_of_unionLaw hh hAH hH hAvoid hMeanMeas hVarMeas hUnion hMean hCov)

end InteractingSLE.Sec5.CrossCond.Gen
