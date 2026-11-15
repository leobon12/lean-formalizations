/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW3LawJointIndep
import InteractingSLE.GFF.LocalSets.Projection
import InteractingSLE.GFF.PushforwardLaw
import QuantumZipper.Proofs.Thm18.LWFarPocketFar
import QuantumZipper.Proofs.GFF.K3.Conformal
import SupercriticalConformalCovariance.ZBConformal.Covariance

/-!
# The Markov decomposition read through a conformal chart

Packet PROVE-STAGEDLOC, item (1). A later piece of a staged path is a flow line of the field read through a random
conformal chart `c = (fwd, inv, lift)` fixed by the past: `h' = h ∘ inv + m` on `ℍ` (`Chart.pullField`, tested
against the transported test functions `Chart.pushTest`; `m` collects the deterministic offset, lift and harmonic
mean terms). Its locality is expressed through the Markov decomposition `h' = X' + Y'` of the chart field along an
open set `U' ⊆ ℍ`, while the locality of the whole path is expressed through the Markov decomposition `h = X + Y` of
the physical field along `U` (specification Proposition 3.1). For `U' = inv⁻¹(U)` (`chartPre`) and `U ∖ dom c` open
(the old curve, which carries the frontier of the chart domain in `ℍ`, avoids `U`), the two decompositions correspond:

  `X' = X ∘ inv`,   `Y' = Y ∘ inv + m`   (`ae_markov_pushTest_eq`, `ae_markovCompl_pushTest_eq`).

Proof: `X'(φ)` is the `L²` limit of the Dirichlet pairings `h'(−Δf_n/2π)`, `f_n ∈ C_c^∞(U')`, `∇f_n → covVec_{U'} φ`
(`LocalSets.exists_tendsto_integral_sq_of_isMarkovDecomposition`). Since `Y` is harmonic on `U`, `Y ∘ inv` is
harmonic on `U'` (`IsHarmonicDistOn.pullField`: harmonic functions composed with holomorphic maps), so
`h'(−Δf_n/2π) = X(pushTest(−Δf_n/2π)) + m(−Δf_n/2π)`, and `m` vanishes on Dirichlet pairings of `U'` (both sides are
centred). Finally `E|X(pushTest χ)|² = σ²_U(pushTest χ) = σ²_{U'}(χ)` (`zeroGFFTestCov_pushTest_chartPre`: the
covariance of `U` restricted to measures carried by `dom c` is the covariance of `U ∩ dom c`, which is conformally
invariant), so `X(pushTest(−Δf_n/2π)) → X(pushTest φ)` in `L²`.

## Main results

* `chartPre`, `isOpen_chartPre`, `image_chartPre`: the chart pre-image `U' = {w ∈ ℍ | inv w ∈ U}`;
* **`zeroGFFTestCov_pushTest_chartPre`**: `σ_U(pushTest φ, pushTest ψ) = σ_{U'}(φ, ψ)` for every pair of test
  functions on `ℍ` (not only those supported in `U'`);
* **`IsHarmonicDistOn.pullField`**: `T` harmonic on `U` ⇒ `T ∘ inv` harmonic on `U'`;
* **`ae_markov_pushTest_eq`**, **`ae_markovCompl_pushTest_eq`**: the chart transport of Markov decompositions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal
open QuantumZipper (H isOpen_H zeroGFFTestCov dualNormSq dualCov zeroSpace testMeasPos testMeasNeg)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)

namespace InteractingSLE

namespace Restart

namespace MarkovChart

/-! ### The chart pre-image of an open set -/

section Pre

variable {c : Chart}

/-- **The chart pre-image** `{w ∈ ℍ | inv w ∈ U}` of a set `U` (for `U ⊆ ℍ` this is `fwd(U ∩ dom c)`). -/
def chartPre (c : Chart) (U : Set ℂ) : Set ℂ := {w | w ∈ H ∧ c.2.1 w ∈ U}

theorem chartPre_subset_H (c : Chart) (U : Set ℂ) : chartPre c U ⊆ H := fun _ hw => hw.1

theorem isOpen_chartPre (hc : c.IsConformal) {U : Set ℂ} (hU : IsOpen U) : IsOpen (chartPre c U) :=
  hc.1.continuousOn.isOpen_inter_preimage isOpen_H hU

/-- The chart pre-image as an open set. -/
def chartPreOpens (hc : c.IsConformal) (U : Opens ℂ) : Opens ℂ := ⟨chartPre c U, isOpen_chartPre hc U.isOpen⟩

theorem coe_chartPreOpens (hc : c.IsConformal) (U : Opens ℂ) : (chartPreOpens hc U : Set ℂ) = chartPre c U := rfl

theorem chartPreOpens_le (hc : c.IsConformal) (U : Opens ℂ) : chartPreOpens hc U ≤ upperHalfPlaneOpens :=
  chartPre_subset_H c U

/-- `inv` maps the chart pre-image onto `U ∩ dom c`. -/
theorem image_chartPre (hc : c.IsConformal) (U : Set ℂ) : c.2.1 '' chartPre c U = U ∩ c.dom := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwH, hwU⟩, rfl⟩
    exact ⟨hwU, hc.inv_mem_dom hwH⟩
  · rintro ⟨hzU, hzD⟩
    refine ⟨c.1 z, ⟨hc.fwd_mem hzD, ?_⟩, hc.inv_fwd hzD⟩
    rw [hc.inv_fwd hzD]
    exact hzU

/-- `inv` is a conformal bijection of the chart pre-image onto `U ∩ dom c`. -/
theorem isConformalBijection_chartPre (hc : c.IsConformal) (U : Set ℂ) :
    IsConformalBijection c.2.1 (chartPre c U) (U ∩ c.dom) :=
  ⟨hc.1.mono (chartPre_subset_H c U), by
    rw [← image_chartPre hc U]
    exact (hc.injOn.mono (chartPre_subset_H c U)).bijOn_image⟩

end Pre

/-! ### Conformal invariance of the covariance on the chart pre-image -/

section Cov

variable {c : Chart}

/-- **The dual norm of a measure carried by the chart domain.** If `μ'` does not charge `ℍ`-complement of the chart
domain and is the transport of the finite measure `μ` by `inv` (on test functions of the chart domain), then its dual
norm on an open `U ⊆ ℍ` with `U ∖ dom c` open is the dual norm of `μ` on the chart pre-image of `U`. -/
theorem dualNormSq_eq_chartPre (hc : c.IsConformal) {U : Set ℂ} (hU : IsOpen U)
    (hUD : IsOpen (U \ c.dom)) {μ μ' : Measure ℂ} [IsFiniteMeasure μ] (hμ'D : μ' ((c.dom : Set ℂ)ᶜ) = 0)
    (hpair : ∀ f ∈ zeroSpace (c.dom : Set ℂ), ∫ x, f x ∂μ' = ∫ x, f x ∂((μ.restrict H).map c.2.1)) :
    dualNormSq U (zeroSpace U) μ' = dualNormSq (chartPre c U) (zeroSpace (chartPre c U)) μ := by
  set C : Set ℂ := U ∩ c.dom with hCdef
  have hCo : IsOpen C := hU.inter c.dom.isOpen
  have hUC : U \ C = U \ c.dom := by
    ext z; simp only [hCdef, Set.mem_sdiff, mem_inter_iff]; tauto
  have hsplit : dualNormSq U (zeroSpace U) μ' = dualNormSq C (zeroSpace C) μ' := by
    refine Theorem14.GW3Joint.dualNormSq_eq_of_split hCo (hUC ▸ hUD) inter_subset_left ?_
    rw [hUC]
    exact measure_mono_null (fun z hz => hz.2) hμ'D
  rw [hsplit]
  have hpre : IsOpen (chartPre c U) := isOpen_chartPre hc hU
  have hmeas : AEMeasurable c.2.1 (μ.restrict (chartPre c U)) :=
    (hc.1.continuousOn.mono (chartPre_subset_H c U)).aemeasurable hpre.measurableSet
  have hb := isConformalBijection_chartPre hc U
  have hconf : QuantumZipper.K3.IsConformalOnto c.2.1 (chartPre c U) C :=
    SupercriticalConformalCovariance.ZBConformal.isConformalOnto
      (U := ⟨chartPre c U, hpre⟩) (V := ⟨C, hCo⟩) hb
  rw [QuantumZipper.K3.dualNormSq_conformal hconf μ]
  refine Theorem14.GW3Joint.dualNormSq_congr_integral fun f hf => ?_
  have hfD : f ∈ zeroSpace (c.dom : Set ℂ) := ⟨hf.1, hf.2.1, hf.2.2.trans inter_subset_right⟩
  have hmeasH : AEMeasurable c.2.1 (μ.restrict H) := hc.1.continuousOn.aemeasurable isOpen_H.measurableSet
  rw [hpair f hfD, integral_map hmeasH hf.1.continuous.aestronglyMeasurable,
    integral_map hmeas hf.1.continuous.aestronglyMeasurable]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero isOpen_H.measurableSet (chartPre_subset_H c U)
    fun w hw => ?_).symm.symm
  refine image_eq_zero_of_notMem_tsupport fun hsupp => hw.2 ⟨hw.1, (hf.2.2 hsupp).1⟩

theorem integral_add_map {μ₁ μ₂ : Measure ℂ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] (hc : c.IsConformal)
    {f : ℂ → ℝ} (hf : f ∈ zeroSpace (c.dom : Set ℂ)) :
    ∫ x, f x ∂(((μ₁ + μ₂).restrict H).map c.2.1) =
      ∫ x, f x ∂((μ₁.restrict H).map c.2.1) + ∫ x, f x ∂((μ₂.restrict H).map c.2.1) := by
  have hm₁ : AEMeasurable c.2.1 (μ₁.restrict H) := hc.1.continuousOn.aemeasurable isOpen_H.measurableSet
  have hm₂ : AEMeasurable c.2.1 (μ₂.restrict H) := hc.1.continuousOn.aemeasurable isOpen_H.measurableSet
  rw [Measure.restrict_add, AEMeasurable.map_add₀ hm₁ hm₂]
  exact integral_add_measure (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1)
    (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1)

/-- **The dual covariance of measures carried by the chart domain** (`dualNormSq_eq_chartPre` for both measures and
their sum). -/
theorem dualCov_eq_chartPre (hc : c.IsConformal) {U : Set ℂ} (hU : IsOpen U) (hUD : IsOpen (U \ c.dom))
    {μ₁ μ₂ μ₁' μ₂' : Measure ℂ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₁']
    [IsFiniteMeasure μ₂'] (h₁D : μ₁' ((c.dom : Set ℂ)ᶜ) = 0) (h₂D : μ₂' ((c.dom : Set ℂ)ᶜ) = 0)
    (hp₁ : ∀ f ∈ zeroSpace (c.dom : Set ℂ), ∫ x, f x ∂μ₁' = ∫ x, f x ∂((μ₁.restrict H).map c.2.1))
    (hp₂ : ∀ f ∈ zeroSpace (c.dom : Set ℂ), ∫ x, f x ∂μ₂' = ∫ x, f x ∂((μ₂.restrict H).map c.2.1)) :
    dualCov U (zeroSpace U) μ₁' μ₂' = dualCov (chartPre c U) (zeroSpace (chartPre c U)) μ₁ μ₂ := by
  have hsumD : (μ₁' + μ₂') ((c.dom : Set ℂ)ᶜ) = 0 := by rw [Measure.add_apply, h₁D, h₂D, add_zero]
  have hpsum : ∀ f ∈ zeroSpace (c.dom : Set ℂ),
      ∫ x, f x ∂(μ₁' + μ₂') = ∫ x, f x ∂(((μ₁ + μ₂).restrict H).map c.2.1) := fun f hf => by
    rw [integral_add_map hc hf, integral_add_measure (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1)
      (hf.1.continuous.integrable_of_hasCompactSupport hf.2.1), hp₁ f hf, hp₂ f hf]
  unfold dualCov
  rw [dualNormSq_eq_chartPre hc hU hUD hsumD hpsum, dualNormSq_eq_chartPre hc hU hUD h₁D hp₁,
    dualNormSq_eq_chartPre hc hU hUD h₂D hp₂]

/-- `pushTest` as the conformal push-forward of SupercriticalConformalCovariance (equal functions). -/
theorem coe_pushTest_eq_confPushTest (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) :
    ⇑(Chart.pushTest hc φ) = ⇑(confPushTest hc.isConformalBijection φ) := by
  change ⇑(GFF.testIncl c.dom upperHalfPlaneOpens (confPushTest hc.isConformalBijection φ)) = _
  exact GFF.coe_testIncl hc.dom_le _

theorem isFiniteMeasure_testMeasPos (φ : TestOn upperHalfPlaneOpens) : IsFiniteMeasure (testMeasPos φ) :=
  (QuantumZipper.K3.isGoodMeas_withDensity φ.continuous φ.hasCompactSupport).1

theorem isFiniteMeasure_testMeasNeg (φ : TestOn upperHalfPlaneOpens) : IsFiniteMeasure (testMeasNeg φ) :=
  (QuantumZipper.K3.isGoodMeas_withDensity φ.continuous.neg φ.hasCompactSupport.neg).1

/-- **Conformal invariance of the zero-boundary covariance on the chart pre-image.** For an open `U ⊆ ℍ` with
`U ∖ dom c` open and any test functions `φ, ψ` on `ℍ`: `σ_U(pushTest φ, pushTest ψ) = σ_{inv⁻¹ U}(φ, ψ)`. -/
theorem zeroGFFTestCov_pushTest_chartPre (hc : c.IsConformal) {U : Set ℂ} (hU : IsOpen U)
    (hUD : IsOpen (U \ c.dom)) (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov U (Chart.pushTest hc φ) (Chart.pushTest hc ψ) = zeroGFFTestCov (chartPre c U) φ ψ := by
  have hb := hc.isConformalBijection
  have : IsFiniteMeasure (testMeasPos φ) := isFiniteMeasure_testMeasPos φ
  have : IsFiniteMeasure (testMeasNeg φ) := isFiniteMeasure_testMeasNeg φ
  have : IsFiniteMeasure (testMeasPos ψ) := isFiniteMeasure_testMeasPos ψ
  have : IsFiniteMeasure (testMeasNeg ψ) := isFiniteMeasure_testMeasNeg ψ
  have : IsFiniteMeasure (testMeasPos (Chart.pushTest hc φ)) := isFiniteMeasure_testMeasPos _
  have : IsFiniteMeasure (testMeasNeg (Chart.pushTest hc φ)) := isFiniteMeasure_testMeasNeg _
  have : IsFiniteMeasure (testMeasPos (Chart.pushTest hc ψ)) := isFiniteMeasure_testMeasPos _
  have : IsFiniteMeasure (testMeasNeg (Chart.pushTest hc ψ)) := isFiniteMeasure_testMeasNeg _
  have hDc : ∀ χ : TestOn upperHalfPlaneOpens, (c.dom : Set ℂ)ᶜ ⊆ (tsupport (Chart.pushTest hc χ))ᶜ :=
    fun χ => compl_subset_compl.2 (Chart.tsupport_pushTest_subset hc χ)
  have pD : ∀ χ, testMeasPos (Chart.pushTest hc χ) ((c.dom : Set ℂ)ᶜ) = 0 := fun χ =>
    measure_mono_null (hDc χ) (LQGMetric.testMeasPos_compl_tsupport _)
  have nD : ∀ χ, testMeasNeg (Chart.pushTest hc χ) ((c.dom : Set ℂ)ᶜ) = 0 := fun χ =>
    measure_mono_null (hDc χ) (LQGMetric.testMeasNeg_compl_tsupport _)
  have pp : ∀ χ : TestOn upperHalfPlaneOpens, ∀ f ∈ zeroSpace (c.dom : Set ℂ),
      ∫ x, f x ∂(testMeasPos (Chart.pushTest hc χ)) = ∫ x, f x ∂(((testMeasPos χ).restrict H).map c.2.1) :=
    fun χ f hf => by
      rw [coe_pushTest_eq_confPushTest hc χ]
      exact SupercriticalConformalCovariance.ZBConformal.integral_pos_transport_measure hb χ f hf.1.continuous
  have np : ∀ χ : TestOn upperHalfPlaneOpens, ∀ f ∈ zeroSpace (c.dom : Set ℂ),
      ∫ x, f x ∂(testMeasNeg (Chart.pushTest hc χ)) = ∫ x, f x ∂(((testMeasNeg χ).restrict H).map c.2.1) :=
    fun χ f hf => by
      rw [coe_pushTest_eq_confPushTest hc χ]
      exact SupercriticalConformalCovariance.ZBConformal.integral_neg_transport_measure hb χ f hf.1.continuous
  unfold zeroGFFTestCov
  rw [dualCov_eq_chartPre hc hU hUD (pD φ) (pD ψ) (pp φ) (pp ψ),
    dualCov_eq_chartPre hc hU hUD (pD φ) (nD ψ) (pp φ) (np ψ),
    dualCov_eq_chartPre hc hU hUD (nD φ) (pD ψ) (np φ) (pp ψ),
    dualCov_eq_chartPre hc hU hUD (nD φ) (nD ψ) (np φ) (np ψ)]

end Cov

/-! ### Harmonic distributions read through a chart -/

section Harm

variable {c : Chart}

/-- The transported test function of a test function supported in the chart pre-image of `U` is supported in
`U`. -/
theorem tsupport_pushTest_subset_of_chartPre (hc : c.IsConformal) {U : Set ℂ} {φ : TestOn upperHalfPlaneOpens}
    (hφ : tsupport φ ⊆ chartPre c U) : tsupport (Chart.pushTest hc φ) ⊆ U := by
  have hK : IsCompact (tsupport φ) := φ.hasCompactSupport.isCompact
  have hKH : tsupport φ ⊆ H := hφ.trans (chartPre_subset_H c U)
  have hIK : IsCompact (c.2.1 '' tsupport φ) := hK.image_of_continuousOn (hc.1.continuousOn.mono hKH)
  have hsupp : Function.support (Chart.pushTest hc φ) ⊆ c.2.1 '' tsupport φ := by
    intro z hz
    by_cases hzD : z ∈ c.dom
    · rw [Function.mem_support, Chart.pushTest_apply_of_mem hc φ hzD] at hz
      have hφz : φ (c.1 z) ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
      exact ⟨c.1 z, subset_tsupport φ hφz, hc.inv_fwd hzD⟩
    · exact absurd (Chart.pushTest_apply_of_notMem hc φ hzD) hz
  refine (closure_minimal hsupp hIK.isClosed).trans ?_
  rintro _ ⟨w, hw, rfl⟩
  exact (hφ hw).2

/-- **A harmonic distribution read through a chart is harmonic on the chart pre-image** (a harmonic function
composed with the holomorphic `inv` is harmonic; change of variables `z = inv w`). -/
theorem isHarmonicDistOn_pullField (hc : c.IsConformal) {T : DistOn upperHalfPlaneOpens} {U : Set ℂ}
    (hT : IsHarmonicDistOn T U) : IsHarmonicDistOn (Chart.pullField hc T) (chartPre c U) := by
  obtain ⟨v, hv, hTv⟩ := hT
  refine ⟨fun w => v (c.2.1 w), fun w hw => ?_, fun φ hφ => ?_⟩
  · have han : AnalyticAt ℂ c.2.1 w := hc.1.analyticAt (isOpen_H.mem_nhds hw.1)
    exact QuantumZipper.Thm18Asm.LWFar.pocket_harmonicAt_comp han (hv _ hw.2)
  · rw [Chart.pullField_apply, hTv _ (tsupport_pushTest_subset_of_chartPre hc hφ), Chart.integral_mul_pushTest]

end Harm

/-! ### The chart transport of Markov decompositions -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν] {c : Chart}

omit [IsProbabilityMeasure ν] in
/-- **The second moment of the transported projection**: `E|X(pushTest χ)|² = ‖covVec_{U'} χ‖²` for `X` a
zero-boundary GFF on `U` extended by zero and `U' = inv⁻¹ U`. -/
theorem integral_sq_pushTest (hc : c.IsConformal) {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    (hUD : IsOpen ((U : Set ℂ) \ c.dom)) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : GFF.IsZBGFFExtOn U upperHalfPlaneOpens X ν) (χ : TestOn upperHalfPlaneOpens) :
    ∫ ω, (X ω (Chart.pushTest hc χ)) ^ 2 ∂ν = ‖QuantumZipper.Thm11Asm.covVec (chartPre c U) χ‖ ^ 2 := by
  rw [LocalSets.integral_sq_of_isZBGFFExtOn hUH hX, ← real_inner_self_eq_norm_sq,
    ← LocalSets.zeroGFFTestCov_eq_inner_covVec U.isOpen hUH, zeroGFFTestCov_pushTest_chartPre hc U.isOpen hUD,
    LocalSets.zeroGFFTestCov_eq_inner_covVec (isOpen_chartPre hc U.isOpen) (chartPre_subset_H c U),
    real_inner_self_eq_norm_sq]

/-- **The chart transport of the Markov projection.** Let `X` be a zero-boundary GFF on `U ⊆ ℍ` extended by zero
with `h − X` harmonic on `U` (the Markov projection of `h` along `U`), `c` a conformal chart with `U ∖ dom c` open, and
`h' = h ∘ inv + m` with `m` deterministic. Then for every Markov decomposition `h' = X' + Y'` of `h'` along the
chart pre-image `U' = inv⁻¹ U`, `X' = X ∘ inv` almost surely at each test function. -/
theorem ae_markov_pushTest_eq (hc : c.IsConformal) {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    (hUD : IsOpen ((U : Set ℂ) \ c.dom)) {h X : Ω → DistOn upperHalfPlaneOpens}
    (hX : GFF.IsZBGFFExtOn U upperHalfPlaneOpens X ν) (hY : ∀ᵐ ω ∂ν, IsHarmonicDistOn (h ω - X ω) U)
    {h' X' : Ω → DistOn upperHalfPlaneOpens}
    (hd' : GFF.IsMarkovDecomposition (chartPreOpens hc U) upperHalfPlaneOpens h' X' ν)
    (m : TestOn upperHalfPlaneOpens → ℝ) (hh' : ∀ φ, ∀ᵐ ω ∂ν, h' ω φ = h ω (Chart.pushTest hc φ) + m φ)
    (φ : TestOn upperHalfPlaneOpens) : ∀ᵐ ω ∂ν, X' ω φ = X ω (Chart.pushTest hc φ) := by
  set U' : Opens ℂ := chartPreOpens hc U with hU'def
  have hU'le : U' ≤ upperHalfPlaneOpens := chartPreOpens_le hc U
  have hYp : ∀ᵐ ω ∂ν, IsHarmonicDistOn (Chart.pullField hc (h ω - X ω)) U' :=
    hY.mono fun ω hω => isHarmonicDistOn_pullField hc hω
  have hY' := LocalSets.ae_isHarmonicDistOn_of_isMarkovDecomposition hU'le hd'
  have e1 : ∀ f : LQGMetric.MarkovZB.zsSub (U' : Set ℂ), ∀ᵐ ω ∂ν,
      h' ω (LocalSets.lapTest U' f) = X' ω (LocalSets.lapTest U' f) := fun f => by
    filter_upwards [hY'] with ω hω
    have h0 := LocalSets.IsHarmonicDistOn.apply_lapTest_eq_zero U'.isOpen hω hU'le subset_rfl f
    rw [sub_apply] at h0
    linarith
  have e2 : ∀ f : LQGMetric.MarkovZB.zsSub (U' : Set ℂ), ∀ᵐ ω ∂ν,
      h ω (Chart.pushTest hc (LocalSets.lapTest U' f)) = X ω (Chart.pushTest hc (LocalSets.lapTest U' f)) :=
    fun f => by
      filter_upwards [hYp] with ω hω
      have h0 := LocalSets.IsHarmonicDistOn.apply_lapTest_eq_zero U'.isOpen hω hU'le subset_rfl f
      rw [Chart.pullField_apply, sub_apply] at h0
      linarith
  have hgX : ∀ χ, HasGaussianLaw (fun ω => X ω χ) ν := fun χ => hX.gaussian.hasGaussianLaw_eval χ
  have hgX' : ∀ χ, HasGaussianLaw (fun ω => X' ω χ) ν := fun χ =>
    hd'.isZBGFFExtOn.gaussian.hasGaussianLaw_eval χ
  have hm0 : ∀ f : LQGMetric.MarkovZB.zsSub (U' : Set ℂ), m (LocalSets.lapTest U' f) = 0 := fun f => by
    have hae : (fun _ : Ω => m (LocalSets.lapTest U' f)) =ᵐ[ν] fun ω =>
        X' ω (LocalSets.lapTest U' f) - X ω (Chart.pushTest hc (LocalSets.lapTest U' f)) := by
      filter_upwards [hh' (LocalSets.lapTest U' f), e1 f, e2 f] with ω a b c'
      linarith
    have i1 := (hgX' (LocalSets.lapTest U' f)).memLp_two.integrable one_le_two
    have i2 := (hgX (Chart.pushTest hc (LocalSets.lapTest U' f))).memLp_two.integrable one_le_two
    have := integral_congr_ae hae
    rw [integral_const, integral_sub i1 i2, hd'.isZBGFFExtOn.centered, hX.centered, probReal_univ, one_smul,
      sub_zero] at this
    exact this
  obtain ⟨f, hf, hlim⟩ := LocalSets.exists_tendsto_integral_sq_of_isMarkovDecomposition hU'le hd' φ
  set D : Ω → ℝ := fun ω => X' ω φ - X ω (Chart.pushTest hc φ) with hDdef
  have hDm : MemLp D 2 ν := (hgX' φ).memLp_two.sub (hgX _).memLp_two
  have hsplit : ∀ n, ∀ᵐ ω ∂ν, D ω = (X' ω φ - h' ω (LocalSets.lapTest U' (f n))) +
      X ω (Chart.pushTest hc (LocalSets.lapTest U' (f n) - φ)) := fun n => by
    filter_upwards [hh' (LocalSets.lapTest U' (f n)), e2 (f n)] with ω a b
    rw [map_sub (Chart.pushTest hc), map_sub (X ω), a, b, hm0, hDdef]
    ring
  have hB : ∀ n, ∫ ω, (X ω (Chart.pushTest hc (LocalSets.lapTest U' (f n) - φ))) ^ 2 ∂ν =
      ‖QuantumZipper.K3.gradFeat (U' : Set ℂ) (f n).1 - QuantumZipper.Thm11Asm.covVec (U' : Set ℂ) φ‖ ^ 2 :=
    fun n => by
      rw [integral_sq_pushTest hc hUH hUD hX, ← coe_chartPreOpens hc U, ← hU'def,
        LocalSets.covVec_sub U'.isOpen hU'le, LocalSets.covVec_lapTest hU'le U'.isOpen hU'le subset_rfl]
  have hle : ∀ n, ∫ ω, D ω ^ 2 ∂ν ≤ 2 * ∫ ω, (X' ω φ - h' ω (LocalSets.lapTest U' (f n))) ^ 2 ∂ν +
      2 * ‖QuantumZipper.K3.gradFeat (U' : Set ℂ) (f n).1 -
        QuantumZipper.Thm11Asm.covVec (U' : Set ℂ) φ‖ ^ 2 := fun n => by
    rw [← hB n, ← integral_const_mul, ← integral_const_mul]
    have iA := (LocalSets.memLp_markov_sub_lapTest hU'le hd' φ (f n)).integrable_sq
    have iB := ((hgX (Chart.pushTest hc (LocalSets.lapTest U' (f n) - φ))).memLp_two).integrable_sq
    rw [← integral_add (iA.const_mul 2) (iB.const_mul 2)]
    refine integral_mono_ae hDm.integrable_sq ((iA.const_mul 2).add (iB.const_mul 2)) ?_
    filter_upwards [hsplit n] with ω hω
    rw [hω]
    set a := X' ω φ - h' ω (LocalSets.lapTest U' (f n))
    set b := X ω (Chart.pushTest hc (LocalSets.lapTest U' (f n) - φ))
    have e : (a + b) ^ 2 = 2 * a ^ 2 + 2 * b ^ 2 - (a - b) ^ 2 := by ring
    rw [e]
    linarith [sq_nonneg (a - b)]
  have hlimB : Tendsto (fun n => ‖QuantumZipper.K3.gradFeat (U' : Set ℂ) (f n).1 -
      QuantumZipper.Thm11Asm.covVec (U' : Set ℂ) φ‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => QuantumZipper.K3.gradFeat (U' : Set ℂ) (f n).1 -
        QuantumZipper.Thm11Asm.covVec (U' : Set ℂ) φ) atTop (𝓝 0) := by
      simpa using hf.sub (tendsto_const_nhds (x := QuantumZipper.Thm11Asm.covVec (U' : Set ℂ) φ))
    simpa using (continuous_norm.tendsto _ |>.comp h1).pow 2
  have hlimS : Tendsto (fun n => 2 * ∫ ω, (X' ω φ - h' ω (LocalSets.lapTest U' (f n))) ^ 2 ∂ν +
      2 * ‖QuantumZipper.K3.gradFeat (U' : Set ℂ) (f n).1 -
        QuantumZipper.Thm11Asm.covVec (U' : Set ℂ) φ‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hlim.const_mul 2).add (hlimB.const_mul 2)
  have hint0 : ∫ ω, D ω ^ 2 ∂ν ≤ 0 := ge_of_tendsto' hlimS hle
  have hint : ∫ ω, D ω ^ 2 ∂ν = 0 := le_antisymm hint0 (integral_nonneg fun ω => sq_nonneg _)
  have hzero := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (D ω)) hDm.integrable_sq).1 hint
  filter_upwards [hzero] with ω hω
  have : D ω = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hω
  simp only [hDdef] at this
  linarith

/-- **The chart transport of the Markov complement**: `Y' = Y ∘ inv + m` (`ae_markov_pushTest_eq`). -/
theorem ae_markovCompl_pushTest_eq (hc : c.IsConformal) {U : Opens ℂ} (hUH : (U : Set ℂ) ⊆ H)
    (hUD : IsOpen ((U : Set ℂ) \ c.dom)) {h X : Ω → DistOn upperHalfPlaneOpens}
    (hX : GFF.IsZBGFFExtOn U upperHalfPlaneOpens X ν) (hY : ∀ᵐ ω ∂ν, IsHarmonicDistOn (h ω - X ω) U)
    {h' X' : Ω → DistOn upperHalfPlaneOpens}
    (hd' : GFF.IsMarkovDecomposition (chartPreOpens hc U) upperHalfPlaneOpens h' X' ν)
    (m : TestOn upperHalfPlaneOpens → ℝ) (hh' : ∀ φ, ∀ᵐ ω ∂ν, h' ω φ = h ω (Chart.pushTest hc φ) + m φ)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂ν, h' ω φ - X' ω φ = h ω (Chart.pushTest hc φ) - X ω (Chart.pushTest hc φ) + m φ := by
  filter_upwards [ae_markov_pushTest_eq hc hUH hUD hX hY hd' m hh' φ, hh' φ] with ω h1 h2
  rw [h1, h2]
  ring

end Main

end MarkovChart

end Restart

end InteractingSLE
