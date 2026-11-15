/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.MartMeans2Sub

/-!
# Conformal invariance of the zero-boundary covariance for test functions not supported in the subdomain

Packet PROVE-LOCEXT-I. PROVE-CPL-MART2's `IsConformal.zeroGFFTestCov_pushTest_sub` transports the dual Dirichlet
covariance `zeroGFFTestCov O φ φ` along a conformal chart only for test functions **supported in `O`**. A conditional
zero-boundary GFF on a random subdomain (`IsCondZeroBoundaryGFF`, the two-step model of a local set) quantifies over
**all** test functions of `ℍ`, so moving a local set through a chart (Aux. lemma 53 in the half-plane) needs the
statement for every test function. Here:

* `dualCov_transport_zeroSpace`: SupercriticalConformalCovariance's `dualCov_transport` with the pairing identities
  required only against the test space `zeroSpace V` (the dual norms only see these);
* `IsConformal.integral_max_pushTest_mul`, `…_neg_…`: for `f` smooth with compact support in `inv '' O`,
  `∫ (pushTest φ)⁺ f = ∫ φ⁺ · 1_O (f ∘ inv)` (and for the negative parts) — through a cutoff `χ ∈ C_c^∞(O)` equal to `1`
  on `fwd(supp f)` and SupercriticalConformalCovariance's substitution `integral_max_confPushTest` for `χ φ`;
* **`IsConformal.zeroGFFTestCov_pushTest`**: for every `O ⊆ ℍ` open and **all** test functions `φ, ψ` on `ℍ`,
  `zeroGFFTestCov (inv '' O) (pushTest φ) (pushTest ψ) = zeroGFFTestCov O φ ψ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace Function
open QuantumZipper (H isOpen_H zeroGFFTestCov testMeasPos testMeasNeg)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance (IsConformalBijection confPushTest)

namespace InteractingSLE

namespace Chart

/-- SupercriticalConformalCovariance's covariance transport with the pairing identities required only on the
test space of the target domain. -/
theorem dualCov_transport_zeroSpace {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
    {μ₁ μ₂ μ₁' μ₂' : Measure ℂ} [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] [IsFiniteMeasure μ₁']
    [IsFiniteMeasure μ₂']
    (hpair₁ : ∀ f ∈ QuantumZipper.zeroSpace V, ∫ y, f y ∂μ₁' = ∫ y, f y ∂((μ₁.restrict U).map φ))
    (hpair₂ : ∀ f ∈ QuantumZipper.zeroSpace V, ∫ y, f y ∂μ₂' = ∫ y, f y ∂((μ₂.restrict U).map φ)) :
    QuantumZipper.dualCov V (QuantumZipper.zeroSpace V) μ₁' μ₂' =
      QuantumZipper.dualCov U (QuantumZipper.zeroSpace U) μ₁ μ₂ := by
  have hae₁ : AEMeasurable φ (μ₁.restrict U) :=
    ContinuousOn.aemeasurable hφ.1.continuousOn U.isOpen.measurableSet
  have hae₂ : AEMeasurable φ (μ₂.restrict U) :=
    ContinuousOn.aemeasurable hφ.1.continuousOn U.isOpen.measurableSet
  have hpairAdd : ∀ f ∈ QuantumZipper.zeroSpace V,
      ∫ y, f y ∂(μ₁' + μ₂') = ∫ y, f y ∂(((μ₁ + μ₂).restrict U).map φ) := by
    intro f hf
    have hfint₁' : Integrable f μ₁' := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₂' : Integrable f μ₂' := hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₁ : Integrable f ((μ₁.restrict U).map φ) :=
      hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    have hfint₂ : Integrable f ((μ₂.restrict U).map φ) :=
      hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
    rw [Measure.restrict_add, AEMeasurable.map_add₀ hae₁ hae₂,
      integral_add_measure hfint₁' hfint₂', integral_add_measure hfint₁ hfint₂, hpair₁ f hf, hpair₂ f hf]
  unfold QuantumZipper.dualCov
  rw [SupercriticalConformalCovariance.ZBConformal.dualNormSq_transport hφ hpairAdd,
    SupercriticalConformalCovariance.ZBConformal.dualNormSq_transport hφ hpair₁,
    SupercriticalConformalCovariance.ZBConformal.dualNormSq_transport hφ hpair₂]

variable {c : Chart} {O : Opens ℂ}

/-- A smooth compactly supported cutoff on `O ⊆ ℍ` equal to `1` on a compact `K ⊆ O`. -/
theorem exists_cutoff_of_isCompact (hO : (O : Set ℂ) ⊆ H) {K : Set ℂ} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ χ : TestOn upperHalfPlaneOpens, tsupport χ ⊆ O ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨W, hWo, hKW, hWO, hWc⟩ := exists_open_between_and_isCompact_closure hK O.isOpen hKO
  obtain ⟨χ, hχ, -, hsupp, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hWo hK.isClosed hKW
  have hts : tsupport χ = closure W := by rw [tsupport, hsupp]
  refine ⟨⟨χ, hχ, ?_, ?_⟩, ?_, fun x hx => (hone x).1 hx⟩
  · rw [HasCompactSupport, hts]
    exact hWc
  · rw [hts]
    exact hWO.trans hO
  · change tsupport χ ⊆ O
    rw [hts]
    exact hWO

/-- The product of a test function with a cutoff. -/
def cutTest (χ φ : TestOn upperHalfPlaneOpens) : TestOn upperHalfPlaneOpens where
  toFun := fun z => χ z * φ z
  contDiff' := χ.contDiff.mul φ.contDiff
  hasCompactSupport' := χ.hasCompactSupport.mul_right
  tsupport_subset' := (tsupport_mul_subset_left).trans χ.tsupport_subset

@[simp] theorem cutTest_apply (χ φ : TestOn upperHalfPlaneOpens) (z : ℂ) : cutTest χ φ z = χ z * φ z := rfl

theorem tsupport_cutTest_subset (χ φ : TestOn upperHalfPlaneOpens) : tsupport (cutTest χ φ) ⊆ tsupport χ :=
  tsupport_mul_subset_left

/-- The generic substitution behind both parts: for `g : ℝ → ℝ` with `g 0 = 0`, if `∫ g(push ψ) f = ∫ g(ψ) f ∘ inv`
for every test function `ψ` supported in `O`, then the same holds for every test function `φ`, with `f ∘ inv`
restricted to `O`, whenever `f` has compact support in `inv '' O`. -/
theorem IsConformal.integral_comp_pushTest_mul (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H) (g : ℝ → ℝ)
    (hg0 : g 0 = 0)
    (hsub : ∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ O → ∀ u : ℂ → ℝ,
      ∫ y, g (pushTest hc ψ y) * u y = ∫ x, g (ψ x) * u (c.2.1 x))
    (φ : TestOn upperHalfPlaneOpens) {f : ℂ → ℝ} (hfs : HasCompactSupport f)
    (hfO : tsupport f ⊆ c.2.1 '' (O : Set ℂ)) :
    ∫ y, g (pushTest hc φ y) * f y = ∫ x, g (φ x) * (O : Set ℂ).indicator (fun w => f (c.2.1 w)) x := by
  -- the compact image of the support of `f` and a cutoff equal to `1` there
  have hdom : c.2.1 '' (O : Set ℂ) ⊆ c.dom := fun z ⟨w, hw, hz⟩ => hz ▸ hc.inv_mem_dom (hO hw)
  set K := c.1 '' tsupport f with hKdef
  have hK : IsCompact K :=
    hfs.isCompact.image_of_continuousOn (hc.differentiableOn_fwd.continuousOn.mono (hfO.trans hdom))
  have hKO : K ⊆ O := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hfO hy
    rw [hc.2.2 w (hO hw)]
    exact hw
  obtain ⟨χ, hχO, hχK⟩ := exists_cutoff_of_isCompact hO hK hKO
  have hψO : tsupport (cutTest χ φ) ⊆ O := (tsupport_cutTest_subset χ φ).trans hχO
  -- on the support of `f`, the transported test functions of `φ` and `χ φ` agree
  have h1 : ∀ y, g (pushTest hc φ y) * f y = g (pushTest hc (cutTest χ φ) y) * f y := by
    intro y
    by_cases hy : y ∈ tsupport f
    · have hyd : y ∈ c.dom := hdom (hfO hy)
      rw [pushTest_apply_of_mem hc φ hyd, pushTest_apply_of_mem hc _ hyd, cutTest_apply,
        hχK _ (mem_image_of_mem _ hy), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]
  -- on `O`, `f ∘ inv` vanishes off `K`, where `χ = 1`
  have h2 : ∀ x, g (cutTest χ φ x) * f (c.2.1 x) =
      g (φ x) * (O : Set ℂ).indicator (fun w => f (c.2.1 w)) x := by
    intro x
    by_cases hx : x ∈ (O : Set ℂ)
    · rw [indicator_of_mem hx]
      by_cases hfx : c.2.1 x ∈ tsupport f
      · have hxK : x ∈ K := ⟨c.2.1 x, hfx, hc.2.2 x (hO hx)⟩
        rw [cutTest_apply, hχK x hxK, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hfx, mul_zero, mul_zero]
    · rw [indicator_of_notMem hx, mul_zero, image_eq_zero_of_notMem_tsupport (fun h => hx (hψO h)), hg0,
        zero_mul]
  simp_rw [h1]
  rw [hsub _ hψO f]
  simp_rw [h2]

/-- **Positive parts**: `∫ (pushTest φ)⁺ f = ∫ φ⁺ · 1_O (f ∘ inv)` for `f` with compact support in `inv '' O`. -/
theorem IsConformal.integral_max_pushTest_mul (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H)
    (φ : TestOn upperHalfPlaneOpens) {f : ℂ → ℝ} (hfs : HasCompactSupport f)
    (hfO : tsupport f ⊆ c.2.1 '' (O : Set ℂ)) :
    ∫ y, max (pushTest hc φ y) 0 * f y =
      ∫ x, max (φ x) 0 * (O : Set ℂ).indicator (fun w => f (c.2.1 w)) x := by
  refine hc.integral_comp_pushTest_mul hO (fun a => max a 0) (by simp) (fun ψ hψ u => ?_) φ hfs hfO
  rw [hc.coe_pushTest_eq_confPushTest hO ψ hψ]
  exact SupercriticalConformalCovariance.ZBConformal.integral_max_confPushTest (hc.isConformalBijection_sub hO)
    (testOnSub ψ hψ) u

/-- **Negative parts**: `∫ (pushTest φ)⁻ f = ∫ φ⁻ · 1_O (f ∘ inv)` for `f` with compact support in `inv '' O`. -/
theorem IsConformal.integral_max_neg_pushTest_mul (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H)
    (φ : TestOn upperHalfPlaneOpens) {f : ℂ → ℝ} (hfs : HasCompactSupport f)
    (hfO : tsupport f ⊆ c.2.1 '' (O : Set ℂ)) :
    ∫ y, max (-pushTest hc φ y) 0 * f y =
      ∫ x, max (-φ x) 0 * (O : Set ℂ).indicator (fun w => f (c.2.1 w)) x := by
  refine hc.integral_comp_pushTest_mul hO (fun a => max (-a) 0) (by simp) (fun ψ hψ u => ?_) φ hfs hfO
  rw [hc.coe_pushTest_eq_confPushTest hO ψ hψ]
  exact SupercriticalConformalCovariance.ZBConformal.integral_max_neg_confPushTest
    (hc.isConformalBijection_sub hO) (testOnSub ψ hψ) u

/-- The pairing of `f` with the image under `inv` of a measure restricted to `O`. -/
theorem IsConformal.integral_map_restrict (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H) (μ : Measure ℂ)
    {f : ℂ → ℝ} (hfc : Continuous f) :
    ∫ y, f y ∂((μ.restrict O).map c.2.1) = ∫ x, (O : Set ℂ).indicator (fun w => f (c.2.1 w)) x ∂μ := by
  have hae : AEMeasurable c.2.1 (μ.restrict O) :=
    ContinuousOn.aemeasurable (hc.1.continuousOn.mono hO) O.isOpen.measurableSet
  rw [integral_map hae hfc.aestronglyMeasurable, integral_indicator O.isOpen.measurableSet]

/-- **Conformal invariance of the zero-boundary covariance on a subdomain, for all test functions**: for an open
`O ⊆ ℍ` and every pair of test functions `φ, ψ` on `ℍ` (not necessarily supported in `O`),
`zeroGFFTestCov (inv '' O) (pushTest φ) (pushTest ψ) = zeroGFFTestCov O φ ψ`. -/
theorem IsConformal.zeroGFFTestCov_pushTest (hc : c.IsConformal) (hO : (O : Set ℂ) ⊆ H)
    (φ ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (c.2.1 '' (O : Set ℂ)) (pushTest hc φ) (pushTest hc ψ) = zeroGFFTestCov O φ ψ := by
  have hfin : ∀ ρ : TestOn upperHalfPlaneOpens, IsFiniteMeasure (testMeasPos ρ) ∧ IsFiniteMeasure (testMeasNeg ρ) :=
    fun ρ => ⟨(QuantumZipper.K3.isGoodMeas_withDensity ρ.continuous ρ.hasCompactSupport).1,
      (QuantumZipper.K3.isGoodMeas_withDensity ρ.continuous.neg ρ.hasCompactSupport.neg).1⟩
  have := (hfin φ).1; have := (hfin φ).2; have := (hfin ψ).1; have := (hfin ψ).2
  have := (hfin (pushTest hc φ)).1; have := (hfin (pushTest hc φ)).2
  have := (hfin (pushTest hc ψ)).1; have := (hfin (pushTest hc ψ)).2
  have hV : ((c.imageOpens O : Opens ℂ) : Set ℂ) = c.2.1 '' (O : Set ℂ) := hc.coe_imageOpens hO
  have hbij := hc.isConformalBijection_sub hO
  -- the pairings against the test space of `inv '' O`
  have hpos : ∀ ρ : TestOn upperHalfPlaneOpens, ∀ f ∈ QuantumZipper.zeroSpace (c.imageOpens O),
      ∫ y, f y ∂(testMeasPos (pushTest hc ρ)) = ∫ y, f y ∂(((testMeasPos ρ).restrict O).map c.2.1) := by
    intro ρ f hf
    have hfO : tsupport f ⊆ c.2.1 '' (O : Set ℂ) := hV ▸ hf.2.2
    rw [hc.integral_map_restrict hO _ hf.1.continuous,
      QuantumZipper.K3.integral_testMeasPos_K3 (pushTest hc ρ).continuous.measurable,
      QuantumZipper.K3.integral_testMeasPos_K3 ρ.continuous.measurable]
    exact hc.integral_max_pushTest_mul hO ρ hf.2.1 hfO
  have hneg : ∀ ρ : TestOn upperHalfPlaneOpens, ∀ f ∈ QuantumZipper.zeroSpace (c.imageOpens O),
      ∫ y, f y ∂(testMeasNeg (pushTest hc ρ)) = ∫ y, f y ∂(((testMeasNeg ρ).restrict O).map c.2.1) := by
    intro ρ f hf
    have hfO : tsupport f ⊆ c.2.1 '' (O : Set ℂ) := hV ▸ hf.2.2
    rw [hc.integral_map_restrict hO _ hf.1.continuous,
      QuantumZipper.K3.integral_testMeasNeg_K3 (pushTest hc ρ).continuous.measurable,
      QuantumZipper.K3.integral_testMeasNeg_K3 ρ.continuous.measurable]
    exact hc.integral_max_neg_pushTest_mul hO ρ hf.2.1 hfO
  rw [← hV]
  unfold zeroGFFTestCov
  rw [dualCov_transport_zeroSpace hbij (hpos φ) (hpos ψ), dualCov_transport_zeroSpace hbij (hpos φ) (hneg ψ),
    dualCov_transport_zeroSpace hbij (hneg φ) (hpos ψ), dualCov_transport_zeroSpace hbij (hneg φ) (hneg ψ)]

end Chart

end InteractingSLE
