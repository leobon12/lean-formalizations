/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtDLocal
import InteractingSLE.Spec.Sec7.LocalExtDBridge
import InteractingSLE.Spec.Sec7.LocalExtA3Joint
import LQGMetric.Papers.CONF.S3D127D1

/-!
# Aux. lemma 55, step 5 (locality): the hulls stay local for the recoded field under `Q`

Packet PROVE-LOCEXT-D, item 2. Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L196–L210, p. 250): under
`Q = Z · P` (`srcMeasure`) every hull `K_τ`, `τ ≤ S` a stopping time of the frozen driving filtration, is a local set of the
recoded field `h₀ = h + f − q` (`recode`).

The general tilt `IsLocalSet.withDensity_exp_neg` (`LocalExtDLocal`) applies with the source test functions
`s_k = v_{n_k}` (`srcTest`, energy-Cauchy by `greenEnergy_pairSeq_lt`), `Λ = srcPair`, `Z = srcDensity`, and
`c = f − q` (`recodeShift`) as a distribution. The Dirichlet pairings of `c` are those of the source:
`∫ (−Δg/2π)(f − q) = ∫ g (−Δf/2π) = ∫ g v` (Green's identity for the smooth `f`, `q` harmonic on `ℍ`), and
`∫ v_{n_k} g → ∫ v g` (`tendsto_integral_mul_srcTest`).

* `harmonicOnNhd_qExt`: `q` is harmonic on `ℍ`;
* `isCovCauchy_srcTest`: the source test functions are energy-Cauchy;
* `tendsto_integral_srcTest_mul_eq_recode`: the Dirichlet pairings of `f − q`;
* **`isLocalSet_recode_srcMeasure`**: step 5's locality;
* **`condExp_recode_srcMeasure_eq_twoSeedKernel_of_pos`**: step 5's kernel half, unconditional (PROVE-LOCEXT-A3's
  `srcJointKernelStatement` discharges the named statement of `condExp_recode_srcMeasure_eq_twoSeedKernel`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal NNReal Laplacian

universe u

namespace InteractingSLE

namespace LocalExt

open QuantumZipper QuantumZipper.Thm11Asm LQGMetric LocalSets

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

/-! ### `q` is harmonic on `ℍ` -/

theorem analyticAt_qHolo_of_mem_H {z : ℂ} (hz : 0 < z.im) : AnalyticAt ℂ (qHolo κ xL xR ρL ρR) z := by
  refine analyticAt_const.mul ((Finset.analyticAt_fun_sum _ fun i _ => ?_).add
    (Finset.analyticAt_fun_sum _ fun i _ => ?_))
  · refine analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).clog ?_)
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    show (z - (xL i : ℂ)).im ≠ 0
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact hz.ne'
  · refine analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).clog ?_)
    refine Complex.mem_slitPlane_iff.2 (Or.inr ?_)
    show ((xR i : ℂ) - z).im ≠ 0
    rw [Complex.sub_im, Complex.ofReal_im, zero_sub, ne_eq, neg_eq_zero]
    exact hz.ne'

/-- **`q` is harmonic on `ℍ`** (the imaginary part of a holomorphic function there). -/
theorem harmonicOnNhd_qExt : InnerProductSpace.HarmonicOnNhd (qExt κ xL xR ρL ρR) H := fun z hz => by
  have h := (analyticAt_qHolo_of_mem_H (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) hz).harmonicAt_im
  have he : (fun z => (qHolo κ xL xR ρL ρR z).im) = qExt κ xL xR ρL ρR :=
    funext fun z => (qExt_eq_im_qHolo z).symm
  rwa [he] at h

/-! ### The source test functions -/

theorem zeroGFFTestCov_H_eq_greenEnergy (φ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov H φ φ = greenEnergy φ φ := by
  rw [show H = (upperHalfPlaneOpens : Set ℂ) from rfl,
    LQGMetric.zeroGFFTestCov_eq_green (V := upperHalfPlaneOpens) subset_rfl GFF.isConformalOnto_id_H φ φ]
  rfl

/-- **The source test functions `v_{n_k}` are energy-Cauchy.** -/
theorem isCovCauchy_srcTest (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    IsCovCauchy (srcTest κ ρL ρR hF hr) := by
  intro N n m hn hm
  rw [zeroGFFTestCov_H_eq_greenEnergy]
  have e : ⇑(srcTest κ ρL ρR hF hr n - srcTest κ ρL ρR hF hr m) = fun z =>
      vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr n) z - vApprox κ xL xR ρL ρR r (pairSeq κ ρL ρR hF hr m) z := by
    funext z; rfl
  rw [e]
  exact (greenEnergy_pairSeq_lt hF hr ((strictMono_pairSeq hF hr).monotone hn)
    ((strictMono_pairSeq hF hr).monotone hm)).le

/-- **The Dirichlet pairings of `f − q` are those of the source**: for `g ∈ C_c^∞(U)`, `U ⊆ ℍ` open,
`∫ v_{n_k} g → ∫ (−Δg/2π)(f − q)`. -/
theorem tendsto_integral_srcTest_mul_eq_recode (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (U : Opens ℂ) (hU : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)) :
    Tendsto (fun k => ∫ z, srcTest κ ρL ρR hF hr k z * g.1 z) atTop
      (𝓝 (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (recodeShift κ xL xR ρL ρR r)
        (lapTest U g))) := by
  have hgc : Continuous g.1 := g.2.1.continuous
  have hgs : HasCompactSupport g.1 := g.2.2.1
  have hgU : tsupport g.1 ⊆ (U : Set ℂ) := g.2.2.2
  obtain ⟨C, hC⟩ := hgc.bounded_above_of_compact_support hgs
  have hlim := tendsto_integral_mul_srcTest (κ := κ) (ρL := ρL) (ρR := ρR) hF hr hgc.continuousOn
    (C := C) fun z _ => (Real.norm_eq_abs _).symm.le.trans (hC z) |>.trans_eq' rfl
  -- the limit `∫ g v` is the pairing of `f − q`
  have hlap : ⇑(lapTest U g) = fun z => -(2 * Real.pi)⁻¹ * Δ g.1 z := by
    rw [coe_lapTest hU]; rfl
  have hfC : ContDiff ℝ 2 (fCut κ xL xR ρL ρR r) := contDiff_fCut hF hr
  have hg2 : ContDiff ℝ 2 g.1 := g.2.1.of_le (by simp)
  have hT : SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (recodeShift κ xL xR ρL ρR r)
      (lapTest U g) = ∫ z, g.1 z * vSrc κ xL xR ρL ρR r z := by
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply (continuousOn_recodeShift hF hr)]
    have i1 : Integrable fun z => lapTest U g z * fCut κ xL xR ρL ρR r z := by
      have := Coupling.MartMeans2.integrable_mul_test_of_continuousOn (hfC.continuous.continuousOn (s := H))
        (lapTest U g) (lapTest U g).tsupport_subset
      exact this.congr (ae_of_all _ fun z => mul_comm _ _)
    have i2 : Integrable fun z => lapTest U g z * qExt κ xL xR ρL ρR z := by
      have := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
        (continuousOn_qExt (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR))
        (lapTest U g) (lapTest U g).tsupport_subset
      exact this.congr (ae_of_all _ fun z => mul_comm _ _)
    have e1 : ∫ z, lapTest U g z * recodeShift κ xL xR ρL ρR r z =
        (∫ z, lapTest U g z * fCut κ xL xR ρL ρR r z) - ∫ z, lapTest U g z * qExt κ xL xR ρL ρR z := by
      rw [← integral_sub i1 i2]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [recodeShift]; ring
    -- `q` is harmonic on `U`
    have e2 : ∫ z, lapTest U g z * qExt κ xL xR ρL ρR z = 0 := by
      have h := LQGMetric.HarmLoc.integral_mul_cmTest_of_harmonic U.isOpen
        ((harmonicOnNhd_qExt (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)).mono hU)
        (MarkovZB.zsTest g.2) hgU
      rw [← h]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      rw [coe_lapTest hU]
      exact mul_comm _ _
    -- Green's identity for the smooth `f`
    have e3 : ∫ z, lapTest U g z * fCut κ xL xR ρL ρR r z = ∫ z, g.1 z * vSrc κ xL xR ρL ρR r z := by
      have hG := LQGMetric.CONF.ZBM.integral_mul_laplacian_comm hfC hg2 hgs
      have e4 : (fun z => lapTest U g z * fCut κ xL xR ρL ρR r z) =
          fun z => -(2 * Real.pi)⁻¹ * (fCut κ xL xR ρL ρR r z * Δ g.1 z) := by
        funext z; rw [hlap]; ring
      rw [e4, integral_const_mul, hG, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ H
      · simp only [vSrc, Set.indicator_of_mem hz, vDens, K3.greenDensity]
        ring
      · have hgz : g.1 z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hU (hgU h'))
        simp [hgz]
    rw [e1, e2, sub_zero, e3]
  rw [hT]
  refine hlim.congr fun k => ?_
  exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)

/-! ### Step 5's locality -/

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}

theorem srcMeasure_eq_withDensity_exp (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    srcMeasure κ ρL ρR P hF hr h = P.withDensity fun ω => ENNReal.ofReal (Real.exp
      (-srcPair κ ρL ρR hF hr (h ω) + (srcCentre κ xL xR ρL ρR r - srcNorm κ xL xR ρL ρR r / 2))) := by
  unfold srcMeasure srcDensity
  congr 1
  funext ω
  congr 2
  ring

/-- **Aux. lemma 55, step 5 (locality).** For a coupling with an admissible seed, a seed radius `r` and a stopping time
`τ ≤ S` of the frozen driving filtration, the hull `K_τ` is a local set of the recoded field `h₀ = h + f − q` under
`Q = srcMeasure`. -/
theorem isLocalSet_recode_srcMeasure (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω) :
    IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
      (fun ω => recode κ xL xR ρL ρR r (h ω)) (srcMeasure κ ρL ρR P hF hr h) := by
  have hP : IsProbabilityMeasure P := hC.1.1.isProbabilityMeasure'
  have hgood := ae_isGoodPath hC.1 hκ
  have hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hgood, hτS] with ω hg hτω
    exact lt_of_le_of_lt hτω (localStopPath_lt hg.1 hF hr hseed hg.2)
  obtain ⟨hX', hker⟩ := hC.2.2.2
  obtain ⟨hloc, -⟩ := hker τ hτ hτζ
  have hYg := hC.2.2.1 (bheAt κ ρL ρR xL xR) (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR)
  obtain ⟨C0, hC0⟩ := (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR).2.1
  have hconv := ae_tendsto_srcPair (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
    (continuousOn_of_isBoundedHarmonicExtension (isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR)) hC0 hYg
  have hZ : ∫⁻ ω, ENNReal.ofReal (Real.exp (-srcPair κ ρL ρR hF hr (h ω) +
      (srcCentre κ xL xR ρL ρR r - srcNorm κ xL xR ρL ρR r / 2))) ∂P = 1 := by
    rw [← lintegral_srcDensity hκ hC hF hr hseed]
    refine lintegral_congr fun ω => ?_
    unfold srcDensity
    congr 2
    ring
  rw [srcMeasure_eq_withDensity_exp hF hr]
  exact IsLocalSet.withDensity_exp_neg hloc hC.2.1 (isCovCauchy_srcTest hF hr) (measurable_srcPair hF hr) hconv hZ
    (tendsto_integral_srcTest_mul_eq_recode hF hr)

/-- **Aux. lemma 55, step 5 (kernel half), unconditional**: under `Q = srcMeasure`, the recoded field `h₀ = h + f − q` has
at every driving stop `τ ≤ S` the frozen kernel of the two-seed word (weights `(seedSumL, seedSumR)` at the merged seed
positions), `Q`-almost surely on `{supp φ ∩ K_τ = ∅}`. -/
theorem condExp_recode_srcMeasure_eq_twoSeedKernel_of_pos (hκ : 0 < κ)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτS : ∀ᵐ ω ∂P, τ ω ≤ localStopPath r (ζ ω) fun t => W t ω)
    {u₂ : Ω → ℂ → ℝ}
    (hu₂ : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun _ : Fin 1 => seedSumL xL ρL) (fun _ : Fin 1 => seedSumR xR ρR)
        (fun _ => seedPosL xL W VL τ ω) (fun _ => seedPosR xR W VR τ ω))
      (forceJumpSet (fun _ : Fin 1 => seedPosL xL W VL τ ω) (fun _ : Fin 1 => seedPosR xR W VR τ ω)) (u₂ ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂(srcMeasure κ ρL ρR P hF hr h),
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
      (srcMeasure κ ρL ρR P hF hr h)[fun ω' =>
          Complex.exp (Complex.I * (recode κ xL xR ρL ρR r (h ω') φ : ℂ)) | hτ.measurableSpace] ω =
        Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)
            (u₂ ω) z * φ z : ℝ) : ℂ) -
          (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) :=
  condExp_recode_srcMeasure_eq_twoSeedKernel (srcJointKernelStatement hκ) hκ hC hF hr hseed hX hτ hτS hu₂ φ

end LocalExt

end InteractingSLE
