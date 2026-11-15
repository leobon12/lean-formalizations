/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.MartMeans2Chart
import InteractingSLE.Spec.Coupling.ExpMartingale
import QuantumZipper.Proofs.Zipper.B5VHccZero
import QuantumZipper.Proofs.RS.HullBasics

/-!
# Integrable pairings of a coupled field, and Lemma 7.1's martingale clause from the chart form

Packet PROVE-CPL-MART2, part (2), continued. The martingale clause of Lemma 7.1
(`Sec7.Lemma71.HasTwoSeedMartingaleMeans`, consumed by PROVE-LEMMA71's `lemma71TraceReferenceStatement_of_mappedSegment`)
follows from PROVE-CPL-MART's `hasTwoSeedMartingaleMeans_of_charFun` once the transported field `h_ψ` satisfies the
coupling clause **and has integrable pairings**. The clause is `isCouplingCharFun_of_isChartTransport`; the pairings
are integrable because at time `0` the clause makes `(h', φ)` conditionally Gaussian with a deterministic mean and
variance (the initial force points are deterministic), hence Gaussian (`integrable_apply_of_isCouplingCharFun`).

## Main results

* time-zero identities: `logDerivFwd_zero`, `couplingMean_zero`, `loewnerGreenEnergy_zero_eq`, `fwdHull_rpath_zero`;
* **`integrable_apply_of_isCouplingCharFun`**: the coupling clause with deterministic initial data and a lifetime
  positive almost surely gives `(h, φ) ~ N(∫ 𝔥₀ φ, E₀(φ))`, in particular integrable pairings;
* **`hasTwoSeedMartingaleMeans_of_isChartTransport`**: Lemma 7.1's martingale clause for the transported field, from
  the chart form of the coupling clause (`IsChartCouplingCharFun`) for the two-seed word.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull fwdMap)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

namespace MartMeans2

open Ito

variable {nL nR : ℕ}

/-! ### Time zero -/

section TimeZero

theorem logDerivFwd_zero (w : ℝ → ℝ) (z : ℂ) : QuantumZipper.logDerivFwd w 0 z = 0 := by
  simp only [QuantumZipper.logDerivFwd, intervalIntegral.integral_same, neg_zero]

/-- At time `0` the coupling mean is the bounded harmonic extension itself (driver started at `0`). -/
theorem couplingMean_zero (κ : ℝ) {w : ℝ → ℝ} (hw0 : w 0 = 0) (u : ℂ → ℝ) {z : ℂ} (hz : z ≠ 0) :
    couplingMean κ w 0 u z = u z := by
  rw [couplingMean, logDerivFwd_zero, QuantumZipper.B5.fwdMap_zero_time w (by rw [hw0]; exact hz), hw0,
    Complex.ofReal_zero, sub_zero, Complex.zero_im, mul_zero, sub_zero]

/-- At time `0` the Loewner Green energy does not depend on the driver (started at `0`). -/
theorem loewnerGreenEnergy_zero_eq {w : ℝ → ℝ} (hw0 : w 0 = 0) (φ : TestOn upperHalfPlaneOpens) :
    loewnerGreenEnergy w 0 φ = loewnerGreenEnergy (fun _ => 0) 0 φ := by
  have hfix : ∀ (v : ℝ → ℝ), v 0 = 0 → ∀ y, φ y ≠ 0 → fwdMap v 0 y = y := fun v hv0 y hy => by
    have hyH : y ∈ H := φ.tsupport_subset (subset_tsupport _ hy)
    have hy0 : y ≠ v 0 := by
      rw [hv0]; intro h; rw [h] at hyH; exact lt_irrefl _ (show (0 : ℂ).im > 0 from hyH)
    rw [QuantumZipper.B5.fwdMap_zero_time v hy0, hv0, Complex.ofReal_zero, sub_zero]
  unfold loewnerGreenEnergy
  congr 1
  funext y
  congr 1
  funext z
  by_cases hy : φ y = 0
  · simp only [hy, zero_mul]
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  rw [hfix w hw0 y hy, hfix w hw0 z hz, hfix (fun _ => 0) rfl y hy, hfix (fun _ => 0) rfl z hz]

/-- The hull at time `0` of a driver continuous before a positive lifetime is empty. -/
theorem fwdHull_rpath_zero {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hζ : 0 < ζ) : fwdHull (rpath w) 0 = ∅ := by
  obtain ⟨t₂, ht₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hζ
  have ht₂' : (0 : ℝ) < t₂ := by exact_mod_cast ht₂
  have hc := continuous_clampDrv (W := rpath w) t₂.coe_nonneg (continuousOn_rpath hw ht₂ζ)
  rw [fwdHull_eq_of_eqOn le_rfl ht₂' fun r hr => (clampDrv_eqOn (W := rpath w) (T := (t₂ : ℝ)) hr).symm]
  exact QuantumZipper.RS.fwdHull_zero_eq_empty hc

end TimeZero

/-! ### Integrable pairings -/

section Integrable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- `E₀(φ) ≥ 0`, the time-zero energy (the variance of `(h⁰, φ)` for a zero-boundary GFF on `ℍ`). -/
theorem loewnerGreenEnergy_zero_nonneg (φ : TestOn upperHalfPlaneOpens) :
    0 ≤ loewnerGreenEnergy (fun _ => 0) 0 φ :=
  loewnerGreenEnergy_nonneg continuous_const rfl le_rfl φ
    (by rw [QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const]; exact disjoint_empty _)

/-- **The law of a pairing of a coupled field.** If `h` satisfies the coupling clause (`IsCouplingCharFun`), the
lifetime is positive almost surely, and almost surely the driver starts at `0`, is continuous before the lifetime and
the force points start at deterministic positions `xL`, `xR`, then `(h, φ) ~ N(∫ 𝔥₀ φ, E₀(φ))`, where `𝔥₀` is the
explicit bounded harmonic extension of the time-zero data (`MartChar.meanExt`) and `E₀` the time-zero energy. -/
theorem map_apply_eq_gaussianReal_of_isCouplingCharFun [IsProbabilityMeasure P] {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
    (h0 : ∀ᵐ ω ∂P, 0 < ζ ω ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧
      (∀ i, VL i 0 ω = xL i) ∧ ∀ i, VR i 0 ω = xR i)
    (φ : TestOn upperHalfPlaneOpens) (hφm : Measurable fun ω => h ω φ) :
    P.map (fun ω => h ω φ) = gaussianReal (∫ z, MartChar.meanExt κ ρL ρR 0 xL xR z * φ z)
      (loewnerGreenEnergy (fun _ => 0) 0 φ).toNNReal := by
  set M₀ : ℝ := ∫ z, MartChar.meanExt κ ρL ρR 0 xL xR z * φ z with hM₀
  set E₀ : ℝ := loewnerGreenEnergy (fun _ => 0) 0 φ with hE₀
  have hE0 : 0 ≤ E₀ := loewnerGreenEnergy_zero_nonneg φ
  have hτ : IsStoppingTime 𝓖 fun _ : Ω => ((0 : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓖 0
  have hτm : hτ.measurableSpace = 𝓖 0 := IsStoppingTime.measurableSpace_const 𝓖 0
  have hlt : ∀ᵐ ω ∂P, ((((0 : ℝ≥0) : WithTop ℝ≥0)) : ℝ≥0∞) < ζ ω := by
    filter_upwards [h0] with ω hω
    exact hω.1
  set u : Ω → ℂ → ℝ := fun ω => MartChar.meanExt κ ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun i => VR i 0 ω)
    with hudef
  have hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω -
          W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω -
          W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω)
        (fun i => VR i ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω - W ((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0) ω))
      (u ω) := fun ω => MartChar.isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _
  have hcond : ∀ θ : ℝ, P[fun ω => Complex.exp (Complex.I * θ * (h ω φ : ℂ)) | 𝓖 0] =ᵐ[P]
      fun _ => Complex.exp (Complex.I * θ * (M₀ : ℂ) - θ ^ 2 * (E₀ : ℂ) / 2) := by
    intro θ
    have hcl := hcf _ hτ hlt u hu (θ • φ)
    rw [hτm] at hcl
    have e1 : (fun ω' => Complex.exp (Complex.I * (h ω' (θ • φ) : ℂ))) =
        fun ω' => Complex.exp (Complex.I * θ * (h ω' φ : ℂ)) := by
      funext ω'
      rw [map_smul, smul_eq_mul]
      push_cast
      ring_nf
    rw [e1] at hcl
    filter_upwards [hcl, h0] with ω hω hgω
    obtain ⟨hζ, hwc, hw0, hvl, hvr⟩ := hgω
    have ht0 : (((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ) = 0 := by
      rw [WithTop.untopD_coe, NNReal.coe_zero]
    have hK : fwdHull (fun s : ℝ => W s.toNNReal ω) (((((0 : ℝ≥0) : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : ℝ) = ∅ := by
      rw [ht0]
      exact fwdHull_rpath_zero (w := fun t => W t ω) hwc hζ
    rw [hω (by rw [hK]; exact disjoint_empty _), ht0]
    have hr0 : (fun s : ℝ => W s.toNNReal ω) 0 = 0 := by
      simp only [Real.toNNReal_zero, hw0]
    have huω : u ω = MartChar.meanExt κ ρL ρR 0 xL xR := by
      rw [hudef]
      dsimp only
      rw [hw0, show (fun i => VL i 0 ω) = xL from funext hvl, show (fun i => VR i 0 ω) = xR from funext hvr]
    have hcoe : (⇑(θ • φ) : ℂ → ℝ) = θ • ⇑φ := by
      funext y
      simp
    have hmean : (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) 0 (u ω) z * (θ • φ) z) = θ * M₀ := by
      rw [hcoe, ← MartMeans.integral_mul_smul (MartChar.meanExt κ ρL ρR 0 xL xR) θ φ]
      congr 1
      funext z
      by_cases hz : (θ • ⇑φ) z = 0
      · simp only [hz, mul_zero]
      · have hzH : z ∈ H := φ.tsupport_subset (subset_tsupport _ fun h0 => hz (by
          simp only [Pi.smul_apply, smul_eq_mul, h0, mul_zero]))
        have hz0 : z ≠ 0 := by
          intro h; rw [h] at hzH; exact lt_irrefl _ (show (0 : ℂ).im > 0 from hzH)
        rw [couplingMean_zero κ hr0 (u ω) hz0, huω]
    have hen : loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) 0 ⇑(θ • φ) = θ ^ 2 * E₀ := by
      rw [hcoe, MartMeans.loewnerGreenEnergy_smul, loewnerGreenEnergy_zero_eq hr0 φ]
    rw [hmean, hen]
    congr 1
    push_cast
    ring
  have hmean : ∀ θ : ℝ, ∫ _ω, Complex.exp (Complex.I * θ * (M₀ : ℂ) - θ ^ 2 * (E₀ : ℂ) / 2) ∂P =
      Complex.exp (Complex.I * θ * (M₀ : ℂ) - θ ^ 2 * (((E₀.toNNReal : ℝ≥0) : ℝ) : ℂ) / 2) := by
    intro θ
    rw [integral_const, probReal_univ, one_smul, Real.coe_toNNReal _ hE0]
  exact map_eq_gaussianReal_of_condExp (𝓖.le 0) hφm (m := fun _ => M₀) (v := fun _ => E₀) hcond hmean

/-- **Integrable pairings of a coupled field** (under the hypotheses of `map_apply_eq_gaussianReal_of_isCouplingCharFun`):
each `(h, φ)` is Gaussian, hence integrable. -/
theorem integrable_apply_of_isCouplingCharFun [IsProbabilityMeasure P] {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h)
    (h0 : ∀ᵐ ω ∂P, 0 < ζ ω ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧
      (∀ i, VL i 0 ω = xL i) ∧ ∀ i, VR i 0 ω = xR i)
    (φ : TestOn upperHalfPlaneOpens) (hφm : Measurable fun ω => h ω φ) :
    Integrable (fun ω => h ω φ) P := by
  have hmap := map_apply_eq_gaussianReal_of_isCouplingCharFun hcf h0 φ hφm
  have hg : Integrable id (P.map fun ω => h ω φ) := by
    rw [hmap]
    exact memLp_one_iff_integrable.1 (by simpa using memLp_id_gaussianReal (μ := _) (v := _) (1 : ℝ≥0))
  exact (integrable_map_measure aestronglyMeasurable_id hφm.aemeasurable).1 hg

end Integrable

/-! ### Lemma 7.1's martingale clause from the chart form -/

section TwoSeed

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {c : Ω → Chart} {a k : ℝ} {h h' : Ω → DistOn upperHalfPlaneOpens}

/-- The left geometric force point of the two-seed word starts at `0`. -/
theorem geomL_twoSeed_zero (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (i : Fin 1)
    (ω : Ω) : MartChar.geomL W LP.twoSeedXL i 0 ω = LP.twoSeedXL i := by
  have hc := Bessel.continuous_realPath (B := fun t ω => -W t ω) (fun ω => (hWc ω).neg) ω
  have h0 : Bessel.realPath (fun t ω => -W t ω) ω 0 = 0 := by
    simp only [Bessel.realPath, Real.toNNReal_zero, hW0, neg_zero]
  have e := MartChar.RealFlow.rightImg_zero hc h0 (x := -LP.twoSeedXL i)
    (by simp only [LP.twoSeedXL, neg_zero, le_refl])
  simp only [MartChar.geomL, NNReal.coe_zero, e, neg_neg]

/-- The right geometric force point of the two-seed word starts at `0`. -/
theorem geomR_twoSeed_zero (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (i : Fin 1)
    (ω : Ω) : MartChar.geomR W LP.twoSeedXR i 0 ω = LP.twoSeedXR i := by
  have hc := Bessel.continuous_realPath (B := W) hWc ω
  have h0 : Bessel.realPath W ω 0 = 0 := by
    simp only [Bessel.realPath, Real.toNNReal_zero, hW0]
  have e := MartChar.RealFlow.rightImg_zero hc h0 (x := LP.twoSeedXR i)
    (by simp only [LP.twoSeedXR, le_refl])
  simp only [MartChar.geomR, NNReal.coe_zero, e]

/-- **Lemma 7.1's martingale clause from the chart form of the coupling clause.** Let `W` be a continuous adapted
driver with `W₀ = 0` in a right-continuous filtration `𝓖`, `c ω` `𝓖₀`-measurable conformal charts with lifts
continuous on their domains, and `h` a measurable random distribution satisfying the coupling clause of the two-seed
word with weights `(rL; rR)` in the original domain of the chart (`IsChartCouplingCharFun`, infinite lifetime). Then
for every chart transport `h'` of `h` (`IsChartTransport (c ω) 1 a k`), the coupling means of `h'` are local
martingales before the swallowing times: `Sec7.Lemma71.HasTwoSeedMartingaleMeans κ rL rR P 𝓖 W`. -/
theorem hasTwoSeedMartingaleMeans_of_isChartTransport [IsProbabilityMeasure P] [𝓖.IsRightContinuous]
    {rL rR : ℝ} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) (hh : Measurable h)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓖 W)
    (hcf : IsChartCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P 𝓖 W
      (MartChar.geomL W LP.twoSeedXL) (MartChar.geomR W LP.twoSeedXR) (fun _ => ⊤) c a k h)
    (ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (h' ω)) :
    Sec7.Lemma71.HasTwoSeedMartingaleMeans κ rL rR P 𝓖 W := by
  have hcf' := isCouplingCharFun_of_isChartTransport hc hdom hfwd hliftm hliftc hh
    (Eventually.of_forall fun ω => ⟨hW0 ω, (hWc ω).continuousOn⟩) hcf ht
  have hm : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hliftc hh 1 a k
  have he : h' = fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) := funext fun ω =>
    IsChartTransport.eq_chartTransport (hc ω)
      (Chart.locallyIntegrableOn_of_continuousOn ((hc ω).continuousOn_lift_inv (hliftc ω))) (ht ω)
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h' ω φ) P := fun φ =>
    integrable_apply_of_isCouplingCharFun (xL := LP.twoSeedXL) (xR := LP.twoSeedXR) hcf'
      (Eventually.of_forall fun ω => ⟨ENNReal.zero_lt_top,
        (hWc ω).continuousOn, hW0 ω, fun i => geomL_twoSeed_zero hW0 hWc i ω,
        fun i => geomR_twoSeed_zero hW0 hWc i ω⟩) φ
      (by rw [he]; exact (LQGMetric.measurable_distOn_apply φ).comp hm)
  exact MartMeans.hasTwoSeedMartingaleMeans_of_charFun hW0 hWc hWa hint hcf'

end TwoSeed

end MartMeans2

end Coupling

end InteractingSLE
