/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Mart

/-!
# The local comparison of Aux. lemma 55: the brackets of the tested mean through the local stop

Packet PROVE-LOCEXT-A2, step 4 (path side of (HL4)). With `S` the local stop (`stopTime`) and `𝓔` the usual augmentation
of the evolution's filtration:

* `meanStop … φ t = ∫ 𝔥_{t∧S}(z) φ(z) dz` and `crossStop … φ t = meanStop … φ t · B_{t∧S} − ∫ φ(z)(Im f_{t∧S}(z) − Im z) dz`
  (on the good event, `0` off it);
* `martingale_meanStop_vApprox`, `martingale_crossStop_vApprox`: both are `𝓔`-martingales for every approximation `v_n`
  (the protected martingales of `Coupling.TestMean` and `martingale_crossIntegral` at the exit stops of the coordinate
  size from `[0, R)`, `R → ∞`, `martingale_of_tendsto_of_null`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open LQGMetric (TestOn DistOn)
open Coupling Ito

section Stopped

open scoped Classical

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The explicit harmonic extension along the path of `ω` at time `s`. -/
def bheProc (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ≥0) : ℂ → ℝ :=
  bheAt κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)

theorem isBoundedHarmonicExtension_bheProc (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (ω : Ω) (s : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (bheProc κ ρL ρR W VL VR ω s) :=
  isBoundedHarmonicExtension_bheAt κ ρL ρR _ _

/-- **The tested mean stopped at the local stop**, `∫ 𝔥_{t∧S}(z) φ(z) dz` on `G`. -/
def meanStop (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (φ : ℂ → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (stopTime r G ζ W ω) : ℝ≥0)
    (bheProc κ ρL ρR W VL VR ω (min t (stopTime r G ζ W ω))) z * φ z else 0

/-- **The cross process stopped at the local stop**: `meanStop · B_{t∧S} − ∫ φ (Im f_{t∧S} − Im z)` on `G`. -/
def crossStop (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω)
    (φ : ℂ → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ G then meanStop κ ρL ρR r W VL VR ζ G φ t ω * B (min t (stopTime r G ζ W ω)) ω -
    ∫ z, φ z * ((fwdMap (rpath (W · ω)) (min t (stopTime r G ζ W ω) : ℝ≥0) z).im - z.im) else 0

/-- The exit levels `R_k = k + ⌈Σ|x|⌉ + 1`. -/
def exitLevel (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (k : ℕ) : ℕ :=
  k + (⌈∑ i, |xL i| + ∑ i, |xR i|⌉₊ + 1)

theorem lt_exitLevel (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (k : ℕ) :
    ∑ i, |xL i| + ∑ i, |xR i| < (exitLevel xL xR k : ℝ) := by
  unfold exitLevel
  push_cast
  linarith [Nat.le_ceil (∑ i, |xL i| + ∑ i, |xR i|), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The exit stops at level `R_k` before the local stop. -/
def exitK (r : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (G : Set Ω) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (k : ℕ) : Ω → ℝ≥0 :=
  exitStop W VL VR B (stopTime r G ζ W) G (exitLevel xL xR k : ℝ) (stopHorizon r)

variable (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
  (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
  (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hG : ∀ ω ∈ G, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω)

omit hG in
include hGm hGc in
theorem measurableSet_good_zero : MeasurableSet[nullAugmented (usualAugmentation 𝓕 P) P 0] G := by
  rw [nullAugmented_usualAugmentation]
  have h := measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hGc 0
  simpa using h.compl

include hE hGm hGc hG in
theorem isStoppingTime_stopTime_null :
    IsStoppingTime (nullAugmented (usualAugmentation 𝓕 P) P) fun ω => (stopTime r G ζ W ω : WithTop ℝ≥0) := by
  rw [nullAugmented_usualAugmentation]
  exact isStoppingTime_stopTime hE hGm hGc fun ω hω => (hG ω hω).1

include hE hF hr hseed hGm hGc hG in
theorem isStoppingTime_exitK (n : ℕ) (k : ℕ) :
    IsStoppingTime (nullAugmented (usualAugmentation 𝓕 P) P)
      fun ω => (exitK r W VL VR B ζ G xL xR k ω : WithTop ℝ≥0) :=
  isStoppingTime_exitStop (isIntegratedSLEEvolution_usualAugmentation hE)
    (isStoppingTime_stopTime_null hE hGm hGc hG) (measurableSet_good_zero (𝓕 := 𝓕) hGm hGc)
    (fun _ hω => isGoodSafe_vApprox hF hr hseed hG n hω) _ _

include hκ hF hr hseed hG in
theorem isGoodTest_exitK (n k : ℕ) {ω : Ω} (hω : ω ∈ G) :
    IsGoodTest κ xL xR ρL ρR W VL VR B ζ (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR k)
      (1 / (2 * ((n : ℝ) + 1))) (exitLevel xL xR k : ℝ) (r ^ 2 / 64) ω := by
  have hGs := fun (ω' : Ω) (h' : ω' ∈ G) => isGoodSafe_vApprox (κ := κ) hF hr hseed hG n h'
  have hs := hGs ω hω
  have hR0 : coordSize W VL VR B 0 ω < (exitLevel xL xR k : ℝ) := by
    rw [hs.coordSize_zero hκ]; exact lt_exitLevel xL xR k
  refine isGoodTest_of_le hs.1 hs.2.1 hs.2.2 ?_ (exitStop_le _ _ ω) fun s hs' =>
    coordSize_le_of_le_exitStop hGs hω hR0 hs'
  intro z hz
  have := mem_tsupport_vApprox hF hr hz
  exact lt_of_lt_of_le (by positivity) this.1

include hF hr hseed hG in
theorem eventually_exitK_eq (ω : Ω) :
    ∀ᶠ k in atTop, exitK r W VL VR B ζ G xL xR k ω = stopTime r G ζ W ω := by
  have hGs := fun (ω' : Ω) (h' : ω' ∈ G) => isGoodSafe_vApprox (κ := κ) hF hr hseed hG 0 h'
  have h : ∀ᶠ n : ℕ in atTop, exitStop W VL VR B (stopTime r G ζ W) G (n : ℝ) (stopHorizon r) ω =
      stopTime r G ζ W ω :=
    eventually_exitStop_eq hGs (stopTime_le_horizon (r := r) (G := G) (ζ := ζ) (W := W) ω)
  have hle : ∀ k, k ≤ exitLevel xL xR k := fun k => by unfold exitLevel; exact Nat.le_add_right _ _
  have ht : Tendsto (exitLevel xL xR) atTop atTop := tendsto_atTop_mono hle tendsto_id
  filter_upwards [ht.eventually h] with k hk
  exact hk

theorem continuous_vApprox (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) :
    Continuous (vApprox κ xL xR ρL ρR r n) :=
  (contDiff_cutIm n (k := 0)).continuous.mul (contDiff_vDens hF hr).continuous

theorem tsupport_vApprox_subset_H (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) :
    tsupport (vApprox κ xL xR ρL ρR r n) ⊆ H :=
  (vApproxTest (κ := κ) (ρL := ρL) (ρR := ρR) hF hr n).tsupport_subset

theorem hasCompactSupport_vApprox (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (n : ℕ) :
    HasCompactSupport (vApprox κ xL xR ρL ρR r n) :=
  (vApproxTest (κ := κ) (ρL := ρL) (ρR := ρR) hF hr n).hasCompactSupport

include hκ hF hr hseed hG in
/-- On `G` at an exit stop equal to the local stop, the protected integrand is the tested mean. -/
theorem meanIntegrand_eq_of_exitK {n k : ℕ} {ω : Ω} (hω : ω ∈ G)
    (hk : exitK r W VL VR B ζ G xL xR k ω = stopTime r G ζ W ω) (t : ℝ≥0) (z : ℂ) :
    meanIntegrand κ ρL ρR W VL VR B (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR k) G t z ω =
      couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t (stopTime r G ζ W ω) : ℝ≥0)
        (bheProc κ ρL ρR W VL VR ω (min t (stopTime r G ζ W ω))) z * vApprox κ xL xR ρL ρR r n z := by
  by_cases hz : z ∈ tsupport (vApprox κ xL xR ρL ρR r n)
  · simp only [meanIntegrand, hω, ↓reduceIte]
    rw [← (isGoodTest_exitK hκ hF hr hseed hG n k hω).couplingMean_eq_meanVal
      (tsupport_vApprox_subset_H hF hr n) hz (min_le_right _ _) (isBoundedHarmonicExtension_bheProc κ ρL ρR ω _),
      hk]
  · simp [meanIntegrand, hω, eq_zero_of_notMem_tsupport' hz]

include hF hr hseed hG in
/-- The protected integrand is bounded by `meanSrcBound · |v|`. -/
theorem abs_meanIntegrand_exitK_le (n k : ℕ) (t : ℝ≥0) (z : ℂ) (ω : Ω)
    (hgt : ∀ ω ∈ G, IsGoodTest κ xL xR ρL ρR W VL VR B ζ (vApprox κ xL xR ρL ρR r n)
      (exitK r W VL VR B ζ G xL xR k) (1 / (2 * ((n : ℝ) + 1))) (exitLevel xL xR k : ℝ) (r ^ 2 / 64) ω) :
    |meanIntegrand κ ρL ρR W VL VR B (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR k) G t z ω| ≤
      meanSrcBound κ ρL ρR r * |vSrc κ xL xR ρL ρR r z| := by
  have hM0 : 0 ≤ meanSrcBound κ ρL ρR r := by
    unfold meanSrcBound Coupling.meanHarmonicBound; have := hr.1; positivity
  by_cases hω : ω ∈ G
  · by_cases hz : z ∈ tsupport (vApprox κ xL xR ρL ρR r n)
    · obtain ⟨hzi, hz6, -⟩ := mem_tsupport_vApprox hF hr hz
      have hzpos : 0 < z.im := lt_of_lt_of_le (by positivity) hzi
      simp only [meanIntegrand, hω, ↓reduceIte]
      rw [← (hgt ω hω).couplingMean_eq_meanVal (tsupport_vApprox_subset_H hF hr n) hz (min_le_right _ _)
        (isBoundedHarmonicExtension_bheProc κ ρL ρR ω _), abs_mul]
      have hle : ((min t (exitK r W VL VR B ζ G xL xR k ω) : ℝ≥0) : WithTop ℝ≥0) ≤
          localStopPath r (ζ ω) fun t => W t ω := by
        rw [← coe_stopTime_of_mem hω]
        exact WithTop.coe_le_coe.2 ((min_le_right _ _).trans (exitStop_le _ _ ω))
      exact mul_le_mul (abs_couplingMean_bheAt_le (hG ω hω).1.1 (hG ω hω).1.2 hF hr hseed hle hzpos hz6)
        (abs_vApprox_le _ z) (abs_nonneg _) hM0
    · simp [meanIntegrand, eq_zero_of_notMem_tsupport' hz]; positivity
  · simp [meanIntegrand, hω]; positivity

include hκ hE hF hr hseed hGm hGc hG in
/-- **The stopped tested mean of `v_n` is a martingale** of the usual augmentation (integrated (3.15), through the
local stop). -/
theorem martingale_meanStop_vApprox (n : ℕ) :
    Martingale (meanStop κ ρL ρR r W VL VR ζ G (vApprox κ xL xR ρL ρR r n)) (usualAugmentation 𝓕 P) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hE' := isIntegratedSLEEvolution_usualAugmentation hE
  have hδ : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  set φ := vApprox κ xL xR ρL ρR r n with hφ
  set Yk : ℕ → ℝ≥0 → Ω → ℝ := fun k t ω =>
    ∫ z, meanIntegrand κ ρL ρR W VL VR B φ (exitK r W VL VR B ζ G xL xR k) G t z ω with hYk
  have hgt := fun k => fun ω (hω : ω ∈ G) => isGoodTest_exitK hκ hF hr hseed hG n k hω
  have hmart : ∀ k, Martingale (Yk k) (usualAugmentation 𝓕 P) P := fun k => by
    have := martingale_meanIntegral hE' (isStoppingTime_exitK hE hF hr hseed hGm hGc hG n k)
      (measurableSet_good_zero (𝓕 := 𝓕) hGm hGc) (hgt k) (tsupport_vApprox_subset_H hF hr n)
      (continuous_vApprox hF hr n) (hasCompactSupport_vApprox hF hr n) hδ hκ hGc
      (bheProc κ ρL ρR W VL VR) (fun ω s => isBoundedHarmonicExtension_bheProc κ ρL ρR ω s)
    rwa [nullAugmented_usualAugmentation] at this
  set K := meanSrcBound κ ρL ρR r * ∫ z, |vSrc κ xL xR ρL ρR r z| with hK
  have hbd : ∀ k t ω, |Yk k t ω| ≤ K := fun k t ω => by
    rw [hYk, hK, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
      ((integrable_vSrc hF hr).abs.const_mul _) (ae_of_all _ fun z =>
        abs_meanIntegrand_exitK_le hF hr hseed hG n k t z ω (hgt k)))
  have hconv : ∀ t ω, Tendsto (fun k => Yk k t ω) atTop
      (𝓝 (meanStop κ ρL ρR r W VL VR ζ G φ t ω)) := fun t ω => by
    by_cases hω : ω ∈ G
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_exitK_eq hF hr hseed hG ω] with k hk
      simp only [hYk, meanStop, hω, ↓reduceIte]
      exact integral_congr_ae (ae_of_all _ fun z =>
        (meanIntegrand_eq_of_exitK hκ hF hr hseed hG hω hk t z).symm)
    · refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
      simp [hYk, meanStop, meanIntegrand, hω]
  have hYm : ∀ k t, Measurable (Yk k t) := fun k t =>
    (((hmart k).1 t).mono ((usualAugmentation 𝓕 P).le t)).measurable
  have hlimm : ∀ t, Measurable (meanStop κ ρL ρR r W VL VR ζ G φ t) := fun t =>
    measurable_of_tendsto_metrizable (fun k => hYm k t) (tendsto_pi_nhds.2 (hconv t))
  refine martingale_of_tendsto_of_null (fun t N hN h0 => measurableSet_usualAugmentation_of_null hN h0 t)
    hmart (fun k t => MemLp.of_bound (hYm k t).aestronglyMeasurable K (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hbd k t ω))
    (fun t => ⟨K ^ 2, fun k => by
      calc ∫ ω, Yk k t ω ^ 2 ∂P ≤ ∫ _, K ^ 2 ∂P := integral_mono_of_nonneg
            (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _) (ae_of_all _ fun ω => by
              show Yk k t ω ^ 2 ≤ K ^ 2
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd k t ω) 2)
        _ = K ^ 2 := by simp⟩)
    (fun t => ae_of_all _ (hconv t)) hlimm (fun t => Integrable.of_bound (hlimm t).aestronglyMeasurable K
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hconv t ω))
          fun k => hbd k t ω))

end Stopped

end LocalExt

end InteractingSLE
