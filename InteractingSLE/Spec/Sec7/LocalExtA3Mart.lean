/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA3Path

/-!
# The local comparison of Aux. lemma 55: the tested mean of the source and its cross bracket are martingales

Packet PROVE-LOCEXT-A3, item 1 (a)–(b). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L163–L182, p. 248):
"`(M_t − m, v) = ∫₀ᵗ a_s dB_s`, `0 ≤ t ≤ S`. The stopped versions of these equations are used for arbitrary `t`. … The
same source approximation proves (HL4) for `v`."

With `𝓔` the usual augmentation of the evolution's filtration and `S = stopTime` the local stop:

* `meanDiag n`, `crossDiag n`: the protected tested mean and cross process of `v_n` at the exit stop of level `R_n`
  (martingales by `Coupling.martingale_meanIntegral` and `martingale_crossIntegral`);
* along the good event they converge (eventually `exitK n = S`; `v_n → v` with `|v_n| ≤ |v|`) to `meanStop … v` and
  `crossStop … v`, with bounds uniform in `n` (the cross process through `|B_{t∧exitK n}|`, whose second moment is at
  most `t + E B₀²`);
* **`martingale_meanStop_vSrc`**: `t ↦ ∫ 𝔥_{t∧S} v` is an `𝓔`-martingale;
* **`martingale_crossStop_vSrc`**: `t ↦ (∫ 𝔥_{t∧S} v) B_{t∧S} − ∫ v (Im f_{t∧S} − Im z)` is an `𝓔`-martingale.
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

/-! ### Convergence of the cross term along a good path -/

section PathLim

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

theorem tendsto_integral_vApprox_mul_im_sub (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) :
    Tendsto (fun n => ∫ z, vApprox κ xL xR ρL ρR r n z * ((fwdMap (Ito.rpath w) t z).im - z.im)) atTop
      (𝓝 (∫ z, vSrc κ xL xR ρL ρR r z * ((fwdMap (Ito.rpath w) t z).im - z.im))) := by
  have hv := integrable_mul_im_sub_of_isGoodPath hp hterm hF hr hseed ht (measurable_vSrc hF hr)
    (fun z => le_rfl) (κ := κ) (ρL := ρL) (ρR := ρR)
  refine tendsto_integral_of_dominated_convergence
    (fun z => |vSrc κ xL xR ρL ρR r z| * |(fwdMap (Ito.rpath w) t z).im - z.im|)
    (fun n => (integrable_mul_im_sub_of_isGoodPath hp hterm hF hr hseed ht (measurable_vApprox hF hr n)
      (abs_vApprox_le n)).aestronglyMeasurable)
    (hv.abs.congr (ae_of_all _ fun z => abs_mul _ _)) (fun n => ae_of_all _ fun z => ?_)
    (ae_of_all _ fun z => (tendsto_vApprox z).mul_const _)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_vApprox_le n z) (abs_nonneg _)

end PathLim

/-! ### The diagonal approximations -/

section Diag

open scoped Classical

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

variable (κ xL xR ρL ρR r W VL VR B ζ G) in
/-- The protected tested mean of `v_n` at the exit stop of level `R_n`. -/
def meanDiag (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ z, meanIntegrand κ ρL ρR W VL VR B (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR n) G t z ω

variable (κ xL xR ρL ρR r W VL VR B ζ G) in
/-- The protected cross process of `v_n` at the exit stop of level `R_n`. -/
def crossDiag (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ z, crossIntegrand κ ρL ρR W VL VR B (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR n) G t z ω

variable (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
  (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
  (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hG : ∀ ω ∈ G, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω)

include hκ hE hF hr hseed hGm hGc hG in
theorem martingale_meanDiag (n : ℕ) :
    Martingale (meanDiag κ xL xR ρL ρR r W VL VR B ζ G n) (usualAugmentation 𝓕 P) P := by
  have hE' := isIntegratedSLEEvolution_usualAugmentation hE
  have hδ : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have := martingale_meanIntegral hE' (isStoppingTime_exitK hE hF hr hseed hGm hGc hG n n)
    (measurableSet_good_zero (𝓕 := 𝓕) hGm hGc) (fun ω hω => isGoodTest_exitK hκ hF hr hseed hG n n hω)
    (tsupport_vApprox_subset_H hF hr n) (continuous_vApprox hF hr n) (hasCompactSupport_vApprox hF hr n) hδ hκ hGc
    (bheProc κ ρL ρR W VL VR) (fun ω s => isBoundedHarmonicExtension_bheProc κ ρL ρR ω s)
  rwa [nullAugmented_usualAugmentation] at this

include hκ hE hF hr hseed hGm hGc hG in
theorem martingale_crossDiag (n : ℕ) :
    Martingale (crossDiag κ xL xR ρL ρR r W VL VR B ζ G n) (usualAugmentation 𝓕 P) P := by
  have hE' := isIntegratedSLEEvolution_usualAugmentation hE
  have hδ : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  have := martingale_crossIntegral hE' (isStoppingTime_exitK hE hF hr hseed hGm hGc hG n n)
    (measurableSet_good_zero (𝓕 := 𝓕) hGm hGc) (fun ω hω => isGoodTest_exitK hκ hF hr hseed hG n n hω)
    (tsupport_vApprox_subset_H hF hr n) (continuous_vApprox hF hr n) (hasCompactSupport_vApprox hF hr n) hδ hκ hGc
    (bheProc κ ρL ρR W VL VR) (fun ω s => isBoundedHarmonicExtension_bheProc κ ρL ρR ω s)
  rwa [nullAugmented_usualAugmentation] at this

theorem meanSrcBound_nonneg (hr : IsSeedRadius xL xR r) : 0 ≤ meanSrcBound κ ρL ρR r := by
  unfold meanSrcBound Coupling.meanHarmonicBound; have := hr.1; positivity

/-- Through an exit stop below the local stop, `t ∧ exitK n ≤ S` along the good event. -/
theorem coe_min_exitK_le {n : ℕ} {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    ((min t (exitK r W VL VR B ζ G xL xR n ω) : ℝ≥0) : WithTop ℝ≥0) ≤
      localStopPath r (ζ ω) fun t => W t ω := by
  rw [← coe_stopTime_of_mem hω]
  exact WithTop.coe_le_coe.2 ((min_le_right _ _).trans (exitStop_le _ _ ω))

include hκ hF hr hseed hG in
/-- The protected tested mean is bounded by `meanSrcBound · ∫ |v|`. -/
theorem abs_meanDiag_le (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |meanDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω| ≤
      meanSrcBound κ ρL ρR r * ∫ z, |vSrc κ xL xR ρL ρR r z| := by
  rw [meanDiag, ← integral_const_mul]
  exact (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    ((integrable_vSrc hF hr).abs.const_mul _) (ae_of_all _ fun z =>
      abs_meanIntegrand_exitK_le hF hr hseed hG n n t z ω fun ω hω => isGoodTest_exitK hκ hF hr hseed hG n n hω))

include hκ hF hr hseed hG in
/-- The cross integrand is bounded by `(M |B_{t∧exitK n}| + 7r) |v|`. -/
theorem abs_crossIntegrand_diag_le (n : ℕ) (t : ℝ≥0) (z : ℂ) (ω : Ω) :
    |crossIntegrand κ ρL ρR W VL VR B (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR n) G t z ω| ≤
      (meanSrcBound κ ρL ρR r * |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| + 7 * r) *
        |vSrc κ xL xR ρL ρR r z| := by
  have hM0 := meanSrcBound_nonneg (κ := κ) (ρL := ρL) (ρR := ρR) hr
  have hr0 := hr.1
  by_cases hω : ω ∈ G
  · by_cases hz : z ∈ tsupport (vApprox κ xL xR ρL ρR r n)
    · have h1 := abs_meanIntegrand_exitK_le hF hr hseed hG n n t z ω
        fun ω hω => isGoodTest_exitK hκ hF hr hseed hG n n hω
      have hfo : fwdOn W (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR n) G t z ω =
          fwdMap (rpath (W · ω)) (min t (exitK r W VL VR B ζ G xL xR n ω) : ℝ≥0) z := by
        simp [fwdOn, hω, hz]
      obtain ⟨hzi, hz6, hz7⟩ := mem_tsupport_vApprox hF hr hz
      have h2 := abs_im_fwdMap_sub_le (hG ω hω).1.1 (hG ω hω).1.2 hF hr hseed
        (coe_min_exitK_le (VL := VL) (VR := VR) (B := B) (xL := xL) (xR := xR) (n := n) hω t) (lt_of_lt_of_le (by positivity) hzi) hz6 hz7
      simp only [crossIntegrand, hω, ↓reduceIte, hfo]
      calc |meanIntegrand κ ρL ρR W VL VR B (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR n) G t z ω *
            B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω - vApprox κ xL xR ρL ρR r n z *
            ((fwdMap (rpath (W · ω)) (min t (exitK r W VL VR B ζ G xL xR n ω) : ℝ≥0) z).im - z.im)|
          ≤ |meanIntegrand κ ρL ρR W VL VR B (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR n) G t z ω|
              * |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| + |vApprox κ xL xR ρL ρR r n z| *
              |(fwdMap (rpath (W · ω)) (min t (exitK r W VL VR B ζ G xL xR n ω) : ℝ≥0) z).im - z.im| := by
            rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
        _ ≤ meanSrcBound κ ρL ρR r * |vSrc κ xL xR ρL ρR r z| *
              |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| + |vSrc κ xL xR ρL ρR r z| * (7 * r) :=
            add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
              (mul_le_mul (abs_vApprox_le n z) h2 (abs_nonneg _) (abs_nonneg _))
        _ = _ := by ring
    · simp [crossIntegrand, meanIntegrand, eq_zero_of_notMem_tsupport' hz]; positivity
  · simp [crossIntegrand, meanIntegrand, hω]; positivity

include hκ hF hr hseed hG in
theorem abs_crossDiag_le (n : ℕ) (t : ℝ≥0) (ω : Ω) :
    |crossDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω| ≤
      (meanSrcBound κ ρL ρR r * ∫ z, |vSrc κ xL xR ρL ρR r z|) *
          |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| + 7 * r * ∫ z, |vSrc κ xL xR ρL ρR r z| := by
  have e : (meanSrcBound κ ρL ρR r * ∫ z, |vSrc κ xL xR ρL ρR r z|) *
        |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| + 7 * r * ∫ z, |vSrc κ xL xR ρL ρR r z| =
      ∫ z, (meanSrcBound κ ρL ρR r * |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| + 7 * r) *
        |vSrc κ xL xR ρL ρR r z| := by
    rw [integral_const_mul]; ring
  rw [e, crossDiag]
  exact (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    ((integrable_vSrc hF hr).abs.const_mul _) (ae_of_all _ fun z =>
      abs_crossIntegrand_diag_le hκ hF hr hseed hG n t z ω))

/-! ### Convergence on the good event -/

include hκ hF hr hseed hG in
theorem tendsto_meanDiag (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => meanDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω) atTop
      (𝓝 (meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω)) := by
  by_cases hω : ω ∈ G
  · have hle : ((min t (stopTime r G ζ W ω) : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
      rw [← coe_stopTime_of_mem hω]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
    have h := tendsto_integral_couplingMean_vApprox_of_isGoodPath (hG ω hω).1.1 (hG ω hω).1.2 hF hr hseed hle
      (isBoundedHarmonicExtension_bheProc (W := W) (VL := VL) (VR := VR) κ ρL ρR ω (min t (stopTime r G ζ W ω))) (tendsto_id (α := ℕ))
    simp only [meanStop, hω, ↓reduceIte]
    refine h.congr' ?_
    filter_upwards [eventually_exitK_eq hF hr hseed hG ω] with n hn
    simp only [meanDiag, id]
    exact integral_congr_ae (ae_of_all _ fun z => (meanIntegrand_eq_of_exitK hκ hF hr hseed hG hω hn t z).symm)
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    simp [meanDiag, meanStop, meanIntegrand, hω]

include hκ hF hr hseed hG in
theorem tendsto_crossDiag (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => crossDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω) atTop
      (𝓝 (crossStop κ ρL ρR r W VL VR B ζ G (vSrc κ xL xR ρL ρR r) t ω)) := by
  by_cases hω : ω ∈ G
  · set S := stopTime r G ζ W ω with hS
    have hle : ((min t S : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
      rw [hS, ← coe_stopTime_of_mem hω]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
    have hp := (hG ω hω).1.1
    have hterm := (hG ω hω).1.2
    have h1 := tendsto_integral_couplingMean_vApprox_of_isGoodPath hp hterm hF hr hseed hle
      (isBoundedHarmonicExtension_bheProc (W := W) (VL := VL) (VR := VR) κ ρL ρR ω (min t (stopTime r G ζ W ω))) (tendsto_id (α := ℕ))
    have h2 := tendsto_integral_vApprox_mul_im_sub hp hterm hF hr hseed hle (κ := κ) (ρL := ρL) (ρR := ρR)
    have h3 := (h1.mul_const (B (min t S) ω)).sub h2
    simp only [crossStop, meanStop, hω, ↓reduceIte]
    refine h3.congr' ?_
    filter_upwards [eventually_exitK_eq hF hr hseed hG ω] with n hn
    simp only [id]
    have hpt : ∀ z, crossIntegrand κ ρL ρR W VL VR B (vApprox κ xL xR ρL ρR r n)
        (exitK r W VL VR B ζ G xL xR n) G t z ω =
        couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t S : ℝ≥0) (bheProc κ ρL ρR W VL VR ω (min t S)) z *
          vApprox κ xL xR ρL ρR r n z * B (min t S) ω -
        vApprox κ xL xR ρL ρR r n z * ((fwdMap (rpath (W · ω)) (min t S : ℝ≥0) z).im - z.im) := fun z => by
      have hm := meanIntegrand_eq_of_exitK hκ hF hr hseed hG hω hn t z (n := n)
      simp only [crossIntegrand, hω, ↓reduceIte, hm, hn]
      by_cases hz : z ∈ tsupport (vApprox κ xL xR ρL ρR r n)
      · have hfo : fwdOn W (vApprox κ xL xR ρL ρR r n) (exitK r W VL VR B ζ G xL xR n) G t z ω =
            fwdMap (rpath (W · ω)) (min t S : ℝ≥0) z := by simp [fwdOn, hω, hz, hn, hS]
        rw [hfo]
      · simp [eq_zero_of_notMem_tsupport' hz]
    have hi1 : Integrable fun z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) (min t S : ℝ≥0)
        (bheProc κ ρL ρR W VL VR ω (min t S)) z * vApprox κ xL xR ρL ρR r n z :=
      integrable_couplingMean_mul_of_isGoodPath hp hterm hF hr hseed hle
        (isBoundedHarmonicExtension_bheProc (W := W) (VL := VL) (VR := VR) κ ρL ρR ω (min t (stopTime r G ζ W ω))) (measurable_vApprox hF hr n) (abs_vApprox_le n)
    have hi2 : Integrable fun z => vApprox κ xL xR ρL ρR r n z *
        ((fwdMap (rpath (W · ω)) (min t S : ℝ≥0) z).im - z.im) :=
      integrable_mul_im_sub_of_isGoodPath hp hterm hF hr hseed hle (measurable_vApprox hF hr n) (abs_vApprox_le n)
    rw [crossDiag, integral_congr_ae (ae_of_all _ hpt), integral_sub (hi1.mul_const _) hi2, integral_mul_const]
    rfl
  · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
    simp [crossDiag, crossStop, crossIntegrand, meanIntegrand, hω]

/-! ### The limits are martingales -/

include hκ hE hF hr hseed hGm hGc hG in
/-- **The stopped tested mean of the source is a martingale** of the usual augmentation. -/
theorem martingale_meanStop_vSrc :
    Martingale (meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r)) (usualAugmentation 𝓕 P) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set K := meanSrcBound κ ρL ρR r * ∫ z, |vSrc κ xL xR ρL ρR r z| with hK
  have hmart := martingale_meanDiag hκ hE hF hr hseed hGm hGc hG
  have hbd := abs_meanDiag_le hκ hF hr hseed hG
  have hconv := tendsto_meanDiag hκ hF hr hseed hG
  have hYm : ∀ n t, Measurable (meanDiag κ xL xR ρL ρR r W VL VR B ζ G n t) := fun n t =>
    (((hmart n).1 t).mono ((usualAugmentation 𝓕 P).le t)).measurable
  have hlimm : ∀ t, Measurable (meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t) := fun t =>
    measurable_of_tendsto_metrizable (fun n => hYm n t) (tendsto_pi_nhds.2 (hconv t))
  refine martingale_of_tendsto_of_null (fun t N hN h0 => measurableSet_usualAugmentation_of_null hN h0 t)
    hmart (fun n t => MemLp.of_bound (hYm n t).aestronglyMeasurable K (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hbd n t ω))
    (fun t => ⟨K ^ 2, fun n => by
      calc ∫ ω, meanDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω ^ 2 ∂P ≤ ∫ _, K ^ 2 ∂P := integral_mono_of_nonneg
            (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _) (ae_of_all _ fun ω => by
              show meanDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω ^ 2 ≤ K ^ 2
              rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd n t ω) 2)
        _ = K ^ 2 := by simp⟩)
    (fun t => ae_of_all _ (hconv t)) hlimm (fun t => Integrable.of_bound (hlimm t).aestronglyMeasurable K
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hconv t ω))
          fun n => hbd n t ω))

include hκ hE hF hr hseed hGm hGc hG in
/-- **The stopped cross process of the source is a martingale** of the usual augmentation. -/
theorem martingale_crossStop_vSrc :
    Martingale (crossStop κ ρL ρR r W VL VR B ζ G (vSrc κ xL xR ρL ρR r)) (usualAugmentation 𝓕 P) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hE' := isIntegratedSLEEvolution_usualAugmentation hE
  have hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[usualAugmentation 𝓕 P t] N :=
    fun t N hN h0 => measurableSet_usualAugmentation_of_null hN h0 t
  set a := meanSrcBound κ ρL ρR r * ∫ z, |vSrc κ xL xR ρL ρR r z| with ha
  set b := 7 * r * ∫ z, |vSrc κ xL xR ρL ρR r z| with hb
  have hmart := martingale_crossDiag hκ hE hF hr hseed hGm hGc hG
  have hbd := abs_crossDiag_le hκ hF hr hseed hG
  have hconv := tendsto_crossDiag hκ hF hr hseed hG
  have hBc : ∀ ω ∈ G, Continuous (B · ω) := fun ω hω => (hG ω hω).2
  have hstopK : ∀ n, IsStoppingTime (usualAugmentation 𝓕 P)
      fun ω => (exitK r W VL VR B ζ G xL xR n ω : WithTop ℝ≥0) := fun n => by
    have := isStoppingTime_exitK hE hF hr hseed hGm hGc hG n n
    rwa [nullAugmented_usualAugmentation] at this
  have hBn := fun n t => integral_sq_stoppedNoise_le hE'.1 hnull hGm hGc hBc (hstopK n) t
  have hYm : ∀ n t, Measurable (crossDiag κ xL xR ρL ρR r W VL VR B ζ G n t) := fun n t =>
    (((hmart n).1 t).mono ((usualAugmentation 𝓕 P).le t)).measurable
  have hlimm : ∀ t, Measurable (crossStop κ ρL ρR r W VL VR B ζ G (vSrc κ xL xR ρL ρR r) t) := fun t =>
    measurable_of_tendsto_metrizable (fun n => hYm n t) (tendsto_pi_nhds.2 (hconv t))
  have ha0 : 0 ≤ a := mul_nonneg (meanSrcBound_nonneg hr) (integral_nonneg fun _ => abs_nonneg _)
  have hb0 : 0 ≤ b := mul_nonneg (by have := hr.1; positivity) (integral_nonneg fun _ => abs_nonneg _)
  -- `L²` membership and the uniform bound
  have hL2 : ∀ n t, MemLp (crossDiag κ xL xR ρL ρR r W VL VR B ζ G n t) 2 P := fun n t => by
    have hg : MemLp (fun ω => a * ‖B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω‖ + b) 2 P :=
      ((hBn n t).1.norm.const_mul a).add (memLp_const b)
    refine hg.of_le (hYm n t).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (mul_nonneg ha0 (abs_nonneg _)) hb0)]
    exact hbd n t ω
  have hsq : ∀ n t ω, crossDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω ^ 2 ≤
      2 * a ^ 2 * B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω ^ 2 + 2 * b ^ 2 := fun n t ω => by
    have h1 := hbd n t ω
    have h2 : crossDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω ^ 2 ≤
        (a * |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| + b) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have h3 : (a * |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| + b) ^ 2 ≤
        2 * a ^ 2 * B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω ^ 2 + 2 * b ^ 2 := by
      have := sq_nonneg (a * |B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω| - b)
      nlinarith [sq_abs (B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω)]
    exact h2.trans h3
  have hbound : ∀ t, ∃ M, ∀ n, ∫ ω, crossDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω ^ 2 ∂P ≤ M := fun t =>
    ⟨2 * a ^ 2 * (t + ∫ ω, WholeField.noiseOn B G 0 ω ^ 2 ∂P) + 2 * b ^ 2, fun n => by
      have hBi : Integrable (fun ω => B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω ^ 2) P :=
        (hBn n t).1.integrable_sq
      calc ∫ ω, crossDiag κ xL xR ρL ρR r W VL VR B ζ G n t ω ^ 2 ∂P
          ≤ ∫ ω, (2 * a ^ 2 * B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω ^ 2 + 2 * b ^ 2) ∂P :=
            integral_mono (hL2 n t).integrable_sq ((hBi.const_mul _).add (integrable_const _)) (hsq n t)
        _ = 2 * a ^ 2 * ∫ ω, B (min t (exitK r W VL VR B ζ G xL xR n ω)) ω ^ 2 ∂P + 2 * b ^ 2 := by
            rw [integral_add (hBi.const_mul _) (integrable_const _), integral_const_mul]; simp
        _ ≤ _ := by
            gcongr
            exact (hBn n t).2⟩
  -- the limit is integrable
  have hS : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (stopTime r G ζ W ω : WithTop ℝ≥0) :=
    isStoppingTime_stopTime hE hGm hGc fun ω hω => (hG ω hω).1
  have hBS := integral_sq_stoppedNoise_le hE'.1 hnull hGm hGc hBc hS
  have hlimi : ∀ t, Integrable (crossStop κ ρL ρR r W VL VR B ζ G (vSrc κ xL xR ρL ρR r) t) P := fun t => by
    have hg : Integrable (fun ω => a * ‖B (min t (stopTime r G ζ W ω)) ω‖ + b) P :=
      (((hBS t).1.integrable one_le_two).norm.const_mul a).add (integrable_const b)
    refine hg.mono' (hlimm t).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine le_of_tendsto ((continuous_abs.tendsto _).comp (hconv t ω)) ?_
    by_cases hω : ω ∈ G
    · filter_upwards [eventually_exitK_eq hF hr hseed hG ω] with n hn
      have := hbd n t ω
      rw [hn] at this
      exact this
    · refine Eventually.of_forall fun n => ?_
      simp only [Function.comp_apply, crossDiag, crossIntegrand, meanIntegrand, hω, ↓reduceIte, zero_mul,
        sub_zero, integral_zero, abs_zero]
      positivity
  exact martingale_of_tendsto_of_null hnull hmart hL2 hbound (fun t => ae_of_all _ (hconv t)) hlimm hlimi

end Diag

end LocalExt

end InteractingSLE
