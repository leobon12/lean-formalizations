/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenFinalPass
import InteractingSLE.WangWu.ImgChartConstAsm

/-!
# Bounds and protected right limits of the generalized image kernels

PROVE-CROSSCOND-GEN. The chart arguments from the theta chain use continuity of
the force coordinates, including at their allowed collisions. The existing generic
chart continuity theorem therefore applies directly to contact words.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H)
open LQGMetric (TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open Sec7.Lemma71D

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} {κ a k : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0} {c : Ω → Chart}

/-- A Gaussian image kernel has norm at most one, through admissible force
collisions, whenever its lifetime has not ended. -/
theorem norm_imageChar_le_one (hK : IsContactWord W VL VR T)
    {ω : Ω} (hc : (c ω).IsConformal) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < (T ω : ℝ≥0∞)) (φ : TestOn upperHalfPlaneOpens) :
    ‖imageChar κ ρL ρR W VL VR c a k t φ ω‖ ≤ 1 := by
  have hv := WangWu.chartVar_nonneg hc (hK.contW ω) φ ht
  rw [imageChar, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_sub]
  linarith

/-- The protected chart kernels converge along every decreasing capacity sequence
strictly above the current capacity. No strict force separation is needed. -/
theorem tendsto_imageChar_of_isChartAvoid (hK : IsContactWord W VL VR T)
    {ω : Ω} (hc : (c ω).IsConformal) (hlift : ContinuousOn (c ω).2.2 (c ω).dom)
    {r : ℝ≥0} {φ : TestOn upperHalfPlaneOpens}
    (hav : IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ r)
    {u : ℕ → ℝ≥0} (hu : Antitone u) (hru : ∀ n, r < u n) (hlim : Tendsto u atTop (𝓝 r)) :
    (∀ᶠ n in atTop, IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ (u n)) ∧
      Tendsto (fun n => imageChar κ ρL ρR W VL VR c a k (u n) φ ω) atTop
        (𝓝 (imageChar κ ρL ρR W VL VR c a k r φ ω)) := by
  obtain ⟨hev, hmean, hvar⟩ := tendsto_chart_of_isChartAvoid
    (κ := κ) (ρL := ρL) (ρR := ρR) (a := a) (k := k)
    (w := fun t => W t ω) (vL := fun i t => VL i t ω) (vR := fun j t => VR j t ω)
    (ζ := (T ω : ℝ≥0∞)) (c := c ω) (t := r) (φ := φ)
    hc hlift (hK.contW ω) (fun i => (hK.pathL ω i).1) (fun j => (hK.pathR ω j).1) hav hu hru hlim
  refine ⟨hev, ?_⟩
  unfold imageChar
  refine (Complex.continuous_exp.tendsto _).comp ?_
  exact (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp hmean)).sub
    ((Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul hvar))

/-- The explicit Gaussian candidate is measurable on a raw avoidance event as soon
as its mean, variance and that event are. -/
theorem measurable_indicator_imageChar {m : MeasurableSpace Ω} {r : ℝ≥0}
    {φ : TestOn upperHalfPlaneOpens} {E : Set Ω} (hE : MeasurableSet[m] E)
    (hM : Measurable[m] (E.indicator fun ω => chartMean κ ρL ρR (W · ω)
      (fun i t => VL i t ω) (fun j t => VR j t ω) (c ω) a k φ r))
    (hV : Measurable[m] (E.indicator fun ω => chartVar (W · ω) (c ω) φ r)) :
    Measurable[m] (E.indicator (imageChar κ ρL ρR W VL VR c a k r φ)) := by
  have he : E.indicator (imageChar κ ρL ρR W VL VR c a k r φ) =
      E.indicator (fun ω => Complex.exp
        (Complex.I * ((E.indicator (fun ω => chartMean κ ρL ρR (W · ω)
          (fun i t => VL i t ω) (fun j t => VR j t ω) (c ω) a k φ r)) ω : ℂ) -
          (((1 / 2 : ℝ) * (E.indicator (fun ω => chartVar (W · ω) (c ω) φ r)) ω : ℝ) : ℂ))) := by
    apply indicator_congr
    intro ω hω
    simp only [imageChar, indicator_of_mem hω]
  rw [he]
  exact Measurable.indicator (Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp hM).const_mul _ |>.sub
      (Complex.measurable_ofReal.comp (hV.const_mul _)))) hE

end InteractingSLE.Sec5.CrossCond.Gen
