/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Brackets

/-!
# The local comparison of Aux. lemma 55: the drift of the cross bracket (deterministic part)

Packet PROVE-LOCEXT-A3, item 1 (c). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L163–L182, p. 248):
"`(M_t − m, v) = ∫₀ᵗ a_s dB_s`, `a_s = ∫ k_s(z) v(z) d²z`".

In the local regime (and through the stop along a good path):

* `integral_vSrc_mul_im_sub_eq`: `∫ v(z) (Im f_s(z) − Im z) dz = ∫₀ˢ A(u) du` with `A = srcDrift` (the integrated cross
  bracket `d⟨(𝔥, v), B⟩ = A dt`; Fubini with `∫₀ˢ Im(2/f_u(z)) du = Im f_s(z) − Im z`);
* `integrable_mul_im_sub`, `integrable_couplingMean_mul_src`: the two pieces of the cross process are integrable for
  `|φ| ≤ |v|`, with the bounds `7r |v|` and `M |v|`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull chiC)

section Det

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {W : ℝ → ℝ} {T : ℝ}

/-- `|Im f_s(z) − Im z| ≤ 7r` on the source in the local regime. -/
theorem abs_im_fwdMap_sub_src_le (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {s : ℝ} (hs : s ∈ Icc 0 T) {z : ℂ} (hz : vSrc κ xL xR ρL ρR r z ≠ 0) :
    |(fwdMap W s z).im - z.im| ≤ 7 * r := by
  obtain ⟨hzS, -, hz7⟩ := mem_srcSet_of_vSrc_ne_zero hF hr hz
  have halive := h.mem_of_lt_norm hzS.1 hzS.2
  have h1 := im_fwdMap_le_im h halive hs
  have h2 := (Ito.im_fwdMap_pos h.cont h.T_nonneg halive hs).le
  rw [abs_of_nonpos (by linarith)]
  linarith [Complex.im_le_norm z]

/-- `φ (Im f_s − Im z)` is integrable for `|φ| ≤ |v|`, with the bound `7r |v|`. -/
theorem integrable_mul_im_sub (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {s : ℝ} (hs : s ∈ Icc 0 T) {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ z, |φ z| ≤ |vSrc κ xL xR ρL ρR r z|) :
    Integrable fun z => φ z * ((fwdMap W s z).im - z.im) := by
  classical
  have hc : ContinuousOn (fwdMap W s) (srcSet r) := continuousOn_fwdMap_srcSet h hs
  have hm : Measurable ((srcSet r).piecewise (fun z => (fwdMap W s z).im - z.im) fun _ => 0) :=
    ((Complex.continuous_im.comp_continuousOn hc).sub Complex.continuous_im.continuousOn).measurable_piecewise
      continuousOn_const (isOpen_srcSet r).measurableSet
  have e : (fun z => φ z * ((fwdMap W s z).im - z.im)) =
      φ * ((srcSet r).piecewise (fun z => (fwdMap W s z).im - z.im) fun _ => 0) := funext fun z => by
    by_cases hz : φ z = 0
    · simp [hz]
    · simp only [Pi.mul_apply, Set.piecewise_eq_of_mem _ _ _ (srcSet_of_abs_le hF hr hφ hz).1]
  refine Integrable.mono' ((integrable_vSrc (κ := κ) (ρL := ρL) (ρR := ρR) hF hr).abs.const_mul (7 * r))
    (by rw [e]; exact (hφm.mul hm).aestronglyMeasurable) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : φ z = 0
  · rw [hz, abs_zero, zero_mul]; have := hr.1; positivity
  · have hv : vSrc κ xL xR ρL ρR r z ≠ 0 := fun h0 => hz (abs_nonpos_iff.1 (by simpa [h0] using hφ z))
    calc |φ z| * |(fwdMap W s z).im - z.im| ≤ |vSrc κ xL xR ρL ρR r z| * (7 * r) :=
          mul_le_mul (hφ z) (abs_im_fwdMap_sub_src_le h hF hr hs hv) (abs_nonneg _) (abs_nonneg _)
      _ = 7 * r * |vSrc κ xL xR ρL ρR r z| := by ring

/-- `𝔥_s φ` is integrable for `|φ| ≤ |v|`. -/
theorem integrable_couplingMean_mul_src (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {u : ℂ → ℝ} (hu : ContinuousOn u H) {C : ℝ} (hC : ∀ w ∈ H, |u w| ≤ C)
    {s : ℝ} (hs : s ∈ Icc 0 T) {φ : ℂ → ℝ} (hφm : Measurable φ) (hφ : ∀ z, |φ z| ≤ |vSrc κ xL xR ρL ρR r z|) :
    Integrable fun z => couplingMean κ W s u z * φ z := by
  set M := C + |chiC κ| * (32 / (121 * r ^ 2) * T) with hM
  refine Integrable.mono' ((integrable_vSrc (κ := κ) (ρL := ρL) (ρR := ρR) hF hr).abs.const_mul M)
    (measurable_couplingMean_mul h hu hs hφm fun z hz => (srcSet_of_abs_le hF hr hφ hz).1).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hz : φ z = 0
  · rw [hz, abs_zero, mul_zero]
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC Complex.I (by simp [QuantumZipper.H]))
    have hT0 := h.T_nonneg
    have hr0 := h.r_pos
    positivity
  · obtain ⟨hzS, hz6⟩ := srcSet_of_abs_le hF hr hφ hz
    have hb := abs_couplingMean_src_le (κ := κ) h hC hzS.1 hz6 hs
    calc |couplingMean κ W s u z| * |φ z| ≤ M * |vSrc κ xL xR ρL ρR r z| :=
          mul_le_mul hb (hφ z) (abs_nonneg _) ((abs_nonneg _).trans hb)
      _ = _ := rfl

/-- **The integrated cross bracket of the source** (local regime):
`∫ v(z) (Im f_s(z) − Im z) dz = ∫₀ˢ A(u) du`, `A = srcDrift`. -/
theorem integral_vSrc_mul_im_sub_eq (h : IsLocalRegime W r T) (hF : IsOrderedForceWord xL xR)
    (hr : IsSeedRadius xL xR r) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ∫ z, vSrc κ xL xR ρL ρR r z * ((fwdMap W s z).im - z.im) =
      ∫ u in (0 : ℝ)..s, srcDrift κ xL xR ρL ρR r W u := by
  classical
  have hs0 := hs.1
  have hr0 : 0 < r := hr.1
  obtain ⟨Cv, hCv0, hCv⟩ := exists_abs_vSrc_le (κ := κ) (ρL := ρL) (ρR := ρR) hF hr
  set v := vSrc κ xL xR ρL ρR r with hv
  set F : ℝ → ℂ → ℝ := fun u y => srcKer r W (clampS s u) y * v y with hF_def
  have hcl : ∀ u, clampS s u ∈ Icc 0 T := fun u =>
    ⟨(clampS_mem hs0 u).1, (clampS_mem hs0 u).2.trans hs.2⟩
  have hFm : Measurable fun p : ℝ × ℂ => F p.1 p.2 := by
    refine Coupling.measurable_uncurry_of_continuousOn isClosed_univ (0 : ℝ) (fun y => ?_) (fun u _ => ?_)
      (fun u hu => absurd (mem_univ u) hu)
    · refine Continuous.continuousOn ?_
      by_cases hy : y ∈ srcSet r
      · have hys : y ∈ H \ fwdHull W s := srcSet_subset h hs hy
        have hc := (Ito.continuousOn_fwdMap_time' h.cont hs0 hys).comp_continuous (continuous_clampS s)
          (clampS_mem hs0)
        have hk : Continuous fun u => srcKer r W (clampS s u) y := by
          simp only [srcKer, Set.piecewise_eq_of_mem _ _ _ hy]
          exact Complex.continuous_im.comp (continuous_const.div hc fun u =>
            Ito.fwdMap_ne_zero h.cont hs0 hys (clampS_mem hs0 u))
        exact hk.mul continuous_const
      · simp only [hF_def, srcKer, Set.piecewise_eq_of_notMem _ _ _ hy, zero_mul]
        exact continuous_const
    · exact (measurable_srcKer h (hcl u)).mul (measurable_vSrc hF hr)
  set K := 8 / (11 * r) * Cv with hK
  have hFb : ∀ u y, |F u y| ≤ K * (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) y := by
    intro u y
    have hK0 : 0 ≤ K := by rw [hK]; positivity
    by_cases hy : v y = 0
    · simp only [hF_def, hy, mul_zero, abs_zero]
      exact mul_nonneg hK0 (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · obtain ⟨hyS, -, hy7⟩ := mem_srcSet_of_vSrc_ne_zero hF hr hy
      rw [Set.indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; exact hy7), mul_one]
      simp only [hF_def, srcKer, Set.piecewise_eq_of_mem _ _ _ hyS, abs_mul]
      have h2 := abs_im_two_div_src_le h hF hr (hcl u) hy
      have h3 := hCv y
      calc |(2 / fwdMap W (clampS s u) y).im| * |v y| ≤ 8 / (11 * r) * Cv := by gcongr
        _ = K := by rw [hK]
  have hint : Integrable (Function.uncurry F) ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℂ => (fun _ : ℝ => (1 : ℝ)) p.1 *
        (fun y => K * (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) y) p.2)
        ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
      have hball : Integrable fun y : ℂ => (closedBall (0 : ℂ) (7 * r)).indicator (fun _ => (1 : ℝ)) y :=
        (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
      have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) s)) := by
        rw [uIoc_of_le hs0]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      exact Integrable.mul_prod (L := ℝ) (integrable_const _) (hball.const_mul K)
    refine hg.mono' hFm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, one_mul, Real.norm_eq_abs]
    exact hFb p.1 p.2
  have hswap := intervalIntegral_integral_swap hint
  have hleft : ∫ u in (0 : ℝ)..s, ∫ y, F u y = ∫ u in (0 : ℝ)..s, srcDrift κ xL xR ρL ρR r W u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs0] at hu
    simp only [hF_def, clampS_of_mem hu]
    rw [srcDrift]
    exact integral_congr_ae (ae_of_all _ fun y => srcKer_mul_vSrc hF hr W u y)
  have hright : ∀ y, ∫ u in (0 : ℝ)..s, F u y = v y * ((fwdMap W s y).im - y.im) := by
    intro y
    by_cases hy : v y = 0
    · simp [hF_def, hy]
    · have hyS := (mem_srcSet_of_vSrc_ne_zero hF hr hy).1
      have halive := h.mem_of_lt_norm hyS.1 hyS.2
      rw [← integral_im_two_div_fwdMap h.cont h.T_nonneg halive hs, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hs0] at hu
      simp only [hF_def, clampS_of_mem hu, srcKer, Set.piecewise_eq_of_mem _ _ _ hyS]
      ring
  rw [← hleft, hswap]
  exact integral_congr_ae (ae_of_all _ fun y => (hright y).symm)

end Det

/-! ### Along a good path, through the stop -/

section Path

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- **The integrated cross bracket along a good path** at every `t ≤ S`. -/
theorem integral_vSrc_mul_im_sub_eq_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) :
    ∫ z, vSrc κ xL xR ρL ρR r z * ((fwdMap (Ito.rpath w) t z).im - z.im) =
      ∫ u in (0 : ℝ)..t, srcDrift κ xL xR ρL ρR r (Ito.rpath w) u := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  have h := integral_vSrc_mul_im_sub_eq (κ := κ) (ρL := ρL) (ρR := ρR) hreg hF hr
    ⟨t.coe_nonneg, by exact_mod_cast htT⟩
  simp only [Ito.fwdMap_clampDrv_of_le htT₂] at h
  rw [h]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le t.coe_nonneg] at hu
  simp only [srcDrift_clampDrv (hu.2.trans htT₂)]

theorem integrable_mul_im_sub_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ z, |φ z| ≤ |vSrc κ xL xR ρL ρR r z|) :
    Integrable fun z => φ z * ((fwdMap (Ito.rpath w) t z).im - z.im) := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  have h := integrable_mul_im_sub hreg hF hr ⟨t.coe_nonneg, by exact_mod_cast htT⟩ hφm hφ
  simp only [Ito.fwdMap_clampDrv_of_le htT₂] at h
  exact h

theorem integrable_couplingMean_mul_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) {u : ℂ → ℝ} {g : ℝ → ℝ} {S : Set ℝ}
    (hu : IsBoundedHarmonicExtension g S u) {φ : ℂ → ℝ} (hφm : Measurable φ)
    (hφ : ∀ z, |φ z| ≤ |vSrc κ xL xR ρL ρR r z|) :
    Integrable fun z => couplingMean κ (Ito.rpath w) t u z * φ z := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  obtain ⟨C, hC⟩ := hu.2.1
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  have h := integrable_couplingMean_mul_src (κ := κ) hreg hF hr (continuousOn_of_isBoundedHarmonicExtension hu) hC
    ⟨t.coe_nonneg, by exact_mod_cast htT⟩ hφm hφ
  rwa [couplingMean_clampDrv_of_le κ _ t.coe_nonneg htT₂] at h

end Path

end LocalExt

end InteractingSLE
