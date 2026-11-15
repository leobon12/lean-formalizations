/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Cond
import InteractingSLE.Spec.Coupling.SafeStop
import InteractingSLE.Spec.Coupling.WholeField3Brown
import InteractingSLE.Spec.Sec7.TwoForceMain2Riemann
import InteractingSLE.Spec.Sec2.TwoSeedLawBridge

/-!
# The local comparison of Aux. lemma 55: the tested mean through the local stop and its brackets

Packet PROVE-LOCEXT-A2, step 4 (path side of (HL4)). Source: Aux. lemma 55, proof (`source/spec/p241-288.md`
L163–L180, p. 248): "`(M_t − m, v) = ∫₀ᵗ a_s dB_s`, `a_s = ∫ k_s(z) v(z) d²z`, `0 ≤ t ≤ S`".

The integrated means of PROVE-T11-ITO (`d𝔥_t(z) = Im(2/f_t(z)) dB_t`, `Ito.exists_martingale_couplingMean`,
`Ito.exists_martingale_couplingMean_mul_B`) are integrated against the source approximations `v_n` at protected stops
(`Coupling.TestMean`, `Coupling.SafeStop`). This file supplies the protection through the local stop:

* `half_im_le_im_fwdMap`: in the local regime, `Im f_s(z) ≥ Im z / 2` on the source (`6r ≤ |z|`), since
  `|d Im f / ds| = 2 Im f/|f|² ≤ 32 Im z/(121 r²)`;
* `isTestSafe_vApprox`: along a good path the local stop protects the support of every `v_n` at height
  `1/(2(n+1))` (`Coupling.IsTestSafe`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull IsForwardSol)
open LQGMetric (TestOn DistOn)

/-! ### Height of the source under the flow -/

section Height

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {W : ℝ → ℝ} {T : ℝ}

/-- `|Im(2/w)| = 2 Im w/|w|²`. -/
theorem abs_im_two_div_le {w : ℂ} (hw : 0 ≤ w.im) {c : ℝ} (hc : 0 < c) (hwc : c ≤ ‖w‖) :
    |(2 / w).im| ≤ 2 * w.im / c ^ 2 := by
  have hw0 : w ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hc hwc)
  rw [Complex.div_im]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, zero_div, zero_sub, abs_neg]
  rw [abs_div, abs_of_nonneg (mul_nonneg zero_le_two hw), abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  exact div_le_div_of_nonneg_left (mul_nonneg zero_le_two hw) (by positivity)
    (pow_le_pow_left₀ hc.le hwc 2)

/-- **The source stays high**: in the local regime, `Im f_s(z) ≥ Im z / 2` for `z ∈ ℍ`, `6r ≤ |z|`. -/
theorem half_im_le_im_fwdMap (h : IsLocalRegime W r T) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖) {s : ℝ}
    (hs : s ∈ Icc 0 T) : z.im / 2 ≤ (fwdMap W s z).im := by
  have hr := h.r_pos
  have halive : z ∈ H \ fwdHull W T := h.mem_of_lt_norm hz (by linarith)
  have heq := Ito.fwdMap_eq_sub_add_integral h.cont h.T_nonneg halive hs
  have hint : IntervalIntegrable (fun u => 2 / fwdMap W u z) volume 0 s :=
    (continuousOn_const.div ((Ito.continuousOn_fwdMap_time' h.cont h.T_nonneg halive).mono
      (Icc_subset_Icc le_rfl hs.2)) fun u hu =>
        Ito.fwdMap_ne_zero h.cont h.T_nonneg halive ⟨hu.1, hu.2.trans hs.2⟩).intervalIntegrable_of_Icc hs.1
  have him : (fwdMap W s z).im = z.im + ∫ u in (0 : ℝ)..s, (2 / fwdMap W u z).im := by
    rw [heq]
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
    congr 1
    rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    rfl
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) s, ‖(2 / fwdMap W u z).im‖ ≤ 32 * z.im / (121 * r ^ 2) := by
    intro u hu
    rw [uIoc_of_le hs.1] at hu
    have huT : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans hs.2⟩
    have hn := h.le_norm_fwdMap_src hz hz6 huT
    have hpos := (Ito.im_fwdMap_pos h.cont h.T_nonneg halive huT).le
    have hle := im_fwdMap_le_im h halive huT
    rw [Real.norm_eq_abs]
    refine (abs_im_two_div_le hpos (by positivity) hn).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg hs.1, Real.norm_eq_abs] at hI
  have hsT : s ≤ r ^ 2 / 64 := hs.2.trans h.T_le
  have h1 : 32 * z.im / (121 * r ^ 2) * s ≤ z.im / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [him]
  linarith [neg_abs_le (∫ u in (0 : ℝ)..s, (2 / fwdMap W u z).im)]

end Height

/-! ### Protection of the approximations along good paths -/

section Protect

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- A forward solution only sees the driver on `[0, T]`. -/
theorem isForwardSol_congr {W W' : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ} (h : ∀ s ∈ Icc 0 T, W s = W' s)
    (hu : IsForwardSol W z T u) : IsForwardSol W' z T u :=
  ⟨hu.1, fun t ht => ⟨(hu.2 t ht).1, by rw [← h t ht]; exact (hu.2 t ht).2⟩⟩

theorem mem_tsupport_vApprox (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {n : ℕ} {z : ℂ}
    (hz : z ∈ tsupport (vApprox κ xL xR ρL ρR r n)) :
    1 / ((n : ℝ) + 1) ≤ z.im ∧ 6 * r ≤ ‖z‖ ∧ ‖z‖ ≤ 7 * r :=
  ⟨(tsupport_vApprox_subset hF hr n hz).1, tsupport_vApprox_subset_norm hF hr n hz,
    (tsupport_vApprox_subset hF hr n hz).2⟩

/-- **Protection through the stop**: along a good path, at every `t ≤ S`, every point of the support of `v_n` has a
forward solution on `[0, t]` and height `Im f_t ≥ 1/(2(n+1))`. -/
theorem protect_vApprox_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) (n : ℕ) {z : ℂ}
    (hz : z ∈ tsupport (vApprox κ xL xR ρL ρR r n)) :
    (∃ u, IsForwardSol (Ito.rpath w) z t u) ∧ 1 / (2 * ((n : ℝ) + 1)) ≤ (fwdMap (Ito.rpath w) t z).im := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  obtain ⟨hzi, hz6, -⟩ := mem_tsupport_vApprox hF hr hz
  have hr0 := hr.1
  have hzpos : 0 < z.im := lt_of_lt_of_le (by positivity) hzi
  have halive := hreg.mem_of_lt_norm hzpos (by linarith)
  have htT' : (t : ℝ) ≤ T := by exact_mod_cast htT
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  refine ⟨⟨_, isForwardSol_congr (fun s hs => Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨hs.1, hs.2.trans htT₂⟩)
    (Ito.isForwardSol_fwdMap_of_mem hreg.cont t.coe_nonneg (Ito.mem_diff_fwdHull_of_le halive htT'))⟩, ?_⟩
  have h := half_im_le_im_fwdMap hreg hzpos hz6 ⟨t.coe_nonneg, htT'⟩
  rw [Ito.fwdMap_clampDrv_of_le htT₂] at h
  have : 1 / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 := by rw [div_div, mul_comm]
  rw [this]
  linarith

end Protect

/-! ### The process-level setting -/

section Setting

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

/-- The good paths with a continuous noise. -/
def IsGoodNoisePath (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω ∧ Continuous (B · ω)

theorem exists_goodNoiseEvent [IsProbabilityMeasure P]
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω := by
  have hae : ∀ᵐ ω ∂P, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω := by
    filter_upwards [ae_isGoodPath hE hκ, hE.1.1.cont] with ω h1 h2 using ⟨h1, h2⟩
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  refine ⟨Nᶜ, hNm.compl, by rwa [compl_compl], fun ω hω => ?_⟩
  by_contra h
  exact hω (hN h)

/-- The local stop as an `ℝ≥0`-valued time. -/
def stopTime (r : ℝ) (G : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  (localStop r G ζ W ω).untopD 0

theorem coe_stopTime (ω : Ω) : (stopTime r G ζ W ω : WithTop ℝ≥0) = localStop r G ζ W ω := by
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 (localStop_ne_top (r := r) (G := G) (ζ' := ζ) (W' := W) (ω := ω))
  rw [stopTime, ← ha, WithTop.untopD_coe]

theorem stopTime_le_horizon (ω : Ω) : stopTime r G ζ W ω ≤ stopHorizon r := by
  have h := localStop_le_stopHorizon (r := r) (G := G) (ζ' := ζ) (W' := W) (ω := ω)
  rw [← coe_stopTime] at h
  exact WithTop.coe_le_coe.1 h

theorem coe_stopTime_of_mem {ω : Ω} (hω : ω ∈ G) :
    (stopTime r G ζ W ω : WithTop ℝ≥0) = localStopPath r (ζ ω) fun t => W t ω := by
  rw [coe_stopTime, localStop_of_mem hω]

/-- **The local stop is a stopping time of the usual augmentation of the evolution's filtration.** -/
theorem isStoppingTime_stopTime (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0) (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (stopTime r G ζ W ω : WithTop ℝ≥0) := by
  have hE' := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hGt : MeasurableSet[usualAugmentation 𝓕 P 0] G := by
    have h := Ito.measurableSet_usualAugmentation_of_null (𝓕 := 𝓕) hGm.compl hG0 0
    simpa using h.compl
  simp_rw [coe_stopTime]
  exact isStoppingTime_localStop hE'.2.1 hE'.2.2.1 hE'.2.2.2.1 hGt hG r

/-- **Safe protection of every `v_n` by the local stop** along the good paths. -/
theorem isGoodSafe_vApprox (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    (hG : ∀ ω ∈ G, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω) (n : ℕ) {ω : Ω} (hω : ω ∈ G) :
    Coupling.IsGoodSafe κ xL xR ρL ρR W VL VR B ζ (vApprox κ xL xR ρL ρR r n) (stopTime r G ζ W)
      (1 / (2 * ((n : ℝ) + 1))) (r ^ 2 / 64) ω := by
  obtain ⟨hg, hBc⟩ := hG ω hω
  have hS := coe_stopTime_of_mem (r := r) (ζ := ζ) (W := W) hω
  refine ⟨hg.1, hBc, ?_, ?_, fun z hz => ?_⟩
  · have := localStop_lt (fun ω hω => (hG ω hω).1) hF hr hseed hω (r := r)
    rwa [← coe_stopTime] at this
  · have := NNReal.coe_le_coe.2 (stopTime_le_horizon (r := r) (G := G) (ζ := ζ) (W := W) ω)
    rwa [coe_stopHorizon] at this
  · exact protect_vApprox_of_isGoodPath hg.1 hg.2 hF hr hseed hS.le n hz

end Setting

/-! ### The cross bracket `(𝔥, φ) B − ∫ (φ, Im(2/f))` at protected stops -/

section Cross

open Coupling Ito
open scoped Classical

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {φ : ℂ → ℝ} {σ : Ω → ℝ≥0} {δ R N : ℝ}

/-- `∫₀ˢ Im(2/f_u(z)) du = Im f_s(z) − Im z` while `z` is alive. -/
theorem integral_im_two_div_fwdMap {W' : ℝ → ℝ} (hW : Continuous W') {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H \ fwdHull W' T) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ∫ u in (0 : ℝ)..s, (2 / fwdMap W' u z).im = (fwdMap W' s z).im - z.im := by
  have heq := Ito.fwdMap_eq_sub_add_integral hW hT hz hs
  have hint : IntervalIntegrable (fun u => 2 / fwdMap W' u z) volume 0 s :=
    (continuousOn_const.div ((Ito.continuousOn_fwdMap_time' hW hT hz).mono
      (Icc_subset_Icc le_rfl hs.2)) fun u hu =>
        Ito.fwdMap_ne_zero hW hT hz ⟨hu.1, hu.2.trans hs.2⟩).intervalIntegrable_of_Icc hs.1
  have h2 : (∫ u in (0 : ℝ)..s, 2 / fwdMap W' u z).im = ∫ u in (0 : ℝ)..s, (2 / fwdMap W' u z).im := by
    rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
    rfl
  rw [heq]
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, sub_zero, h2]
  ring

/-- The cross integrand `1_G φ(z) (𝔥_{t∧σ}(z) B_{t∧σ} − (Im f_{t∧σ}(z) − Im z))`. -/
def crossIntegrand (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (φ : ℂ → ℝ)
    (σ : Ω → ℝ≥0) (G : Set Ω) (t : ℝ≥0) (z : ℂ) (ω : Ω) : ℝ :=
  meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω * (if ω ∈ G then B (min t (σ ω)) ω else 0) -
    (if ω ∈ G then φ z * ((fwdOn W φ σ G t z ω).im - z.im) else 0)

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
  (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
  {G : Set Ω} (hG0 : MeasurableSet[nullAugmented 𝓕 P 0] G)
  (hGgood : ∀ ω ∈ G, IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ σ δ R N ω) (hφH : tsupport φ ⊆ H)
  (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hδ : 0 < δ)

include hGgood hφH in
/-- Along a good test path, `0 < Im f_r(z) ≤ Im z` on the support for `r ≤ σ`. -/
theorem IsGoodTest.im_fwdMap_mem {ω : Ω} (hω : ω ∈ G) {z : ℂ} (hz : z ∈ tsupport φ) {r : ℝ≥0}
    (hr : r ≤ σ ω) : 0 < (fwdMap (rpath (W · ω)) r z).im ∧ (fwdMap (rpath (W · ω)) r z).im ≤ z.im := by
  have hg := hGgood ω hω
  have hc := hg.continuousOn_rpath
  have hsol := (hg.2.2.2.2.2 z hz).1
  have hrI : (r : ℝ) ∈ Icc 0 (σ ω : ℝ) := ⟨r.coe_nonneg, by exact_mod_cast hr⟩
  refine ⟨Ito.im_fwdMap_pos_of_continuousOn (σ ω).coe_nonneg hc (hφH hz) hsol hrI, ?_⟩
  have hanti := Ito.antitoneOn_im_fwdMap_of_continuousOn (σ ω).coe_nonneg hc (hφH hz) hsol
    ⟨le_rfl, (σ ω).coe_nonneg⟩ hrI hrI.1
  beta_reduce at hanti
  have h0 : (fwdMap (rpath (W · ω)) 0 z).im = z.im := by
    rw [Ito.fwdMap_eq_sub_add_integral_of_continuousOn (σ ω).coe_nonneg hc (hφH hz) hsol
      ⟨le_rfl, (σ ω).coe_nonneg⟩]
    simp
  rwa [h0] at hanti

include hE hσ hG0 hGgood hφH hφc in
theorem measurable_crossIntegrand (t : ℝ≥0) :
    Measurable[(borel ℂ).prod (nullAugmented 𝓕 P t)]
      (fun p : ℂ × Ω => crossIntegrand κ ρL ρR W VL VR B φ σ G t p.1 p.2) := by
  set m𝓖 := nullAugmented 𝓕 P t
  have hm := measurable_meanIntegrand hE hσ hG0 hGgood hφH hφc t (κ := κ) (ρL := ρL) (ρR := ρR)
  have hf := measurable_fwdOn hE hσ hG0 hGgood hφH t (κ := κ) (ρL := ρL) (ρR := ρR)
  have hBm : ∀ s, Measurable[nullAugmented 𝓕 P s] (B s) := fun s =>
    (hE.1.2.1 s).mono (le_nullAugmented 𝓕 P s) le_rfl
  have hBs : Measurable[m𝓖] fun ω => if ω ∈ G then B (min t (σ ω)) ω else 0 :=
    measurable_stopped_of_agree (K := B) (X := B) hσ hBm hG0 0 (fun _ _ _ _ => rfl)
      (fun ω hω => (hGgood ω hω).2.1.continuousOn) t
  have hGt : MeasurableSet[m𝓖] G := (nullAugmented 𝓕 P).mono (zero_le (a := t)) G hG0
  have hS : MeasurableSet[(borel ℂ).prod m𝓖] {p : ℂ × Ω | p.2 ∈ G} := measurable_snd hGt
  have h2 : Measurable[(borel ℂ).prod m𝓖] fun p : ℂ × Ω =>
      (if p.2 ∈ G then φ p.1 * ((fwdOn W φ σ G t p.1 p.2).im - p.1.im) else 0) := by
    have e : (fun p : ℂ × Ω => (if p.2 ∈ G then φ p.1 * ((fwdOn W φ σ G t p.1 p.2).im - p.1.im) else 0)) =
        {p : ℂ × Ω | p.2 ∈ G}.piecewise (fun p => φ p.1 * ((fwdOn W φ σ G t p.1 p.2).im - p.1.im))
          fun _ => 0 := by
      funext p; by_cases hp : p.2 ∈ G <;> simp [hp, Set.piecewise]
    rw [e]
    refine Measurable.piecewise hS ?_ measurable_const
    have hφm : Measurable[(borel ℂ).prod m𝓖] fun p : ℂ × Ω => φ p.1 :=
      (hφc.measurable.mono BorelSpace.measurable_eq.le le_rfl).comp
        measurable_fst
    exact hφm.mul ((Complex.measurable_im.comp hf).sub (Complex.measurable_im.comp measurable_fst))
  exact (hm.mul (hBs.comp measurable_snd)).sub h2

include hE hσ hG0 hGgood hφH hφc hφs hδ in
/-- **The cross bracket is a martingale** (integrated `d⟨𝔥(z), B⟩ = Im(2/f(z)) dt`, with
`∫₀ᵗ Im(2/f_s(z)) ds = Im f_t(z) − Im z`). -/
theorem martingale_crossIntegral (hκ : 0 < κ) (hGc : P Gᶜ = 0) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s)) :
    Martingale (fun t ω => ∫ z, crossIntegrand κ ρL ρR W VL VR B φ σ G t z ω) (nullAugmented 𝓕 P) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  obtain ⟨C, hC⟩ := exists_abs_meanVal_le hφH hφs hδ (κ := κ) (ρL := ρL) (ρR := ρR)
    (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) (xL := xL) (xR := xR) (σ := σ) (R := R) (N := N)
  obtain ⟨Rk, hRk⟩ := hφs.isCompact.isBounded.subset_closedBall 0
  set K := |C| * |R| + |Rk| with hK
  have hbound : ∀ t z ω, |crossIntegrand κ ρL ρR W VL VR B φ σ G t z ω| ≤ K * |φ z| := by
    intro t z ω
    by_cases hz : z ∈ tsupport φ
    · by_cases hω : ω ∈ G
      · have hg := hGgood ω hω
        have hmi := abs_meanIntegrand_le hGgood hC t z ω
        have hBb : |B (min t (σ ω)) ω| ≤ |R| := ((hg.2.2.2.2.1 _ (min_le_right _ _)).2.1).trans (le_abs_self _)
        obtain ⟨hi1, hi2⟩ := IsGoodTest.im_fwdMap_mem hGgood hφH hω hz (min_le_right t (σ ω))
        have hzR : z.im ≤ |Rk| := (Complex.im_le_norm z).trans (by
          have := hRk hz; rw [mem_closedBall, dist_zero_right] at this; exact this.trans (le_abs_self _))
        have hfo : fwdOn W φ σ G t z ω = fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z := by
          simp [fwdOn, hω, hz]
        simp only [crossIntegrand, hω, ↓reduceIte, hfo]
        have h3 : |φ z * ((fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im)| ≤ |Rk| * |φ z| := by
          have hd : |(fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im| ≤ |Rk| := by
            rw [abs_of_nonpos (by linarith)]; linarith
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
        calc |meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω * B (min t (σ ω)) ω -
              φ z * ((fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im)|
            ≤ |meanIntegrand κ ρL ρR W VL VR B φ σ G t z ω| * |B (min t (σ ω)) ω| +
              |φ z * ((fwdMap (rpath (W · ω)) (min t (σ ω) : ℝ≥0) z).im - z.im)| := by
              rw [← abs_mul]; exact abs_sub _ _
          _ ≤ |C| * |φ z| * |R| + |Rk| * |φ z| := add_le_add (mul_le_mul hmi hBb (abs_nonneg _)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))) h3
          _ = K * |φ z| := by rw [hK]; ring
      · simp only [crossIntegrand, meanIntegrand, hω, ↓reduceIte, zero_mul, sub_zero, abs_zero]
        positivity
    · simp [crossIntegrand, meanIntegrand, eq_zero_of_notMem_tsupport' hz]
  refine martingale_integral_of_forall (μ := volume)
    (fun t => measurable_crossIntegrand hE hσ hG0 hGgood hφH hφc t)
    ((hφc.integrable_of_hasCompactSupport hφs).abs.const_mul K)
    (ae_of_all _ fun z t ω => hbound t z ω)
    (ae_of_all _ fun z s t hst S hS => ?_)
  by_cases hz : z ∈ tsupport φ
  · have hσpz : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω ∧
        (∃ u, IsForwardSol (rpath (W · ω)) z (σ ω) u) ∧
        δ ≤ (fwdMap (rpath (W · ω)) (σ ω) z).im ∧ (σ ω : ℝ) ≤ N ∧
        ∀ s ≤ σ ω, |W s ω| ≤ R ∧ |B s ω| ≤ R ∧ (∀ i, |VL i s ω| ≤ R) ∧ ∀ i, |VR i s ω| ≤ R := by
      filter_upwards [hGae] with ω hω
      obtain ⟨-, -, hσζ, hN, hR, hK⟩ := hGgood ω hω
      exact ⟨hσζ, (hK z hz).1, (hK z hz).2, hN, hR⟩
    obtain ⟨M, hM, hMae⟩ := exists_martingale_couplingMean_mul_B hE hκ (hφH hz) hσ hδ hσpz u hu
    have hY : ∀ r, (fun ω => crossIntegrand κ ρL ρR W VL VR B φ σ G r z ω) =ᵐ[P]
        fun ω => M r ω * φ z := fun r => by
      filter_upwards [hMae, hGae] with ω hω hωG
      have hg := hGgood ω hωG
      have hrI : ((min r (σ ω) : ℝ≥0) : ℝ) ∈ Icc 0 (σ ω : ℝ) :=
        ⟨NNReal.coe_nonneg _, by exact_mod_cast min_le_right _ _⟩
      have hint := integral_im_two_div_fwdMap hg.continuous_clampPath (σ ω).coe_nonneg
        ((hg.isProtected hφH) z hz).1 hrI
      have hcl : ∀ v : ℝ, v ≤ σ ω → fwdMap (clampPath W σ ω) v z = fwdMap (rpath (W · ω)) v z :=
        fun v hv => by rw [fwdMap_clampPath hv]
      rw [hcl _ hrI.2] at hint
      have hint' : ∫ s in (0 : ℝ)..((min r (σ ω) : ℝ≥0) : ℝ), (2 / fwdMap (fun s : ℝ => W s.toNNReal ω) s z).im =
          (fwdMap (rpath (W · ω)) (min r (σ ω) : ℝ≥0) z).im - z.im := by
        rw [← hint]
        refine intervalIntegral.integral_congr fun v hv => ?_
        rw [uIcc_of_le (NNReal.coe_nonneg _)] at hv
        simp only [hcl v (hv.2.trans hrI.2)]
        rfl
      have hfo : fwdOn W φ σ G r z ω = fwdMap (rpath (W · ω)) (min r (σ ω) : ℝ≥0) z := by
        simp [fwdOn, hωG, hz]
      simp only [crossIntegrand, meanIntegrand, hωG, ↓reduceIte, hfo]
      rw [hω r, hint', ← hg.couplingMean_eq_meanVal hφH hz (min_le_right _ _) (hu ω _)]
      ring
    rw [integral_congr_ae (ae_restrict_of_ae (hY s)), integral_congr_ae (ae_restrict_of_ae (hY t)),
      integral_mul_const, integral_mul_const, hM.setIntegral_eq hst hS]
  · simp [crossIntegrand, meanIntegrand, eq_zero_of_notMem_tsupport' hz]

end Cross

/-! ### Limits of martingales and the stopped noise -/

section Limits

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **An almost sure limit of `L²`-bounded martingales is a martingale**, in a filtration containing the null sets,
for a measurable integrable limit. -/
theorem martingale_of_tendsto_of_null [IsProbabilityMeasure P] {𝒢 : Filtration ℝ≥0 mΩ}
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 t] N) {Y : ℝ≥0 → Ω → ℝ}
    {Yn : ℕ → ℝ≥0 → Ω → ℝ} (hYn : ∀ n, Martingale (Yn n) 𝒢 P) (hYnL2 : ∀ n t, MemLp (Yn n t) 2 P)
    (hbd : ∀ t, ∃ M, ∀ n, ∫ ω, Yn n t ω ^ 2 ∂P ≤ M)
    (hlim : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => Yn n t ω) atTop (𝓝 (Y t ω)))
    (hYm : ∀ t, Measurable (Y t)) (hYi : ∀ t, Integrable (Y t) P) : Martingale Y 𝒢 P := by
  have hYa : StronglyAdapted 𝒢 Y := fun t => by
    have hg : StronglyMeasurable[𝒢 t] fun ω => limUnder atTop fun n => Yn n t ω :=
      @StronglyMeasurable.limUnder ℕ Ω ℝ (𝒢 t) _ _ atTop _ _ _ _ fun n => (hYn n).1 t
    refine Measurable.stronglyMeasurable fun A hA => ?_
    refine WholeField.measurableSet_of_ae_eq (𝒢.le t) (hnull t) (hYm t hA) (hg.measurable hA) ?_
    filter_upwards [hlim t] with ω hω
    simp only [mem_preimage, hω.limUnder_eq]
  exact Sec7.martingale_of_tendsto_of_sq_bound hYn hYnL2 hbd hlim hYa hYi

/-- **`E B_{t∧ρ}² ≤ t + E B_0²`** for a stop `ρ` of a filtration in which `B` is Brownian and which contains the null
sets (and `B_{t∧ρ} ∈ L²`). -/
theorem integral_sq_stoppedNoise_le [IsProbabilityMeasure P] {𝓔 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓔 B P)
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝓔 t] N) {G : Set Ω}
    (hG : MeasurableSet G) (hG0 : P Gᶜ = 0) (hBc : ∀ ω ∈ G, Continuous (B · ω)) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓔 fun ω => (ρ ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    MemLp (fun ω => B (min t (ρ ω)) ω) 2 P ∧
      ∫ ω, B (min t (ρ ω)) ω ^ 2 ∂P ≤ t + ∫ ω, WholeField.noiseOn B G 0 ω ^ 2 ∂P := by
  obtain ⟨h1, h2⟩ := WholeField.martingale_stoppedNoise hB hnull hG hG0 hBc hρ
  set Y := stoppedProcess (WholeField.noiseOn B G) (fun ω => (ρ ω : WithTop ℝ≥0)) with hY
  set Q : ℝ≥0 → Ω → ℝ := fun t ω => ∫ u in (0 : ℝ)..t, WholeField.stopWeight ρ u ω with hQ
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hG0
  have heq : ∀ s, (fun ω => B (min s (ρ ω)) ω) =ᵐ[P] Y s := fun s => by
    filter_upwards [hGae] with ω hω
    rw [hY, WholeField.stoppedProcess_coe_apply]; simp [WholeField.noiseOn, hω]
  have hQb : ∀ s ω, 0 ≤ Q s ω ∧ Q s ω ≤ s := fun s ω => by
    have hi : IntervalIntegrable (fun u => WholeField.stopWeight ρ u ω) volume 0 s :=
      (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
        (WholeField.measurable_stopWeight ρ ω).aestronglyMeasurable
        (ae_of_all _ fun u => by
          show ‖WholeField.stopWeight ρ u ω‖ ≤ ‖(1 : ℝ)‖
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (WholeField.stopWeight_nonneg ρ u ω), abs_one]
          exact WholeField.stopWeight_le_one ρ u ω)
    refine ⟨intervalIntegral.integral_nonneg s.coe_nonneg fun u _ => WholeField.stopWeight_nonneg ρ u ω, ?_⟩
    have := intervalIntegral.integral_mono_on s.coe_nonneg hi intervalIntegrable_const
      fun u _ => WholeField.stopWeight_le_one ρ u ω
    simpa using this
  have hYm : ∀ s, Measurable (Y s) := fun s => ((h1.1 s).mono (𝓔.le s)).measurable
  have hMm : ∀ s, Measurable (fun ω => Y s ω ^ 2 - Q s ω) := fun s => ((h2.1 s).mono (𝓔.le s)).measurable
  have hQm : ∀ s, Measurable (Q s) := fun s => by
    have : Q s = fun ω => Y s ω ^ 2 - (Y s ω ^ 2 - Q s ω) := funext fun ω => by ring
    rw [this]; exact ((hYm s).pow_const 2).sub (hMm s)
  have hQi : ∀ s, Integrable (Q s) P := fun s => Integrable.of_bound (hQm s).aestronglyMeasurable s
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hQb s ω).1]; exact (hQb s ω).2)
  have hY2 : ∀ s, Integrable (fun ω => Y s ω ^ 2) P := fun s =>
    ((h2.integrable s).add (hQi s)).congr (ae_of_all _ fun ω => sub_add_cancel _ _)
  have hconst := h2.setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le) (MeasurableSet.univ (m := 𝓔 0))
  simp only [Measure.restrict_univ] at hconst
  rw [integral_sub (hY2 0) (hQi 0), integral_sub (hY2 t) (hQi t)] at hconst
  have hQ0 : ∫ ω, Q 0 ω ∂P = 0 := by simp [hQ]
  have hY0 : ∀ ω, Y 0 ω = WholeField.noiseOn B G 0 ω := fun ω => by
    rw [hY, WholeField.stoppedProcess_coe_apply, min_eq_left (show (0 : ℝ≥0) ≤ ρ ω from bot_le)]
  have hQt : ∫ ω, Q t ω ∂P ≤ t := by
    calc ∫ ω, Q t ω ∂P ≤ ∫ _, (t : ℝ) ∂P :=
          integral_mono (hQi t) (integrable_const _) fun ω => (hQb t ω).2
      _ = t := by simp
  refine ⟨?_, ?_⟩
  · refine (memLp_two_iff_integrable_sq (hYm t).aestronglyMeasurable).2 (hY2 t) |>.ae_eq (heq t).symm
  · rw [integral_congr_ae ((heq t).mono fun ω h => congrArg (· ^ 2) h)]
    simp only [hY0, hQ0] at hconst
    linarith

end Limits

/-! ### A uniform bound on the mean through the stop -/

section MeanBound

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- The uniform bound of the mean on the source through the local stop. -/
def meanSrcBound (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ) : ℝ :=
  Coupling.meanHarmonicBound κ ρL ρR + |QuantumZipper.chiC κ| * (32 / (121 * r ^ 2) * (r ^ 2 / 64))

/-- **The coupling mean is uniformly bounded on the source through the stop.** -/
theorem abs_couplingMean_bheAt_le (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖) :
    |couplingMean κ (Ito.rpath w) t (bheAt κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t)) z| ≤
      meanSrcBound κ ρL ρR r := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  have hp' := hp.isSLEPathUpTo le_rfl
  have htζ : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt ht (localStopPath_lt hp hF hr hseed hterm)
  have hC : ∀ y ∈ H, |bheAt κ ρL ρR (fun i => vL i t - w t) (fun i => vR i t - w t) y| ≤
      Coupling.meanHarmonicBound κ ρL ρR := fun y hy => by
    rw [Ito.eqOn_meanHarmonic (fun i => sub_nonpos.2 (hp'.vL_le_w htζ i))
      (fun i => sub_nonneg.2 (hp'.w_le_vR htζ i)) (isBoundedHarmonicExtension_bheAt κ ρL ρR _ _) hy]
    exact Coupling.abs_meanHarmonic_le κ ρL ρR _ _ _
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  have h := abs_couplingMean_src_le (κ := κ) hreg hC hz hz6 ⟨t.coe_nonneg, by exact_mod_cast htT⟩
  rw [couplingMean_clampDrv_of_le κ _ t.coe_nonneg htT₂] at h
  refine h.trans ?_
  have hr0 := hr.1
  unfold meanSrcBound
  gcongr
  exact hreg.T_le

/-- `|Im f_t(z) − Im z| ≤ 7r` on the support of `v_n`, through the stop. -/
theorem abs_im_fwdMap_sub_le (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ localStopPath r ζ w) {z : ℂ} (hz : 0 < z.im) (hz6 : 6 * r ≤ ‖z‖)
    (hz7 : ‖z‖ ≤ 7 * r) : |(fwdMap (Ito.rpath w) t z).im - z.im| ≤ 7 * r := by
  obtain ⟨T, T₂, htT, hTT₂, -, -, hreg⟩ := exists_regime_of_le_localStopPath hp hterm hF hr hseed ht
  have hr0 := hr.1
  have halive := hreg.mem_of_lt_norm hz (by linarith)
  have htT₂ : (t : ℝ) ≤ T₂ := by exact_mod_cast htT.trans hTT₂.le
  have htI : (t : ℝ) ∈ Icc 0 (T : ℝ) := ⟨t.coe_nonneg, by exact_mod_cast htT⟩
  have h1 := im_fwdMap_le_im hreg halive htI
  have h2 := (Ito.im_fwdMap_pos hreg.cont hreg.T_nonneg halive htI).le
  rw [Ito.fwdMap_clampDrv_of_le htT₂] at h1 h2
  rw [abs_of_nonpos (by linarith)]
  linarith [Complex.im_le_norm z]

end MeanBound

end LocalExt

end InteractingSLE
