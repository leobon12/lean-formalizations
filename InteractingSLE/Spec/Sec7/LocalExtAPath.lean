/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtAHL7

/-!
# The local comparison of Aux. lemma 55: (HL6)–(HL7) along the paths of an evolution, through the local stop

Packet PROVE-LOCEXT-A. The deterministic statements of `LocalExtAHL7` are stated for a continuous driver
`W : ℝ → ℝ` in the local regime. Here they are applied to a good path of an integrated `SLE_κ(ρ)` evolution
(`IsGoodPath`, the frozen Definition 2.1 with the terminal state of Aux. lemma 3) up to the local stop
`S = (r²/64) ∧ inf{t < ζ : |W_t| > r/4}` of `LocalExtASetup`: the driver clamped after a time strictly between `S`
and the lifetime is in the local regime, and the distant marks are separated from it by `7r`.

## Main results

* `isLocalRegime_of_le_localStopPath`, `hasDistantMarks_of_le_localStopPath`: the regime along a good path;
* **`srcDrift_eq_distDrift_of_isGoodPath`**: (HL7) along a good path, for every `u ≤ S`:
  `∫ Im(2/f_u(z)) v(z) dz = κ^{-1/2} ∑_{j∈J} ρ_j/(W_u − V^j_u)`;
* **`greenPot_eq_of_isGoodPath`**: (HL6) along a good path, for every `t ≤ S` and `y ∈ ℍ ∖ K_t`:
  `G_{ℍ∖K_t} v (y) = f(y) − q(y) + q_t(y)` (in particular `= q_t(y)` near the seed, where `f = q`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open QuantumZipper (H fwdMap fwdHull)

section PathRegime

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {r : ℝ}

/-- **The driver of a path in the local regime** up to every `T ≤ S`, `T < ζ`: the driver clamped after a time
`T₂ ∈ (T, ζ)`. -/
theorem isLocalRegime_of_le_localStopPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hr : 0 < r) {T T₂ : ℝ≥0} (hT : (T : WithTop ℝ≥0) ≤ localStopPath r ζ w) (hTT₂ : T ≤ T₂)
    (hT₂ : (T₂ : ℝ≥0∞) < ζ) : IsLocalRegime (Ito.clampDrv (Ito.rpath w) T₂) r T := by
  have hp' := hp.isSLEPathUpTo le_rfl
  have hwc := hp'.continuousOn_w
  refine ⟨Ito.continuous_clampDrv T₂.coe_nonneg (Ito.continuousOn_rpath hwc hT₂), ?_, hr, T.coe_nonneg, ?_,
    fun u hu => ?_⟩
  · rw [Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨le_rfl, T₂.coe_nonneg⟩]
    simp [Ito.rpath, hp'.w_zero]
  · have := NNReal.coe_le_coe.2 (le_stopHorizon_of_le_localStopPath hT)
    rwa [coe_stopHorizon] at this
  · have huT₂ : u ≤ T₂ := hu.2.trans (by exact_mod_cast hTT₂)
    rw [Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨hu.1, huT₂⟩, Ito.rpath]
    have hut : u.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hu.2
    exact abs_le_of_le_localStopPath hwc hp'.w_zero hr.le ((WithTop.coe_le_coe.2 hut).trans hT)
      (lt_of_le_of_lt (by exact_mod_cast hut.trans hTT₂) hT₂)

/-- **The distant marks of a path in the local regime.** -/
theorem hasDistantMarks_of_le_localStopPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) {T T₂ : ℝ≥0}
    (hT : (T : WithTop ℝ≥0) ≤ localStopPath r ζ w) (hTT₂ : T ≤ T₂) (hT₂ : (T₂ : ℝ≥0∞) < ζ) :
    HasDistantMarks xL xR (Ito.clampDrv (Ito.rpath w) T₂) (fun i => Ito.rpath (vL i))
      (fun i => Ito.rpath (vR i)) r T := by
  have hp' := hp.isSLEPathUpTo le_rfl
  have hwc := hp'.continuousOn_w
  have hTζ : (T : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hTT₂) hT₂
  -- the clamped driver agrees with the path on `[0, T]`
  have hA : ∀ u ∈ Icc (0 : ℝ) T, Ito.clampDrv (Ito.rpath w) T₂ u = w u.toNNReal := fun u hu =>
    Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨hu.1, hu.2.trans (by exact_mod_cast hTT₂)⟩
  have hlt : ∀ u ∈ Icc (0 : ℝ) T, (u.toNNReal : ℝ≥0∞) < ζ := fun u hu =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hu.2) hTζ
  have hstop : ∀ u ∈ Icc (0 : ℝ) T, (u.toNNReal : WithTop ℝ≥0) ≤ localStopPath r ζ w := fun u hu =>
    (WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hu.2)).trans hT
  have hwle : ∀ u ∈ Icc (0 : ℝ) T, |w u.toNNReal| ≤ r / 4 := fun u hu =>
    abs_le_of_le_localStopPath hwc hp'.w_zero hr.1.le (hstop u hu) (hlt u hu)
  -- the integral equation of a mark in real time
  have heqL : ∀ i, ∀ u ∈ Icc (0 : ℝ) T, Ito.rpath (vL i) u = xL i +
      ∫ s in (0 : ℝ)..u, 2 / (Ito.rpath (vL i) s - Ito.clampDrv (Ito.rpath w) T₂ s) := fun i u hu => by
    have h := hp'.vL_eq (hlt u hu) i
    rw [Real.coe_toNNReal _ hu.1] at h
    rw [Ito.rpath, h]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hu.1] at hs
    simp only [Ito.rpath, hA s ⟨hs.1, hs.2.trans hu.2⟩]
  have heqR : ∀ i, ∀ u ∈ Icc (0 : ℝ) T, Ito.rpath (vR i) u = xR i +
      ∫ s in (0 : ℝ)..u, 2 / (Ito.rpath (vR i) s - Ito.clampDrv (Ito.rpath w) T₂ s) := fun i u hu => by
    have h := hp'.vR_eq (hlt u hu) i
    rw [Real.coe_toNNReal _ hu.1] at h
    rw [Ito.rpath, h]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hu.1] at hs
    simp only [Ito.rpath, hA s ⟨hs.1, hs.2.trans hu.2⟩]
  refine ⟨fun i hi => ⟨?_, heqL i, fun u hu => ?_⟩, fun i hi => ⟨?_, heqR i, fun u hu => ?_⟩,
    fun i _ u hu => ?_, fun i _ u hu => ?_⟩
  · exact Ito.continuousOn_rpath (hp'.continuousOn_vL i) hTζ
  · rw [hA u hu, Ito.rpath]
    have := seven_mul_le_sub_vL hp' hF hr (Finset.mem_filter.1 hi).2 (hlt u hu) (hwle u hu)
    rw [abs_of_nonpos (by linarith [hr.1])]
    linarith
  · exact Ito.continuousOn_rpath (hp'.continuousOn_vR i) hTζ
  · rw [hA u hu, Ito.rpath]
    have := seven_mul_le_vR_sub hp' hF hr (Finset.mem_filter.1 hi).2 (hlt u hu) (hwle u hu)
    rw [abs_of_nonneg (by linarith [hr.1])]
    linarith
  · rw [hA u hu, Ito.rpath]; exact hp'.vL_le_w (hlt u hu) i
  · rw [hA u hu, Ito.rpath]; exact hp'.w_le_vR (hlt u hu) i

/-- The clamped driver has the same Loewner flow up to `T₂`. -/
theorem srcDrift_clampDrv {T₂ : ℝ} {u : ℝ} (hu : u ≤ T₂) (w' : ℝ → ℝ) :
    srcDrift κ xL xR ρL ρR r (Ito.clampDrv w' T₂) u = srcDrift κ xL xR ρL ρR r w' u := by
  simp only [srcDrift, Ito.fwdMap_clampDrv_of_le hu]

/-- On a good path with an admissible seed, the local stop is a positive finite time strictly before the lifetime,
and some time `T₂` lies strictly between them. -/
theorem exists_stop_lt (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hterm : HasThresholdLimit ρL ρR w vL vR ζ)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ T T₂ : ℝ≥0, localStopPath r ζ w = T ∧ 0 < T ∧ T < T₂ ∧ (T₂ : ℝ≥0∞) < ζ := by
  have hlt := localStopPath_lt hp hF hr hseed hterm
  obtain ⟨T, hT⟩ := WithTop.ne_top_iff_exists.1
    (ne_top_of_le_ne_top WithTop.coe_ne_top (localStopPath_le_stopHorizon (r := r) (ζ := ζ) (w := w)))
  have hζ0 : 0 < ζ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h19, -⟩ := hp
    exact pos_iff_ne_zero.2 fun h0 => hseed (h19 h0)
  have hpos := localStopPath_pos (hp.isSLEPathUpTo le_rfl).continuousOn_w hp.1 hr.1 hζ0
  rw [← hT] at hlt hpos
  obtain ⟨T₂, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
  exact ⟨T, T₂, hT.symm, WithTop.coe_pos.1 hpos, WithTop.coe_lt_coe.1 h1, h2⟩

/-- **(HL7) along a good path** (p. 249): for every `u ≤ S`, the source drift of the cutoff field equals the drift
of the distant marks, `∫ Im(2/f_u(z)) v(z) dz = κ^{-1/2} ∑_{j∈J} ρ_j/(W_u − V^j_u)`. -/
theorem srcDrift_eq_distDrift_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {u : ℝ} (hu0 : 0 ≤ u)
    (hu : (u.toNNReal : WithTop ℝ≥0) ≤ localStopPath r ζ w) :
    srcDrift κ xL xR ρL ρR r (Ito.rpath w) u =
      distDrift κ xL xR ρL ρR (w u.toNNReal) (fun i => vL i u.toNNReal) (fun i => vR i u.toNNReal) := by
  obtain ⟨T, T₂, hS, hTpos, hTT₂, hT₂⟩ := exists_stop_lt hp hterm hF hr hseed
  have hTle : (T : WithTop ℝ≥0) ≤ localStopPath r ζ w := hS.ge
  have hreg := isLocalRegime_of_le_localStopPath hp hr.1 hTle hTT₂.le hT₂
  have hD := hasDistantMarks_of_le_localStopPath hp hF hr hTle hTT₂.le hT₂
  have huT : u ≤ T := by
    have := WithTop.coe_le_coe.1 (hu.trans hS.le)
    exact (Real.toNNReal_le_iff_le_coe.1 this)
  have h := srcDrift_eq_distDrift (κ := κ) (ρL := ρL) (ρR := ρR) hreg hF hr hD (by exact_mod_cast hTpos)
    ⟨hu0, huT⟩
  have huT₂ : u ≤ T₂ := huT.trans (by exact_mod_cast hTT₂.le)
  rw [srcDrift_clampDrv huT₂, Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨hu0, huT₂⟩] at h
  exact h

/-- **(HL6) along a good path** (p. 249: "`f − P_t f = q − q_t` on `ℍ ∖ K_t`"): for every `t ≤ S` and `y` alive at
`t`, `G_{ℍ∖K_t} v (y) = f(y) − q(y) + q_t(y)`. -/
theorem greenPot_eq_of_isGoodPath (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hterm : HasThresholdLimit ρL ρR w vL vR ζ) (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : (t.toNNReal : WithTop ℝ≥0) ≤ localStopPath r ζ w) {y : ℂ}
    (hy : y ∈ H \ fwdHull (Ito.rpath w) t) :
    greenPot κ xL xR ρL ρR r (Ito.rpath w) t y = fCut κ xL xR ρL ρR r y - qExt κ xL xR ρL ρR y +
      qAt κ xL xR ρL ρR (Ito.rpath w) (fun i => Ito.rpath (vL i)) (fun i => Ito.rpath (vR i)) t y := by
  obtain ⟨T, T₂, hS, hTpos, hTT₂, hT₂⟩ := exists_stop_lt hp hterm hF hr hseed
  have hTle : (T : WithTop ℝ≥0) ≤ localStopPath r ζ w := hS.ge
  have hreg := isLocalRegime_of_le_localStopPath hp hr.1 hTle hTT₂.le hT₂
  have hD := hasDistantMarks_of_le_localStopPath hp hF hr hTle hTT₂.le hT₂
  have htT : t ≤ T := Real.toNNReal_le_iff_le_coe.1 (WithTop.coe_le_coe.1 (ht.trans hS.le))
  have htT₂ : t < T₂ := lt_of_le_of_lt htT (by exact_mod_cast hTT₂)
  have hwc := (hp.isSLEPathUpTo le_rfl).continuousOn_w
  have hK : fwdHull (Ito.clampDrv (Ito.rpath w) T₂) t = fwdHull (Ito.rpath w) t :=
    fwdHull_eq_of_eqOn ht0 htT₂ fun s hs => Ito.clampDrv_eqOn (W := Ito.rpath w) hs
  have hy' : y ∈ H \ fwdHull (Ito.clampDrv (Ito.rpath w) T₂) t := by rwa [hK]
  have h0 := dFun_eq_zero (κ := κ) (ρL := ρL) (ρR := ρR) hreg hF hr hD ⟨ht0, htT⟩ hy'
  rw [dFun_eq hreg hF hr hD ⟨ht0, htT⟩ hy'] at h0
  have hG : greenPot κ xL xR ρL ρR r (Ito.clampDrv (Ito.rpath w) T₂) t y =
      greenPot κ xL xR ρL ρR r (Ito.rpath w) t y := by
    simp only [greenPot, Ito.fwdMap_clampDrv_of_le htT₂.le]
  have hq : qAt κ xL xR ρL ρR (Ito.clampDrv (Ito.rpath w) T₂) (fun i => Ito.rpath (vL i))
      (fun i => Ito.rpath (vR i)) t y =
      qAt κ xL xR ρL ρR (Ito.rpath w) (fun i => Ito.rpath (vL i)) (fun i => Ito.rpath (vR i)) t y := by
    simp only [qAt, Ito.fwdMap_clampDrv_of_le htT₂.le, Ito.clampDrv_eqOn (W := Ito.rpath w) ⟨ht0, htT₂.le⟩]
  rw [hG, hq] at h0
  linarith

end PathRegime

end LocalExt

end InteractingSLE
