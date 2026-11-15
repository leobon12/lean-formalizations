/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BsThr
import InteractingSLE.Spec.Supplement.GW2SdoLaunch

/-!
# A threshold of the stage word along the stage path is a threshold of the near family along the comparison path

Packet PROVE-GW2-BUF (round 16). The near family's word at `m` PRESENTS the stage word `β` (`GW2Sdf.PresentsO`). The
stage word's flow-line data at angle `0` are the family's labels scaled by `√scale = c⁻¹`, with the family's weights,
and with the sides swapped on odd histories. The comparison path is `s ↦ ±c · D(s / c²)` (`scaledPath (c²) (±c) D`).
So a continuation threshold of the stage word along the stage path `D` at stage time `u` is one of the family's word
along the comparison path at time `c² u`:

* `thresholdCondition_swap` (the threshold under the reflection of the sides);
* `frozenDrive_scaledPath_eq`, **`imgState_scaledPath_eq`** (the comparison image state is the state of the dilated
  real-time path);
* **`cmp_threshold_of_stage`** (SDE's `thresholdCondition_cast` and `thresholdCondition_scD_iff`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Restart MartChar.RealFlow Sec5.CrossCond.StagedRepLater

variable {nL nR : ℕ}

/-- **The threshold under the reflection of the sides.** -/
theorem thresholdCondition_swap (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρR ρL w vR vL ↔
      ForceWord.ThresholdCondition ρL ρR (-w) (fun i => -vL i) (fun j => -vR j) := by
  unfold ForceWord.ThresholdCondition
  have h1 : (univ.filter fun i => -vL i = -w) = univ.filter fun i => vL i = w :=
    Finset.filter_congr fun i _ => neg_inj
  have h2 : (univ.filter fun j => -vR j = -w) = univ.filter fun j => vR j = w :=
    Finset.filter_congr fun j _ => neg_inj
  rw [h1, h2]
  exact or_comm

/-- The frozen comparison path agrees with the dilated real-time path before the frozen time. -/
theorem frozenDrive_scaledPath_eq {c : ℝ≥0} (ε : ℝ) (D : ℝ≥0 → ℝ) (v : ℝ≥0) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) v) :
    frozenDrive (scaledPath (c ^ 2) (ε * c) D) v r = scD c (fun q => ε * D q.toNNReal) r := by
  unfold frozenDrive scaledPath scD
  rw [min_eq_left hr.2]
  have h : r.toNNReal / c ^ 2 = (r / (c : ℝ) ^ 2).toNNReal := by
    apply NNReal.eq
    rw [NNReal.coe_div, Real.coe_toNNReal _ hr.1, Real.coe_toNNReal _ (div_nonneg hr.1 (by positivity)),
      NNReal.coe_pow]
  rw [h]
  ring

theorem continuous_scD_rp {D : ℝ≥0 → ℝ} (hD : Continuous D) (c ε : ℝ) :
    Continuous (scD c (fun q => ε * D q.toNNReal)) :=
  continuous_scD (continuous_const.mul (hD.comp continuous_real_toNNReal)) c

/-- **The comparison image state is the state of the dilated real-time path.** -/
theorem imgState_scaledPath_eq (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {c : ℝ≥0} (hc : 0 < c) (ε : ℝ)
    {D : ℝ≥0 → ℝ} (hD : Continuous D) (u : ℝ≥0) :
    GW2Sdg.imgState xL xR (scaledPath (c ^ 2) (ε * c) D) (c ^ 2 * u) =
      (scD c (fun q => ε * D q.toNNReal) ((c : ℝ) ^ 2 * u),
        fun i => -rightImg (fun v => -scD c (fun q => ε * D q.toNNReal) v) (-xL i) ((c : ℝ) ^ 2 * u),
        fun j => rightImg (scD c (fun q => ε * D q.toNNReal)) (xR j) ((c : ℝ) ^ 2 * u)) := by
  have hGc : Continuous (scD c (fun q => ε * D q.toNNReal)) := continuous_scD_rp hD c ε
  have hcoe : ((c ^ 2 * u : ℝ≥0) : ℝ) = (c : ℝ) ^ 2 * u := by push_cast; ring
  have hfr : ∀ r ∈ Icc (0 : ℝ) ((c ^ 2 * u : ℝ≥0) : ℝ),
      frozenDrive (scaledPath (c ^ 2) (ε * c) D) ((c ^ 2 * u : ℝ≥0) : ℝ) r = scD c (fun q => ε * D q.toNNReal) r :=
    fun r hr => frozenDrive_scaledPath_eq ε D _ hr
  have hc0 : c ≠ 0 := hc.ne'
  unfold GW2Sdg.imgState
  refine Prod.ext ?_ (Prod.ext (funext fun i => ?_) (funext fun j => ?_))
  · show scaledPath (c ^ 2) (ε * c) D (c ^ 2 * u) = scD c (fun q => ε * D q.toNNReal) ((c : ℝ) ^ 2 * u)
    simp only [scaledPath, scD]
    have h1 : c ^ 2 * u / c ^ 2 = u := by rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hc0)]
    have h2 : ((c : ℝ) ^ 2 * u / (c : ℝ) ^ 2).toNNReal = u := by
      rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 (NNReal.coe_ne_zero.2 hc0)), Real.toNNReal_coe]
    rw [h1, h2]
    ring
  · show -rightImg (fun s => -frozenDrive (scaledPath (c ^ 2) (ε * c) D) ((c ^ 2 * u : ℝ≥0) : ℝ) s) (-xL i)
        ((c ^ 2 * u : ℝ≥0) : ℝ) = -rightImg (fun v => -scD c (fun q => ε * D q.toNNReal) v) (-xL i) ((c : ℝ) ^ 2 * u)
    rw [Supp8.GB6.rightImg_congr (w' := fun v => -scD (c : ℝ) (fun q => ε * D q.toNNReal) v) hGc.neg
      (NNReal.coe_nonneg _) fun r hr => by simp only [hfr r hr], hcoe]
  · show rightImg (frozenDrive (scaledPath (c ^ 2) (ε * c) D) ((c ^ 2 * u : ℝ≥0) : ℝ)) (xR j)
        ((c ^ 2 * u : ℝ≥0) : ℝ) = rightImg (scD c (fun q => ε * D q.toNNReal)) (xR j) ((c : ℝ) ^ 2 * u)
    rw [Supp8.GB6.rightImg_congr hGc (NNReal.coe_nonneg _) hfr, hcoe]

/-- **A threshold of the stage word along the stage path is a threshold of the presented family's word along the
comparison path** (dilation by `c = (√scale)⁻¹`; reflection of the sides on odd histories). -/
theorem cmp_threshold_of_stage {κ : ℝ} {β : BoundaryWord} {scale c : ℝ≥0} (hc : 0 < c)
    (hsc : Real.sqrt scale = (c : ℝ)⁻¹) (flip : Bool) {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (hP : GW2Sdf.PresentsO κ β scale flip xL ρL xR ρR) {D : ℝ≥0 → ℝ} (hD : Continuous D) (u : ℝ≥0)
    (hthr : ForceWord.ThresholdCondition (flowLineRhoL κ β.fn β.jumps 0 0) (flowLineRhoR κ β.fn β.jumps 0 0) (D u)
      (fun i => -rightImg (fun v : ℝ => -D v.toNNReal) (-flowLineXL β.fn β.jumps 0 i) u)
      (fun j => rightImg (fun v : ℝ => D v.toNNReal) (flowLineXR β.fn β.jumps 0 j) u)) :
    ForceWord.ThresholdCondition ρL ρR
      (GW2Sdg.imgState xL xR (scaledPath (c ^ 2) (GW2Sdy.nearSign flip * c) D) (c ^ 2 * u)).1
      (GW2Sdg.imgState xL xR (scaledPath (c ^ 2) (GW2Sdy.nearSign flip * c) D) (c ^ 2 * u)).2.1
      (GW2Sdg.imgState xL xR (scaledPath (c ^ 2) (GW2Sdy.nearSign flip * c) D) (c ^ 2 * u)).2.2 := by
  rw [imgState_scaledPath_eq xL xR hc _ hD u]
  have hc' : (0 : ℝ) < c := hc
  have hcs : ∀ x : ℝ, (c : ℝ) * (Real.sqrt scale * x) = x := fun x => by
    rw [← mul_assoc, hsc, mul_inv_cancel₀ hc'.ne', one_mul]
  have hDu : D u = (fun v : ℝ => D v.toNNReal) (u : ℝ) := by simp only [Real.toNNReal_coe]
  have hDc : Continuous fun v : ℝ => D v.toNNReal := hD.comp continuous_real_toNNReal
  cases flip with
  | false =>
    obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := hP
    rw [← hxL, ← hxR, ← hρL, ← hρR] at hthr
    have h1 := (GW2Sdo.thresholdCondition_cast eL eR ρL
      (fun i => -rightImg (fun v : ℝ => -D v.toNNReal) (-(Real.sqrt scale * xL i)) u) ρR
      (fun j => rightImg (fun v : ℝ => D v.toNNReal) (Real.sqrt scale * xR j) u) (D u)).1 hthr
    rw [hDu] at h1
    have h2 := (GW2Sdo.thresholdCondition_scD_iff hDc hc' u.coe_nonneg ρL ρR (fun i => Real.sqrt scale * xL i)
      (fun j => Real.sqrt scale * xR j)).2 h1
    simp only [hcs] at h2
    simpa only [GW2Sdy.nearSign, Bool.false_eq_true, ↓reduceIte, one_mul] using h2
  | true =>
    obtain ⟨eL, eR, hxL, hxR, hρL, hρR⟩ := hP
    rw [← hxL, ← hxR, ← hρL, ← hρR] at hthr
    have h1 := (GW2Sdo.thresholdCondition_cast eL eR ρR
      (fun j => -rightImg (fun v : ℝ => -D v.toNNReal) (-(-(Real.sqrt scale * xR j))) u) ρL
      (fun i => rightImg (fun v : ℝ => D v.toNNReal) (-(Real.sqrt scale * xL i)) u) (D u)).1 hthr
    have h3 := (thresholdCondition_swap ρL ρR (D u)
      (fun i => rightImg (fun v : ℝ => D v.toNNReal) (-(Real.sqrt scale * xL i)) u)
      (fun j => -rightImg (fun v : ℝ => -D v.toNNReal) (-(-(Real.sqrt scale * xR j))) u)).1 h1
    have hDt : Continuous fun v : ℝ => -D v.toNNReal := hDc.neg
    have h3' : ForceWord.ThresholdCondition ρL ρR ((fun v : ℝ => -D v.toNNReal) (u : ℝ))
        (fun i => -rightImg (fun v => -(fun v : ℝ => -D v.toNNReal) v) (-(Real.sqrt scale * xL i)) u)
        (fun j => rightImg (fun v : ℝ => -D v.toNNReal) (Real.sqrt scale * xR j) u) := by
      simpa only [neg_neg, Real.toNNReal_coe] using h3
    have h4 := (GW2Sdo.thresholdCondition_scD_iff hDt hc' u.coe_nonneg ρL ρR (fun i => Real.sqrt scale * xL i)
      (fun j => Real.sqrt scale * xR j)).2 h3'
    simp only [hcs] at h4
    simpa only [GW2Sdy.nearSign, ↓reduceIte, neg_one_mul] using h4

end InteractingSLE.Theorem14.GW2Bh
