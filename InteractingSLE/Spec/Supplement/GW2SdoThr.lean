/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedRepLaterScale
import InteractingSLE.Spec.Supplement.GW2SdnThr
import InteractingSLE.Spec.Supplement.SB2VrBad

/-!
# Review defect N4, item 2: the continuation threshold is invariant under the chart dilation

Packet PROVE-GW2-SDE (round 14). `OpenLinesS.noThreshold` is read in the stage chart; the candidate's lifetime is read
in its launch chart (RELDET's `GW2Rd.ae_candidate_life_badEntrance`), and the two charts differ by a dilation on the
stage domain (STAGEMEAN's step 3, `ca = λ · cs`). Under a dilation by `c > 0` the driver becomes `scD c w`
(`s ↦ c w(s/c²)`), the marks `c x`, and the time `c² t`; NOJUMP's/Sec5's `rightImg_scale` scales the images by `c`.
So a continuation threshold in one chart is one in the other:

* **`not_threshold_of_notMem_badSet`**: at a time `t > 0` where the Loewner trace is off NOJUMP's bad set
  (`SB.Vr.badSet`) of the force word, there is no continuation threshold (`GW2Sdn.threshold_real_tip` on the trace and
  on the reflected trace). With RELDET's `GW2Rd.ae_candidate_life_badEntrance` (the launch trace stays off the closed
  bad set of the launch word before the lifetime) this is "no threshold before the lifetime" in launch coordinates;
* **`thresholdCondition_scD_iff`**: the frozen `ForceWord.ThresholdCondition` of the state of `scD c w` at `c² t`
  with marks `c xL`, `c xR` (left images `−rightImg (−·) (−·)`, as in `OpenLinesS.noThreshold`) holds iff that of `w`
  at `t` with marks `xL`, `xR` does.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset

namespace InteractingSLE.Theorem14.GW2Sdo

open MartChar.RealFlow Sec5.CrossCond.StagedRepLater

/-- **The continuation threshold is invariant under dilation** (deterministic). -/
theorem thresholdCondition_scD_iff {w : ℝ → ℝ} (hw : Continuous w) {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR (scD c w (c ^ 2 * t))
        (fun i => -rightImg (fun v => -scD c w v) (-(c * xL i)) (c ^ 2 * t))
        (fun j => rightImg (scD c w) (c * xR j) (c ^ 2 * t)) ↔
      ForceWord.ThresholdCondition ρL ρR (w t) (fun i => -rightImg (fun v => -w v) (-xL i) t)
        (fun j => rightImg w (xR j) t) := by
  have hc0 : c ≠ 0 := hc.ne'
  have hD : scD c w (c ^ 2 * t) = c * w t := by
    simp only [scD]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hc0)]
  have hneg : (fun v => -scD c w v) = scD c (fun v => -w v) := by
    funext v
    simp only [scD]
    ring
  have hR : ∀ j, rightImg (scD c w) (c * xR j) (c ^ 2 * t) = c * rightImg w (xR j) t := fun j =>
    rightImg_scale hw hc (xR j) ht
  have hL : ∀ i, rightImg (fun v => -scD c w v) (-(c * xL i)) (c ^ 2 * t) =
      c * rightImg (fun v => -w v) (-xL i) t := fun i => by
    rw [hneg, show -(c * xL i) = c * (-xL i) by ring]
    exact rightImg_scale hw.neg hc (-xL i) ht
  unfold ForceWord.ThresholdCondition
  have hsetL : (univ.filter fun i => -rightImg (fun v => -scD c w v) (-(c * xL i)) (c ^ 2 * t) =
      scD c w (c ^ 2 * t)) = univ.filter fun i => -rightImg (fun v => -w v) (-xL i) t = w t := by
    refine Finset.filter_congr fun i _ => ?_
    rw [hL i, hD]
    constructor
    · intro h
      have : c * (-rightImg (fun v => -w v) (-xL i) t) = c * w t := by linarith
      exact mul_left_cancel₀ hc0 this
    · intro h
      rw [← h]
      ring
  have hsetR : (univ.filter fun j => rightImg (scD c w) (c * xR j) (c ^ 2 * t) = scD c w (c ^ 2 * t)) =
      univ.filter fun j => rightImg w (xR j) t = w t := by
    refine Finset.filter_congr fun j _ => ?_
    rw [hR j, hD]
    exact ⟨fun h => mul_left_cancel₀ hc0 h, fun h => by rw [h]⟩
  rw [hsetL, hsetR]

open QuantumZipper (fwdMapInv) in
/-- **Off the bad set there is no continuation threshold** (deterministic): if the Loewner trace of `U` at `t > 0` is
not a bad point of the word, the force-point state of `U` at `t` (in the form of `OpenLinesS.noThreshold`) has no
continuation threshold. -/
theorem not_threshold_of_notMem_badSet {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {t : ℝ} (ht : 0 < t)
    {η : ℝ → ℂ} (hη : IsLoewnerTraceLT U t η) (hc : ContinuousOn η (Icc 0 t))
    {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hoff : η t ∉ SB.Vr.badSet xL xR ρL ρR) :
    ¬ ForceWord.ThresholdCondition ρL ρR (U t) (fun i => -rightImg (fun v => -U v) (-xL i) t)
      (fun j => rightImg U (xR j) t) := by
  classical
  intro hthr
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 ht hc
  have htip := TraceClose.extendFrom_zero_eq hη hU hU0 ht hc
  have hη' := SB.Vo.isLoewnerTraceLT_reflect hη
  have hc' : ContinuousOn (fun s => LP.reflectC (η s)) (Icc 0 t) := LP.continuous_reflectC.comp_continuousOn hc
  have hU0' : (-U) 0 = 0 := by simp [hU0]
  have hB' := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη' hU.neg hU0' ht hc'
  have htip' := TraceClose.extendFrom_zero_eq hη' hU.neg hU0' ht hc'
  rcases GW2Sdn.threshold_real_tip hU hU0 ht.le hB htip hB' htip' hxL hxR hthr with
    ⟨him, hre, hsum⟩ | ⟨him, hre, hsum⟩
  · -- a left threshold: the reflected tip is `−conj (η t)`
    have him' : (η t).im = 0 := by simpa [LP.reflectC] using him
    have hre' : (η t).re ≤ 0 := by
      have : 0 ≤ -(η t).re := by simpa [LP.reflectC] using hre
      linarith
    have hset : univ.filter (fun i => -xL i ≤ (LP.reflectC (η t)).re) =
        univ.filter (fun i => (η t).re ≤ xL i) :=
      Finset.filter_congr fun i _ => by simp only [LP.reflectC, Complex.neg_re, Complex.conj_re, neg_le_neg_iff]
    rw [hset] at hsum
    exact hoff ⟨him', Or.inr ⟨hre', hsum⟩⟩
  · exact hoff ⟨him, Or.inl ⟨hre, hsum⟩⟩

end InteractingSLE.Theorem14.GW2Sdo
