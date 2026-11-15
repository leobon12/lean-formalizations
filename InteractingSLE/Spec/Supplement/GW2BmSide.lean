/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BmTip
import InteractingSLE.Spec.Supplement.GW2SfChart
import InteractingSLE.Spec.Supplement.RLCG8DetRelBoundary
import InteractingSLE.Spec.Sec2.T24BrImage
import InteractingSLE.Foundations.Loewner.Reflect

/-!
# Untouched real points stay strictly between the junctions of the relative chart (D17 (B), the off-condition)

Packet PROVE-GW2-BUF (round 10). In GB6's relative chart `relBdry U s` of a counterflow `(U, s)`, the real line
splits into the left tail `(−∞, junctionL]`, the image of the untouched original-real points, and the right tail
`[junctionR, ∞)`. This file proves the strict middle part that the contact clause needs.

* **`baseR_lt_re_fwdMap`**, **`re_fwdMap_lt_baseL`**: an untouched real point `x > 0` (resp. `x < 0`) has a centred
  image strictly right of `V̂^{0,R}_s` (resp. strictly left of `V̂^{0,L}_s`). Untouched points form an open set, and
  the real flow is strictly increasing.
* **`re_relBdry_lt_junctionR`**, **`junctionL_lt_re_relBdry`**: hence an untouched real point has a chart image
  strictly inside `(junctionL, junctionR)`.
* **`lt_junctionR_of_relBdry_eq`**, **`junctionL_lt_of_relBdry_eq`**: every real chart value of a safe point is
  strictly inside `(junctionL, junctionR)` (when the corresponding base end is nonzero).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdHull fwdMap)

namespace InteractingSLE.Theorem14.GW2Bh

open MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel

/-- An untouched positive real point is alive. -/
theorem alive_of_notMem_closure_fwdHull {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {y : ℝ} (hy : 0 < y) (hyK : (y : ℂ) ∉ closure (fwdHull U s)) : Alive U y s := by
  obtain ⟨v, hv⟩ := RLC.G8Det.alive_of_notMem_closure hU (by rw [hU0]; exact hy.ne') hs hyK
  exact Sec7.Lemma76E.alive_of_isForwardSol hU hs (by rw [hU0]; exact hy) hv

/-- **An untouched positive real point has a centred image strictly right of the right base end.** -/
theorem baseR_lt_re_fwdMap {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    (hx : 0 < x) (hxK : (x : ℂ) ∉ closure (fwdHull U s)) : baseR U s < (fwdMap U s x).re := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hxK
  set x' : ℝ := max (x - δ / 2) (x / 2) with hx'def
  have hx'pos : 0 < x' := lt_max_of_lt_right (half_pos hx)
  have hx'x : x' < x := max_lt (by linarith) (by linarith)
  have hx'K : (x' : ℂ) ∉ closure (fwdHull U s) := by
    apply hball
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    have : x - δ / 2 ≤ x' := le_max_left _ _
    linarith
  have hA := alive_of_notMem_closure_fwdHull hU hU0 hs hx hxK
  have hA' := alive_of_notMem_closure_fwdHull hU hU0 hs hx'pos hx'K
  have h1 := rightImg_le_gImg hU hs hx'pos hA'
  have h2 := Restart.FCAux79.gImg_lt_gImg hU hs hA' hx'x
  rw [Sec2.T24Bridge.re_fwdMap_eq_cflow hU hs hA]
  unfold baseR
  simp only [gImg] at h1 h2
  linarith

/-- **An untouched negative real point has a centred image strictly left of the left base end** (by reflection). -/
theorem re_fwdMap_lt_baseL {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    (hx : x < 0) (hxK : (x : ℂ) ∉ closure (fwdHull U s)) : (fwdMap U s x).re < baseL U s := by
  have hV : Continuous (-U) := hU.neg
  have hV0 : (-U) 0 = 0 := by simp [hU0]
  have hrx : LP.reflectC (x : ℂ) = ((-x : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [LP.reflectC]
  have hxK' : ((-x : ℝ) : ℂ) ∉ closure (fwdHull (-U) s) := by
    rw [LP.fwdHull_neg, ← hrx, ← LP.coe_reflectHomeo, ← LP.reflectHomeo.image_closure]
    rintro ⟨w, hw, hwx⟩
    exact hxK (LP.reflectHomeo.injective hwx ▸ hw)
  have h := baseR_lt_re_fwdMap hV hV0 hs (neg_pos.2 hx) hxK'
  rw [← hrx, LP.fwdMap_neg U hs] at h
  have e1 : (LP.reflectC (fwdMap U s x)).re = -(fwdMap U s x).re := by simp [LP.reflectC]
  have e2 : baseR (-U) s = -baseL U s := by
    have hfun : (fun r => -U r) = -U := rfl
    unfold baseR baseL
    rw [hfun]
    simp only [Pi.neg_apply]
    ring
  rw [e1, e2] at h
  linarith

/-- **An untouched positive real point has a relative chart image strictly left of the right junction.** -/
theorem re_relBdry_lt_junctionR {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {y : ℝ}
    (hy : 0 < y) (hyA : (y : ℂ) ∉ closure (invHull U s)) (hbL : baseL U s < 0) :
    (relBdry U s y).re < junctionR U s := by
  rw [GW2Sf.relBdry_of_real hU hU0 hs hy.ne' hyA, ofReal_re]
  have hm := re_fwdMap_lt_baseL hU hU0 hs (neg_lt_zero.2 (inv_pos.2 hy)) (negInv_notMem_closure hy.ne' hyA)
  set m := (fwdMap U s ((-y⁻¹ : ℝ) : ℂ)).re with hmdef
  have hm0 : m < 0 := hm.trans hbL
  unfold junctionR
  have := (inv_lt_inv_of_neg hbL hm0).2 hm
  linarith

/-- **An untouched negative real point has a relative chart image strictly right of the left junction.** -/
theorem junctionL_lt_re_relBdry {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {y : ℝ}
    (hy : y < 0) (hyA : (y : ℂ) ∉ closure (invHull U s)) (hbR : 0 < baseR U s) :
    junctionL U s < (relBdry U s y).re := by
  rw [GW2Sf.relBdry_of_real hU hU0 hs hy.ne hyA, ofReal_re]
  have hm := baseR_lt_re_fwdMap hU hU0 hs (neg_pos.2 (inv_lt_zero.2 hy)) (negInv_notMem_closure hy.ne hyA)
  set m := (fwdMap U s ((-y⁻¹ : ℝ) : ℂ)).re with hmdef
  have hm0 : 0 < m := hbR.trans hm
  unfold junctionL
  have := (inv_lt_inv₀ hm0 hbR).2 hm
  linarith

/-- A safe point with a real chart value is a real point. -/
theorem eq_re_of_relBdry_eq_real {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ relSafe U s) {r : ℝ} (hr : relBdry U s z = r) : z = (z.re : ℂ) := by
  have hzH : z ∉ H := fun h => by
    have h1 := (relBdry_mem_H_iff hU hU0 hs hz).2 h
    rw [hr] at h1
    have h2 : (0 : ℝ) < ((r : ℂ)).im := h1
    rw [ofReal_im] at h2
    exact lt_irrefl _ h2
  have him : z.im = 0 := le_antisymm (not_lt.1 hzH) hz.1
  exact Complex.ext rfl (by simp [him])

/-- **Every real chart value of a safe point lies strictly left of the right junction** (when `V̂^{0,L}_s < 0`). -/
theorem lt_junctionR_of_relBdry_eq {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ relSafe U s) {r : ℝ} (hr : relBdry U s z = r) (hbL : baseL U s < 0) : r < junctionR U s := by
  have hjR : 0 < junctionR U s := by unfold junctionR; exact neg_pos.2 (inv_lt_zero.2 hbL)
  have hze := eq_re_of_relBdry_eq_real hU hU0 hs hz hr
  have hyA : ((z.re : ℝ) : ℂ) ∉ closure (invHull U s) := hze ▸ hz.2
  have hre : (relBdry U s (z.re : ℂ)).re = r := by rw [← hze, hr, ofReal_re]
  rcases lt_trichotomy z.re 0 with hn | h0 | hp
  · have := ((GW2Sf.relBdry_real_sign hU hU0 hs hn.ne hyA).2).1 hn
    linarith
  · rw [h0, ofReal_zero, relBdry_zero hU hU0 hs, zero_re] at hre
    linarith
  · have := re_relBdry_lt_junctionR hU hU0 hs hp hyA hbL
    linarith

/-- **Every real chart value of a safe point lies strictly right of the left junction** (when `V̂^{0,R}_s > 0`). -/
theorem junctionL_lt_of_relBdry_eq {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ relSafe U s) {r : ℝ} (hr : relBdry U s z = r) (hbR : 0 < baseR U s) : junctionL U s < r := by
  have hjL : junctionL U s < 0 := by unfold junctionL; exact neg_lt_zero.2 (inv_pos.2 hbR)
  have hze := eq_re_of_relBdry_eq_real hU hU0 hs hz hr
  have hyA : ((z.re : ℝ) : ℂ) ∉ closure (invHull U s) := hze ▸ hz.2
  have hre : (relBdry U s (z.re : ℂ)).re = r := by rw [← hze, hr, ofReal_re]
  rcases lt_trichotomy z.re 0 with hn | h0 | hp
  · have := junctionL_lt_re_relBdry hU hU0 hs hn hyA hbR
    linarith
  · rw [h0, ofReal_zero, relBdry_zero hU hU0 hs, zero_re] at hre
    linarith
  · have := ((GW2Sf.relBdry_real_sign hU hU0 hs hp.ne' hyA).1).1 hp
    linarith

end InteractingSLE.Theorem14.GW2Bh
