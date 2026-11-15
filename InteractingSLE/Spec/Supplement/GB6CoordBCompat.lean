/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBClock

/-!
# Compatibility of canonical relative prefix drivers

`IsDrivenCurve.segDrv_eq` recovers any fixed-prefix driver from the mapped
curve. Consequently changing the physical prefix endpoint does not change
the driver on the smaller live capacity interval.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.CoordB

open Sec7.PocketTraversal Sec7.Lemma71C

variable {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 < s)
  {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
  {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace w ⊤ γ)

include hU hU0 hs htip hw hw0 hγ in
/-- The canonical relative prefix formula recovers a fixed driver through
any smaller positive physical prefix. -/
theorem localDriver_eq_fixed {T S : ℝ≥0} (hT : 0 < T) (hS : 0 < S) (hST : S < T)
    (hd : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)))
    {V : ℝ → ℝ} (hV : Continuous V) (hV0 : V 0 = 0)
    (hK : ∀ q ∈ Icc (0 : ℝ) S, fwdHull V (relClock U s (Ito.rpath w) q) =
      fillH ((fun r : ℝ => relBdry U s (γ r.toNNReal)) '' Icc 0 q))
    {r : ℝ≥0} (hr : (r : ℝ) ≤ relClock U s (Ito.rpath w) S) :
    drivenDriver (fun _ : Unit => localCurve U s γ T) r () = V r := by
  have hc := isDrivenCurve_localCurve hU hU0 hs htip hw hw0 hγ hT hd
  obtain ⟨u, hu, he⟩ := exists_clockOf_eq hST
  have hup : 0 < u := by
    by_contra hn
    have he0 : u = 0 := le_antisymm (not_lt.1 hn) hu
    rw [he0, clockOf_zero] at he
    exact ne_of_gt (show (0 : ℝ) < S by exact_mod_cast hS) he.symm
  have hlive : (r : ℝ≥0∞) < capLife (localCurve U s γ T) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_le_ofReal hr).trans_lt
      (relClock_lt_localLife hU hU0 hs htip hw hw0 hγ hd hT hST)
  rw [drivenDriver_eq (γ := fun _ : Unit => localCurve U s γ T) (ω := ()) hlive]
  apply hc.segDrv_eq hup hV hV0
  · intro v hv
    rw [capClock_localCurve hU hU0 hs htip hw hw0 hγ hd hT hv.1,
      localCurve, image_relCurve_Icc _ (by exact_mod_cast hT) hv.1]
    apply hK
    refine ⟨clockOf_nonneg (by exact_mod_cast hT) hv.1, ?_⟩
    rw [← he]
    exact (strictMonoOn_clockOf (by exact_mod_cast hT)).monotoneOn hv.1 hu hv.2
  · exact r.coe_nonneg
  · rw [capClock_localCurve hU hU0 hs htip hw hw0 hγ hd hT hu, he]
    exact hr

include hU hU0 hs htip hw hw0 hγ in
/-- Local drivers for nested physical prefixes agree on the smaller live interval. -/
theorem localDriver_eq_of_le {T₁ T₂ : ℝ≥0} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂) (h12 : T₁ ≤ T₂)
    (hd₁ : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T₁)))
    (hd₂ : Disjoint (closure (fwdHull U s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T₂)))
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < capLife (localCurve U s γ T₁)) :
    drivenDriver (fun _ : Unit => localCurve U s γ T₁) r () =
      drivenDriver (fun _ : Unit => localCurve U s γ T₂) r () := by
  have hc := isDrivenCurve_localCurve hU hU0 hs htip hw hw0 hγ hT₁ hd₁
  have hr' : ENNReal.ofReal (r : ℝ) < capLife (localCurve U s γ T₁) := by
    rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨n, hn0, hn⟩ := hc.exists_pos_lt_capClock r.coe_nonneg hr'
  have hq0 : 0 < clockOf T₁ n := by
    have h := strictMonoOn_clockOf (by exact_mod_cast hT₁) (self_mem_Ici)
      (show (0 : ℝ) ≤ n by positivity) hn0
    rwa [clockOf_zero] at h
  let S : ℝ≥0 := ⟨clockOf T₁ n, hq0.le⟩
  have hS : 0 < S := hq0
  have hST₁ : S < T₁ := clockOf_lt (by exact_mod_cast hT₁) (by positivity)
  have hST₂ : S < T₂ := hST₁.trans_le h12
  have hrS : (r : ℝ) ≤ relClock U s (Ito.rpath w) S := by
    rw [capClock_localCurve hU hU0 hs htip hw hw0 hγ hd₁ hT₁ (by positivity)] at hn
    exact hn.le
  obtain ⟨V, hV, hV0, hK⟩ := exists_relBdry_prefix_driver hU hU0 hs htip hw hw0 hγ hd₁
  have hKV : ∀ q ∈ Icc (0 : ℝ) S, fwdHull V (relClock U s (Ito.rpath w) q) =
      fillH ((fun r : ℝ => relBdry U s (γ r.toNNReal)) '' Icc 0 q) := by
    intro q hq
    exact (hK q ⟨hq.1, hq.2.trans (by exact_mod_cast hST₁.le)⟩).2.1
  exact (localDriver_eq_fixed hU hU0 hs htip hw hw0 hγ hT₁ hS hST₁ hd₁ hV hV0 hKV hrS).trans
    (localDriver_eq_fixed hU hU0 hs htip hw hw0 hγ hT₂ hS hST₂ hd₂ hV hV0 hKV hrS).symm

end InteractingSLE.Supp8.GB6.CoordB
