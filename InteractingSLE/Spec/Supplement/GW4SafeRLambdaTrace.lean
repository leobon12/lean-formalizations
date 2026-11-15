/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaLanding
import InteractingSLE.Spec.Supplement.RLCG8DetRealCollar

/-! # GW4: every exposed finite landing is on the physical trace -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse Sec7.PocketStopSide

/-- Exposed GW4 accesses land on the ambient closed hull, including when
the landing lies on the original real line. -/
theorem Frame.current_seed_landing_mem_closure_hull {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {t q : ℝ≥0} (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hq : 0 < q) (hqV : (q : ℝ≥0∞) < V) (hqt : (q : ℝ) = F.rcap w t)
    {ξ : ℝ} (hξ : ξ ∈ Ioo
      (-MartChar.RealFlow.rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
      (MartChar.RealFlow.rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q))
    {p : ℂ} (hland : Tendsto (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1
      (𝓝[H] (ξ : ℂ)) (𝓝 p)) : p ∈ closure (fwdHull (fun r : ℝ => w r.toNNReal) t) := by
  have hCo := Frame.isOpen_C hF hw
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hBase := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun r : ℝ => R r.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun r : ℝ => R r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  obtain ⟨s, hs⟩ := hVer q hqV
  obtain ⟨E, hE, hEc, -⟩ := Frame.exists_physical_inverse_extension hF hw
  obtain ⟨Fb, hFb, hFbc⟩ := Frame.exists_inverse_extension_of_hullAt hF hw hRR hRR0 hs
  apply landing_mem_closure_hull_of_seed hBase hRR hRR0 (NNReal.coe_pos.2 hq) hE hEc hFb hFbc
    (ξ := ξ) (p := p) _ (by simpa only [Real.toNNReal_coe] using hξ) hland
  rw [component_base_domain hF.2.2.2.1 hCo hCH]
  exact componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0
    (Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 hs htEnt htExit hqt)

/-- A landing adherent to both the closed hull and its upper complement
lies on the compact generating trace. The real case uses the existing
upper-half-ball dichotomy and does not discard real contacts. -/
theorem Frame.mem_trace_of_common_hull_closures {F : Frame} {w : ℝ≥0 → ℝ}
    (hw : F.IsPathOk w) {t : ℝ≥0} {p : ℂ}
    (hpK : p ∈ closure (fwdHull (fun r : ℝ => w r.toNNReal) t))
    (hpD : p ∈ closure (H \ fwdHull (fun r : ℝ => w r.toNNReal) t)) :
    p ∈ trc w '' Icc 0 t := by
  have hS : IsCompact (trc w '' Icc 0 t) := isCompact_Icc.image (Frame.continuous_trc hw)
  have hfill := Sec5.CrossRestart.fwdHull_eq_fillH_of_isFilling hS (hw.2.2.1.2.2 t ENNReal.coe_lt_top)
  rw [hfill] at hpK hpD
  have hpbar : p ∈ closure H := closure_mono sdiff_subset hpD
  rw [show closure H = QuantumZipper.Hbar from Complex.closure_setOfPred_lt_im 0] at hpbar
  by_cases hpH : p ∈ H
  · have hpFill : p ∈ fillH (trc w '' Icc 0 t) := by
      by_contra hn
      have hO := isOpen_H_diff_fillH hS.isBounded
      obtain ⟨z, hzD, hzK⟩ := mem_closure_iff.1 hpK _ hO ⟨hpH, hn⟩
      exact hzD.2 hzK
    exact Sec7.ReverseArc.mem_of_mem_fillH_of_mem_closure hS.isClosed hpFill hpD
  · have hpim : p.im = 0 := le_antisymm (not_lt.1 hpH) hpbar
    have hpr : p = (p.re : ℂ) := Complex.ext (by simp only [ofReal_re]) (by simp only [ofReal_im, hpim])
    rw [hpr] at hpK hpD ⊢
    exact RLC.G8Det.RealBoundary.mem_trace_of_common_real_closures hS.isClosed sdiff_subset
      disjoint_sdiff_left hpD hpK

end InteractingSLE.Theorem14.GW4Fix
