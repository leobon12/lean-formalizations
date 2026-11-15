/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaAmbient

/-! # GW4: the ambient access and side at a surviving exposed reference -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse Sec7.PocketStopSide MartChar.RealFlow

/-- A surviving old exposed coordinate has a nonzero ambient exposed
coordinate with the same side as the current coordinate. Both approaches
have that same ambient limit. No physical H-landing premise is needed. -/
theorem Frame.ambient_access_of_seed_reference {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {s t v q : ℝ≥0} (hsEnt : F.ent w ≤ s) (hsExit : (s : ℝ≥0∞) < F.exit w)
    (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hv : 0 < v) (hvq : v ≤ q) (hqV : (q : ℝ≥0∞) < V)
    (hvs : (v : ℝ) = F.rcap w s) (hqt : (q : ℝ) = F.rcap w t)
    {ξ x : ℝ}
    (hξ : ξ ∈ Ioo (-rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
      (rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q))
    (hx : x ∈ Ioo (-rightImg (fun r : ℝ => -R r.toNNReal) 0 v - R v)
      (rightImg (fun r : ℝ => R r.toNNReal) 0 v - R v))
    {ε : ℝ} (hε : 0 < ε)
    (hcol : (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) v).2.1 ''
      (H ∩ Metric.ball (x : ℂ) ε) ⊆
      ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).dom : Set ℂ))
    (hTr : Tendsto (fun z => (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) v).1
      ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)))
    {p : ℂ} (hland : Tendsto (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1
      (𝓝[H] (ξ : ℂ)) (𝓝 p)) (hpTip : p ≠ trc w s) :
    ∃ x' : ℝ, x' ≠ 0 ∧
      x' ∈ Ioo (-rightImg (fun r : ℝ => -w r.toNNReal) 0 s - w s)
        (rightImg (fun r : ℝ => w r.toNNReal) 0 s - w s) ∧
      Tendsto (fun z => fwdMap (fun r : ℝ => w r.toNNReal) s
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) v).2.1 z))
        (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun z => fwdMap (fun r : ℝ => w r.toNNReal) s
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧ (ξ < 0 ↔ x' < 0) := by
  have hvV : (v : ℝ≥0∞) < V := (ENNReal.coe_le_coe.2 hvq).trans_lt hqV
  have hq : 0 < q := hv.trans_le hvq
  have hCo := Frame.isOpen_C hF hw
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hBase := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun r : ℝ => R r.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun r : ℝ => R r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hWW : Continuous (fun r : ℝ => w r.toNNReal) := hw.1.comp continuous_real_toNNReal
  have hWW0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw.2.1
  have hη := isLoewnerTrace_of_isGeneratingTrace hw.2.2.1
  have hc := hBase.loewner hRR hRR0 q.coe_nonneg
  have ho := hBase.loewner hRR hRR0 v.coe_nonneg
  have hdom := own_stage_dom_antitone hBase hRR hRR0 v.coe_nonneg (NNReal.coe_le_coe.2 hvq)
  have hTrH := tendsto_nhdsWithin_iff.2 ⟨hTr, eventually_nhdsWithin_of_forall fun y hy =>
    ho.fwd_mem (hdom (hc.inv_mem_dom hy))⟩
  obtain ⟨s₀, hs₀⟩ := hVer v hvV
  obtain ⟨Fo, hFo, hFoc, -⟩ := Frame.exists_physical_stage_inverse_extension hF hw hRR hRR0 hs₀
  have hLo := (Sec7.R5Lift.tendsto_of_ext hFo hFoc x).1
  have hLoC := (hLo.comp hTrH).congr' (eventually_nhdsWithin_of_forall fun y hy =>
    ho.inv_fwd (hdom (hc.inv_mem_dom hy)))
  have := Sec7.R5Lift.nhdsWithin_H_neBot ξ
  have hpEq : Fo x = p := tendsto_nhds_unique hLoC hland
  rw [hpEq] at hLo
  have hpN := Frame.current_seed_landing_notMem hF hw hR hR0 hVer hsEnt hsExit hv hvV hvs hFo hFoc hx
  rw [hpEq] at hpN
  have hDom : ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) v).dom : Set ℂ) ⊆
      H \ fwdHull (fun r : ℝ => w r.toNNReal) s := by
    rw [componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0
      (Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 hs₀ hsEnt hsExit hvs)]
    exact inter_subset_right
  obtain ⟨x', hx'p, hx'⟩ := exists_ambient_access_of_notMem hη hWW hWW0 s.coe_nonneg ho hDom hLo hpN
  have hx'0 : x' ≠ 0 := by
    intro he
    rw [he, Complex.ofReal_zero, ZhanGT4.extendFrom_zero_eq hη hWW hWW0 s.coe_nonneg] at hx'p
    exact hpTip (by simpa only [Real.toNNReal_coe] using hx'p.symm)
  have hx'cur : Tendsto (fun z => fwdMap (fun r : ℝ => w r.toNNReal) s
      ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) :=
    (hx'.comp hTrH).congr' (eventually_nhdsWithin_of_forall fun y hy =>
      congrArg (fwdMap (fun r : ℝ => w r.toNNReal) s)
        (ho.inv_fwd (hdom (hc.inv_mem_dom hy))))
  obtain ⟨n, hn⟩ := Frame.exists_common_reference_phase hF hw hR hR0 hVer htEnt htExit hq hqV hqt
  exact ⟨x', hx'0,
    Frame.current_transition_seed_interval hF hw hR hR0 hVer hsEnt hsExit hv hvV hvs x hx x' hx',
    hx', hx'cur, (hn s v hsEnt hsExit hv hvq hvs ξ hξ x hx ε hε hcol x' hx'0 hx'cur hx').2⟩

end InteractingSLE.Theorem14.GW4Fix
