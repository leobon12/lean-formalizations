/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaBoundary
import InteractingSLE.Spec.Supplement.GW4SafeRIotaReference

/-! # GW4: one integer for all references to a current component chart -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse Sec7.PocketStopSide Sec7.R5Lift MartChar.RealFlow

/-- One actual current integer works for every earlier own reference at its
surviving collar. The reference's ambient physical time may lie on either
side of the current physical time; no directed family is assumed. -/
theorem Frame.exists_common_reference_phase {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {t q : ℝ≥0} (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hq : 0 < q) (hqV : (q : ℝ≥0∞) < V) (hqt : (q : ℝ) = F.rcap w t) :
    ∃ n : ℤ, ∀ (s p : ℝ≥0), F.ent w ≤ s → (s : ℝ≥0∞) < F.exit w →
      0 < p → p ≤ q → (p : ℝ) = F.rcap w s →
      ∀ ξ ∈ Ioo (-rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
        (rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q),
      ∀ x ∈ Ioo (-rightImg (fun r : ℝ => -R r.toNNReal) 0 p - R p)
        (rightImg (fun r : ℝ => R r.toNNReal) 0 p - R p),
      ∀ ε : ℝ, 0 < ε →
        (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆
          ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).dom : Set ℂ) →
      ∀ x' : ℝ, x' ≠ 0 →
        Tendsto (fun y => fwdMap (fun r : ℝ => w r.toNNReal) s
          ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y))
          (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) →
        Tendsto (fun y => fwdMap (fun r : ℝ => w r.toNNReal) s
          ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).2.1 y))
          (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) →
        Tendsto (fun y =>
          (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.2
            ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y) -
          (logDerivFwd (fun r : ℝ => w r.toNNReal) s
            ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y)).im)
          (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) ∧ (ξ < 0 ↔ x' < 0) := by
  obtain ⟨n, hn⟩ := Frame.exists_current_phase_int hF hw hR hR0 hVer htEnt htExit hq hqV hqt
  refine ⟨n, fun s p hsEnt hsExit hp hpq hps ξ hξ x hx ε hε hcol x' hx' hfx hfo => ?_⟩
  have hpV : (p : ℝ≥0∞) < V := (ENNReal.coe_le_coe.2 hpq).trans_lt hqV
  have hCo := Frame.isOpen_C hF hw
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hBase := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun r : ℝ => R r.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun r : ℝ => R r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hWW : Continuous (fun r : ℝ => w r.toNNReal) := hw.1.comp continuous_real_toNNReal
  have hWW0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw.2.1
  obtain ⟨t₀, ht₀⟩ := hVer q hqV
  obtain ⟨s₀, hs₀⟩ := hVer p hpV
  have hKT : ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).dom : Set ℂ) ⊆
      H \ fwdHull (fun r : ℝ => w r.toNNReal) t := by
    rw [componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0
      (Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 ht₀ htEnt htExit hqt)]
    exact inter_subset_right
  have hKS : ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).dom : Set ℂ) ⊆
      H \ fwdHull (fun r : ℝ => w r.toNNReal) s := by
    rw [componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0
      (Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 hs₀ hsEnt hsExit hps)]
    exact inter_subset_right
  obtain ⟨Fc, hFc, hFcc, -⟩ := Frame.exists_physical_stage_inverse_extension hF hw hRR hRR0 ht₀
  obtain ⟨Fo, hFo, hFoc, -⟩ := Frame.exists_physical_stage_inverse_extension hF hw hRR hRR0 hs₀
  obtain ⟨ρT, hρT, hballT⟩ := Metric.isOpen_iff.1 isOpen_Ioo ξ hξ
  obtain ⟨ρS, hρS, hballS⟩ := Metric.isOpen_iff.1 isOpen_Ioo x hx
  exact ref_lift_side_of_cur_notMem (hBase.loewner hRR hRR0 q.coe_nonneg)
    (hBase.loewner hRR hRR0 p.coe_nonneg) hFc hFcc hFo hFoc
    (isLoewnerTrace_of_isGeneratingTrace hw.2.2.1) hWW hWW0 s.coe_nonneg t.coe_nonneg hKT hKS
    (own_stage_dom_antitone hBase hRR hRR0 p.coe_nonneg (NNReal.coe_le_coe.2 hpq)) hε hcol
    ⟨ρT, hρT, fun v hv => Frame.current_seed_landing_notMem hF hw hR hR0 hVer htEnt htExit hq hqV hqt
      hFc hFcc (hballT (mem_ball_of_ofReal_mem_ball hv))⟩
    ⟨ρS, hρS, fun v hv => Frame.current_seed_landing_notMem hF hw hR hR0 hVer hsEnt hsExit hp hpV hps
      hFo hFoc (hballS (mem_ball_of_ofReal_mem_ball hv))⟩
    hx' hfx hfo (hn ξ hξ)
    (Frame.current_transition_side hF hw hR hR0 hVer htEnt htExit hq hqV hqt ξ hξ)

end InteractingSLE.Theorem14.GW4Fix
