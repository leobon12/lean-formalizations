/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaCompare
import InteractingSLE.Spec.Supplement.GW4SafeRKappaChart

/-! # GW4: phase comparison in the actual physical component -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse Sec7.PocketStopSide Sec7.R5Lift MartChar.RealFlow

/-- The two actual physical phase integers agree across a surviving seed
collar. The old access is allowed to map to the ambient tip. -/
theorem Frame.phase_int_eq_of_seed_collar {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {s t p q : ℝ≥0} (hsEnt : F.ent w ≤ s) (htEnt : F.ent w ≤ t)
    (htExit : (t : ℝ≥0∞) < F.exit w) (hst : s ≤ t) (hp : 0 < p) (hpq : p ≤ q)
    (hqV : (q : ℝ≥0∞) < V) (hps : (p : ℝ) = F.rcap w s) (hqt : (q : ℝ) = F.rcap w t)
    {x ξ ε : ℝ} (hx : x ∈ Ioo
      (-rightImg (fun r : ℝ => -R r.toNNReal) 0 p - R p)
      (rightImg (fun r : ℝ => R r.toNNReal) 0 p - R p))
    (hε : 0 < ε)
    (hcol : (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).2.1 ''
      (H ∩ ball (x : ℂ) ε) ⊆ ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).dom : Set ℂ))
    (htr : Tendsto (fun y => (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).1
      ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)))
    (hlift : Tendsto (fun y =>
      (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.2
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y) -
      (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).2.2
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y))
      (𝓝[H] (ξ : ℂ)) (𝓝 0)) {m n : ℤ}
    (hm : Tendsto (fun y =>
      (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).2.2
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).2.1 y) -
      (logDerivFwd (fun r : ℝ => w r.toNNReal) s
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) p).2.1 y)).im)
      (𝓝[H] (x : ℂ)) (𝓝 (2 * Real.pi * m)))
    (hn : Tendsto (fun y =>
      (componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.2
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y) -
      (logDerivFwd (fun r : ℝ => w r.toNNReal) t
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y)).im)
      (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n))) : m = n := by
  have hsExit := (ENNReal.coe_le_coe.2 hst).trans_lt htExit
  have hpV := (ENNReal.coe_le_coe.2 hpq).trans_lt hqV
  have hCo := Frame.isOpen_C hF hw
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hBase := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun r : ℝ => R r.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun r : ℝ => R r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
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
  obtain ⟨Fo, hFo, hFoc, -⟩ := Frame.exists_physical_stage_inverse_extension hF hw hRR hRR0 hs₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isOpen_Ioo x hx
  exact phase_int_eq_of_collar (hBase.loewner hRR hRR0 q.coe_nonneg)
    (hBase.loewner hRR hRR0 p.coe_nonneg) hFo hFoc
    (isLoewnerTrace_of_isGeneratingTrace hw.2.2.1) (hw.1.comp continuous_real_toNNReal)
    (by simpa only [Real.toNNReal_zero] using hw.2.1) s.coe_nonneg (NNReal.coe_le_coe.2 hst)
    hKT hKS (own_stage_dom_antitone hBase hRR hRR0 p.coe_nonneg (NNReal.coe_le_coe.2 hpq))
    hε hρ hcol (fun v hv => Frame.current_seed_landing_notMem hF hw hR hR0 hVer
      hsEnt hsExit hp hpV hps hFo hFoc (hball (mem_ball_of_ofReal_mem_ball hv))) htr hlift hm hn

end InteractingSLE.Theorem14.GW4Fix
