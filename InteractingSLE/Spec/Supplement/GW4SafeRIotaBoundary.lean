/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaLanding
import InteractingSLE.Spec.Supplement.GW4SafeRIotaTip
import InteractingSLE.Spec.Supplement.GW4SafeRIotaOrientation

/-! # GW4: actual side agreement on every current open seed interval -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse MartChar.RealFlow

/-- The actual GW4 current/ambient transition preserves the sign on the
entire current open seed interval. Wall contacts, original-real contacts,
and an endpoint driver need no extra geometric premise. -/
theorem Frame.current_transition_side {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {t q : ℝ≥0} (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hq : 0 < q) (hqV : (q : ℝ≥0∞) < V) (hqt : (q : ℝ) = F.rcap w t) :
    ∀ ξ ∈ Ioo
      (-rightImg (fun s : ℝ => -R s.toNNReal) 0 q - R q)
      (rightImg (fun s : ℝ => R s.toNNReal) 0 q - R q), ∀ y : ℝ,
      Tendsto (fun z => fwdMap (fun s : ℝ => w s.toNNReal) t
        ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.1 z))
        (𝓝[H] (ξ : ℂ)) (𝓝 (y : ℂ)) → (ξ < 0 ↔ y < 0) := by
  have hCo := Frame.isOpen_C hF hw
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hRR : Continuous (fun s : ℝ => R s.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun s : ℝ => R s.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hWW : Continuous (fun s : ℝ => w s.toNNReal) := hw.1.comp continuous_real_toNNReal
  have hWW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw.2.1
  obtain ⟨t₀, ht₀⟩ := hVer q hqV
  have hHull := Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 ht₀ htEnt htExit hqt
  have hK : ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).dom : Set ℂ) ⊆
      H \ fwdHull (fun s : ℝ => w s.toNNReal) t := by
    rw [componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0 hHull]
    exact inter_subset_right
  have hcur := ((Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans
    Chart.isConformal_infinitySourceChart).loewner hRR hRR0 q.coe_nonneg
  obtain ⟨E, hE, hEc, -⟩ := Frame.exists_physical_stage_inverse_extension hF hw hRR hRR0 ht₀
  refine side_of_anchored_interval_notMem hcur hE hEc
    (isLoewnerTrace_of_isGeneratingTrace hw.2.2.1) hWW hWW0 t.coe_nonneg hK
    (fun ξ hξ => Frame.current_seed_landing_notMem hF hw hR hR0 hVer htEnt htExit hq hqV hqt hE hEc hξ)
    ?_ ?_ (Frame.tendsto_current_transition_tip hF hw hR hR0 hVer htEnt htExit hqV hqt)
  · have h := le_rightImg hRR.neg 0 q.coe_nonneg
    simp only [Pi.neg_apply, Real.toNNReal_coe] at h
    change -R q ≤ rightImg (fun s : ℝ => -R s.toNNReal) 0 q at h
    linarith
  · have h := le_rightImg hRR 0 q.coe_nonneg
    simpa only [Real.toNNReal_coe, sub_nonneg] using h

end InteractingSLE.Theorem14.GW4Fix
