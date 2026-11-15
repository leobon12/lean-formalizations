/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaSeed
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaTrace

/-! # GW4: ambient seed coordinates at every exposed access -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse Sec7.PocketStopSide MartChar.RealFlow

/-- The actual component's whole exposed interval maps into the ambient
open seed interval. The assertion includes original-real wall contacts. -/
theorem Frame.current_transition_seed_interval {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {t q : ℝ≥0} (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hq : 0 < q) (hqV : (q : ℝ≥0∞) < V) (hqt : (q : ℝ) = F.rcap w t) :
    ∀ ξ ∈ Ioo (-rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
      (rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q), ∀ x' : ℝ,
      Tendsto (fun y => fwdMap (fun r : ℝ => w r.toNNReal) t
        ((componentAmbientChart F.c (fun r : ℝ => R r.toNNReal) q).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) →
      x' ∈ Ioo (-rightImg (fun r : ℝ => -w r.toNNReal) 0 t - w t)
        (rightImg (fun r : ℝ => w r.toNNReal) 0 t - w t) := by
  have hCo := Frame.isOpen_C hF hw
  have hCH := subset_H_of_mem_betweenComponents hF.2.1
  have hBase := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun r : ℝ => R r.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun r : ℝ => R r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hWW : Continuous (fun r : ℝ => w r.toNNReal) := hw.1.comp continuous_real_toNNReal
  have hWW0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw.2.1
  obtain ⟨s, hs⟩ := hVer q hqV
  have hDom := componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0
    (Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 hs htEnt htExit hqt)
  obtain ⟨Fc, hFc, hFcc, -⟩ := Frame.exists_physical_stage_inverse_extension hF hw hRR hRR0 hs
  have h := ambient_seed_interval_of_closed_landings
    (a := -rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
    (b := rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q)
    (hBase.loewner hRR hRR0 q.coe_nonneg)
    hFc hFcc (isLoewnerTrace_of_isGeneratingTrace hw.2.2.1)
    hWW hWW0 t.coe_nonneg (hDom ▸ inter_subset_right)
  have hland : ∀ u ∈ Ioo
      (-rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
      (rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q),
      Fc u ∉ H \ fwdHull (fun r : ℝ => w r.toNNReal) t := by
    intro u hu
    exact Frame.current_seed_landing_notMem hF hw hR hR0 hVer htEnt htExit hq hqV hqt hFc hFcc hu
  have hclosed : ∀ u ∈ Ioo
      (-rightImg (fun r : ℝ => -R r.toNNReal) 0 q - R q)
      (rightImg (fun r : ℝ => R r.toNNReal) 0 q - R q),
      Fc u ∈ closure (fwdHull (fun r : ℝ => w r.toNNReal) t) := by
    intro u hu
    apply Frame.current_seed_landing_mem_closure_hull hF hw hR hR0 hVer htEnt htExit hq hqV hqt hu
    exact ((hFcc u (by show 0 ≤ (u : ℂ).im; simp only [Complex.ofReal_im]; exact le_rfl)).tendsto.mono_left
      (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)).congr'
        (eventually_nhdsWithin_of_forall fun y hy => hFc hy)
  intro ξ hξ x' hx'
  simpa only [Real.toNNReal_coe] using h hland hclosed ξ hξ x' hx'

end InteractingSLE.Theorem14.GW4Fix
