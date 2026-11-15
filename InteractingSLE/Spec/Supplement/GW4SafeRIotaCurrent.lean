/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRIotaCharts
import InteractingSLE.Spec.Supplement.GW4SafeRIotaReflect

/-! # GW4: one actual current integer on the entire open seed interval -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap logDerivFwd)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Rel Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal
open Sec7.Lemma71C Sec7.R5Lift Sec7.R5Same MartChar.RealFlow

/-- At every positive live component capacity, the actual physical
current chart and the ambient chart have one common winding integer on
the entire open seed interval. This includes landings on the walls and
on the original real line, and assumes no directed reference family. -/
theorem Frame.exists_current_phase_int {F : Frame} (hF : F.IsOk)
    {w R : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hR : Continuous R) (hR0 : R 0 = 0)
    {V : ℝ≥0∞} (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V →
      ∃ t, fwdHull (fun r : ℝ => R r.toNNReal) q = F.hullAt w t)
    {t q : ℝ≥0} (htEnt : F.ent w ≤ t) (htExit : (t : ℝ≥0∞) < F.exit w)
    (hq : 0 < q) (hqV : (q : ℝ≥0∞) < V) (hqt : (q : ℝ) = F.rcap w t) :
    ∃ n : ℤ, ∀ ξ ∈ Ioo
        (-rightImg (fun s : ℝ => -R s.toNNReal) 0 q - R q)
        (rightImg (fun s : ℝ => R s.toNNReal) 0 q - R q),
      Tendsto (fun y =>
        (componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.2
          ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.1 y) -
        (logDerivFwd (fun s : ℝ => w s.toNNReal) t
          ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).2.1 y)).im)
        (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  obtain ⟨T, hLoc, hqLife⟩ := Frame.exists_local_curve_at hF hw htEnt htExit
  rw [← hqt, ENNReal.ofReal_coe_nnreal] at hqLife
  let base := (infinitySourceChart.trans F.c).trans infinitySourceChart
  let γ : Unit → ℝ → ℂ := fun _ => F.curve w T
  let c : Unit → Chart := fun _ => base
  have hγ : IsDrivenCurve (γ ()) := Frame.isDrivenCurve_curve hF hLoc
  have hCo := Frame.isOpen_C hF hw
  have hCH := GW4Traverse.subset_H_of_mem_betweenComponents hF.2.1
  have hc : base.IsConformal := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans Chart.isConformal_infinitySourceChart
  have hRR : Continuous (fun s : ℝ => R s.toNNReal) := hR.comp continuous_real_toNNReal
  have hRR0 : (fun s : ℝ => R s.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hR0
  have hrel := Frame.relChart_eq_componentAmbientChart hF hLoc hR hR0 hVer hqLife hqV
  obtain ⟨t₀, ht₀⟩ := hVer q hqV
  have hHull := Frame.fwdHull_eq_hullAt_of_version hF hw hRR hRR0 ht₀ htEnt htExit hqt
  have hDom : ((relChart c γ q ()).dom : Set ℂ) =
      relDom F.C ∩ (H \ fwdHull (fun s : ℝ => w s.toNNReal) t) := by
    rw [show relChart c γ q () = componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q from hrel]
    exact componentAmbientChart_domain_of_hull hF.2.2.2.1 hCo hCH hRR hRR0 hHull
  have hCur := hc.loewner hRR hRR0 q.coe_nonneg
  obtain ⟨Fc, hFc, hFcc, -⟩ := Frame.exists_physical_stage_inverse_extension hF hw hRR hRR0 ht₀
  obtain ⟨E, hE, hEc, -⟩ := Frame.exists_physical_inverse_extension hF hw
  obtain ⟨Lg, hLg, hLift⟩ := exists_derivLog_componentAmbientChart hF.2.2.2.1 hCo hCH hRR hRR0 q.coe_nonneg
  have hW : Continuous (fun s : ℝ => w s.toNNReal) := hw.1.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw.2.1
  have hTrace := isLoewnerTrace_of_isGeneratingTrace hw.2.2.1
  let x : Unit → Fin 1 → ℝ := fun _ _ => 0
  have hLand : ∀ ξ ∈ Ioo
      (geomLW (fun (s : ℝ≥0) (_ : Unit) => segDriver (γ ()) s) x 0 q () - segDriver (γ ()) q)
      (geomRW (fun (s : ℝ≥0) (_ : Unit) => segDriver (γ ()) s) x 0 q () - segDriver (γ ()) q),
      Fc ξ ∉ H \ fwdHull (fun s : ℝ => w s.toNNReal) t := by
    intro ξ hξ hp
    have hLanding := (tendsto_of_ext hFc hFcc ξ).1
    have hLanding' : Tendsto (relChart c γ q ()).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (Fc ξ)) := by
      rw [show relChart c γ q () = componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q from hrel]
      exact hLanding
    have hK := landing_mem_hull_of_mem_seed_interval (iL := 0) (iR := 0)
      (show x () 0 = 0 from rfl) (show x () 0 = 0 from rfl) hc hγ hqLife hq hE hEc
      (component_base_domain hF.2.2.2.1 hCo hCH) (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW t.coe_nonneg)
      hDom hξ hLanding' hp.1
    exact hp.2 hK
  have hK : ((componentAmbientChart F.c (fun s : ℝ => R s.toNNReal) q).dom : Set ℂ) ⊆
      H \ fwdHull (fun s : ℝ => w s.toNNReal) t := by
    rw [← hrel]
    exact hDom ▸ inter_subset_right
  obtain ⟨n, hn⟩ := exists_int_forall_tendsto_cur_notMem hCur hLg hLift hFc hFcc hTrace hW hW0
    t.coe_nonneg hK hLand
  have hDrivers : EqOn (fun r : ℝ => segDriver (γ ()) r.toNNReal)
      (fun r : ℝ => R r.toNNReal) (Icc 0 (q : ℝ)) := by
    intro r hr
    exact (Frame.eq_segDrv_of_version hF hLoc hR hR0 hVer
      ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans_lt hqLife)
      ((ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans hqV.le)).symm
  obtain ⟨hLeq, hReq⟩ := geom_positions_eq_of_driver_eqOn (fun (s : ℝ≥0) (_ : Unit) => segDriver (γ ()) s)
    x x hRR hDrivers
  have hL := congrFun hLeq 0
  have hR' := congrFun hReq 0
  simp only [x, neg_zero] at hL hR'
  refine ⟨n, fun ξ hξ => hn ξ ?_⟩
  rw [hL, hR']
  simpa only [Real.toNNReal_coe] using hξ

end InteractingSLE.Theorem14.GW4Fix
