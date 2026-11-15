/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitStatement
import InteractingSLE.Spec.Sec7.SideHeightGeom

/-! # GW1: inverse correspondence on the outward original-real ray -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv IsForwardSol)

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish

/-- The original outward record, in the coordinate increasing towards the target. -/
def outwardRecord (right : Bool) (s : ExplState) : ℝ :=
  if right then stRecR s else -stRecL s

/-- Actual boundary inverse correspondence, restricted to the untouched outward ray. -/
def ExteriorInverse (right : Bool) (s : ExplState) : Prop :=
  ∀ x : ℝ, outwardRecord right s < sideCoord right x →
    Tendsto (stChart s).2.1 (𝓝[H] ((stChart s).1 (x : ℂ))) (𝓝 (x : ℂ))

theorem exteriorInverse_init (right : Bool) (root : ℝ) :
    ExteriorInverse right (ExplState.init root) := by
  intro x _
  have hc : Continuous (fun z : ℂ => z + (root : ℂ)) := continuous_id.add continuous_const
  simpa only [ExplState.init, Chart.id, Chart.recenter, sub_add_cancel] using
    (hc.tendsto ((x : ℂ) - root)).mono_left nhdsWithin_le_nhds

theorem exteriorInverse_moveAlong {right : Bool} {s : ExplState}
    (h : ExteriorInverse right s) (w : ℝ) :
    ExteriorInverse right (ExplState.moveAlong s right w true) := by
  intro x hx
  have hxold : outwardRecord right s < sideCoord right x := by
    cases right
    · have he : stRecL (ExplState.moveAlong s false w true) = min (stRecL s) w := by
        cases s; rfl
      change -stRecL (ExplState.moveAlong s false w true) < -x at hx
      rw [he] at hx
      change -stRecL s < -x
      linarith only [hx, min_le_left (stRecL s) w]
    · change stRecR (ExplState.moveAlong s true w true) < x at hx
      rw [GW1W.stRecR_moveAlong_true] at hx
      exact (le_max_left (stRecR s) w).trans_lt hx
  rw [GW1W.stChart_moveAlong]
  let a := ((stChart s).1 (w : ℂ)).re
  have htc : Continuous (fun z : ℂ => z + (a : ℂ)) := continuous_id.add continuous_const
  have ht : Tendsto (fun z : ℂ => z + (a : ℂ))
      (𝓝[H] (((stChart s).recenter a).1 (x : ℂ)))
      (𝓝[H] ((stChart s).1 (x : ℂ))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [Chart.recenter, sub_add_cancel] using
        (htc.tendsto (((stChart s).recenter a).1 (x : ℂ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      show 0 < (z + (a : ℂ)).im
      simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using (show 0 < z.im from hz)
  exact (h x hxold).comp ht

/-- Whole-half-plane tip limits include a finite horizon, by trace closure. -/
theorem tendsto_inverse_trace_le {w : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace w S α) (hw : Continuous w) (hw0 : w 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ S) :
    Tendsto (fwdMapInv (fun r : ℝ => w r.toNNReal) t) (𝓝[H] 0) (𝓝 (α t)) := by
  have hW : Continuous (fun r : ℝ => w r.toNNReal) := hw.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => w r.toNNReal) 0 = 0 := by simpa only [Real.toNNReal_zero] using hw0
  by_cases ht0 : t = 0
  · subst t
    rw [hα.1]
    have hlim : Tendsto (fun z : ℂ => z) (𝓝[H] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (fwdMapInv_zero_time hW hW0 hz).symm
  have htr := hα.mono_horizon ht
  have hη := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace htr
  have hηc : ContinuousOn (fun r : ℝ => α r.toNNReal) (Icc 0 (t : ℝ)) :=
    htr.2.1.comp continuous_real_toNNReal.continuousOn (fun r hr =>
      ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2))
  simpa only [Real.toNNReal_coe] using TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT
    hη hW hW0 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht0)) hηc

theorem exteriorInverse_launch {right : Bool} {s : ExplState}
    (h : ExteriorInverse right s) (hc : IsRealChart (stChart s))
    (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ)
    (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤)
    (hAlive : ∀ x : ℝ, outwardRecord right (ExplState.launch s k D θ ⊤) < sideCoord right x →
      outwardRecord right s < sideCoord right x ∧ lAlive (stChart s) ⊤ D x) :
    ExteriorInverse right (ExplState.launch s k D θ ⊤) := by
  intro x hx
  obtain ⟨hxold, u, hu⟩ := hAlive x hx
  have hW : Continuous (stopDrv ⊤ D) := by
    simpa only [stopDrv_def, min_eq_right (le_top : D.2 ≤ ⊤)] using hP.continuous_stoppedReal.1
  have hW0 : stopDrv ⊤ D 0 = 0 := by
    simpa only [stopDrv_def, min_eq_right (le_top : D.2 ≤ ⊤)] using hP.continuous_stoppedReal.2
  have hB : HasBdryLimits (fwdMapInv (stopDrv ⊤ D) (stopTime ⊤ D)) := by
    simpa only [stopDrv_def, stopTime, min_eq_right (le_top : D.2 ≤ ⊤)] using hP.hasBdryLimits hfin
  have hch := (launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)).1
  have hT := stopTime_nonneg ⊤ D
  have hp : (stChart s).1 (x : ℂ) ∈ Hbar := by
    show 0 ≤ ((stChart s).1 (x : ℂ)).im
    rw [hc x]
  have hu' : IsForwardSol (stopDrv ⊤ D) ((stChart s).1 (x : ℂ)) (stopTime ⊤ D) u := hu
  have he := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB hW hW0 hT hp hu'
  have hmap : fwdMap (stopDrv ⊤ D) (stopTime ⊤ D) ((stChart s).1 (x : ℂ)) = u (stopTime ⊤ D) :=
    InteractingSLE.fwdMap_eq_of_isForwardSol hW hu' ⟨hT, le_rfl⟩
  have hup : u (stopTime ⊤ D) ∈ Hbar := by
    rw [← hmap, hc.eq_ofReal x]
    show 0 ≤ (fwdMap (stopDrv ⊤ D) (stopTime ⊤ D) (rProf (stChart s) x : ℂ)).im
    rw [im_fwdMap_ofReal _ hT]
  have hlim := hB.tendsto hup
  rw [he, ← hmap] at hlim
  rw [hch]
  exact CounterflowRange.tendsto_loewner_inv (c := stChart s) (f := fun _ => (x : ℂ))
    hW hW0 hT hlim (h x hxold)

end InteractingSLE.Theorem14.GW1WalkExit
