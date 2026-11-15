/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WeOrig
import InteractingSLE.Spec.Supplement.SB2LkDom
import InteractingSLE.Spec.Sec7.R6FdLand
import InteractingSLE.Spec.Supplement.Aux10FullLocal

/-!
# SB2(1)'s second clause: the left record is attained by a real point of a piece

Packet PROVE-T14-SB2WORD (round 2). The left record of the lower walk is the infimum of the points it has swallowed
on the left; a swallowed point lies in the closed hull of the stage, whose leftmost real point is a real point of the
trace (`R6Fd.exists_real_le_of_mem_closure_fillH`), which the chart sends back to a real point of the piece (the
boundary correspondence `bdry_eq_of_chartFree` on the untouched left ray). Hence:

* `RecLBound s`: every point strictly between the left record and `0` has a real point of a recorded piece at or left
  of it;
* **`recLBound_launch`**, `recLBound_moveAlong`, `recLBound_root`.

With it the leftmost real point of the retained prefix is at or left of nothing but the record: `L ≤ recL`
(`le_stRecL_of_recLBound`).

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (IsForwardSol chiC fwdMap fwdMapInv fwdHull H Hbar)

namespace InteractingSLE.Theorem14.GW1W

open Exist Exist.StagedLaw Exist.Staged Restart

/-- **Every point strictly between the left record and `0` has a real point of a recorded piece at or left of it.** -/
def RecLBound (s : ExplState) : Prop :=
  ∀ x, stRecL s < x → x < 0 → ∃ p ∈ s.1, ∃ z ∈ p.1.tipSet p.2.1 p.2.2, z.im = 0 ∧ z.re ≤ x

theorem recLBound_root : RecLBound (ExplState.init 0) := fun x hx hx0 => by
  have : stRecL (ExplState.init 0) = 0 := rfl
  rw [this] at hx
  linarith

theorem recLBound_moveAlong {s : ExplState} (hB : RecLBound s) (w : ℝ) :
    RecLBound (ExplState.moveAlong s true w true) := by
  intro x hx hx0
  rw [stRecL_moveAlong_true'] at hx
  obtain ⟨p, hp, z, hz⟩ := hB x hx hx0
  exact ⟨p, by rw [pieces_moveAlong]; exact hp, z, hz⟩

/-- **The left record bound survives a launch**: a point between the new and the old left record was swallowed by
the new piece, so the trace has a real point at or left of its chart image; that real trace point is the image of a
point of the untouched left ray, which is a real point of the new piece. -/
theorem recLBound_launch {s : ExplState} {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hc : IsRealChart (stChart s)) (hs : LLeft s)
    (hcc : (stChart s).IsConformal) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g (stChart s).2.1 H)
    (hSf : ∀ x, x < stRecL s → ContinuousAt (stChart s).1 (x : ℂ) ∧ ChartFree (stChart s) x)
    (hB : RecLBound s) (k : ℕ) (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) (hP : GW1P.PieceRegular D.1 D.2) :
    RecLBound (ExplState.launch s k D θ ⊤) := by
  obtain ⟨-, -, -, hrecL, -, -⟩ := launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)
  set c := stChart s with hcdef
  have hWe : rdrv (recOf ⊤ D) = stopDrv ⊤ D := by rw [rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  have hV : Continuous (stopDrv ⊤ D) := by rw [← hWe]; exact continuous_rdrv _
  have hV0 : stopDrv ⊤ D 0 = 0 := stopDrv_zero hreg ⊤
  have hTs : 0 ≤ stopTime ⊤ D := stopTime_nonneg ⊤ D
  have hH' := (isRealFlow_stop hreg hgood).2
  intro x hx hx0
  by_cases hxr : stRecL s < x
  · obtain ⟨p, hp, z, hz⟩ := hB x hxr hx0
    exact ⟨p, by rw [CounterflowRange.pieces_launch]; exact List.mem_append_left _ hp, z, hz⟩
  push Not at hxr
  -- a dead point of the old ray left of `x`
  have hR1 : -stRecL (ExplState.launch s k D θ ⊤) = newRec (lProf c) (-stRecL s)
      (fun y : ℝ => ∃ u, IsForwardSol (stopDrv ⊤ D) ((-y : ℝ) : ℂ) (stopTime ⊤ D) u) := by
    rw [hrecL, lRecL_eq_newRec hc, neg_neg]
  have hlt : -x < newRec (lProf c) (-stRecL s)
      (fun y : ℝ => ∃ u, IsForwardSol (stopDrv ⊤ D) ((-y : ℝ) : ℂ) (stopTime ⊤ D) u) := by
    rw [← hR1]; linarith
  obtain ⟨z, hz, hxz⟩ := (lt_csSup_iff (bddAbove_dead hs.1 hH') (insert_nonempty _ _)).1 hlt
  rcases hz with rfl | ⟨hza, hzd⟩
  · linarith
  set x₂ := -z with hx₂
  have hx₂x : x₂ < x := by linarith
  have hx₂r : x₂ < stRecL s := by linarith
  have hv : rProf c x₂ < 0 := hs.neg hx₂r
  have hdead : ¬ ∃ u, IsForwardSol (stopDrv ⊤ D) ((rProf c x₂ : ℝ) : ℂ) (stopTime ⊤ D) u := by
    have e : -lProf c z = rProf c x₂ := by rw [lProf_eq, neg_neg]
    rw [← e]
    exact hzd
  -- the dead point is in the closed hull
  have hcl : ((rProf c x₂ : ℝ) : ℂ) ∈ closure (fwdHull (stopDrv ⊤ D) (stopTime ⊤ D)) := by
    by_contra hn
    exact hdead (Aux10.exists_isForwardSol_of_notMem_closure hV hV0 hTs hv.ne hn)
  -- the hull is the fill of the trace
  obtain ⟨hD0, hDc, α, hα, -⟩ := hP
  set T' : ℝ≥0 := D.2.toNNReal with hT'
  have hT'e : ((T' : ℝ≥0) : ℝ≥0∞) = D.2 := ENNReal.coe_toNNReal hfin
  let w : ℝ≥0 → ℝ := fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal
  have hw : Continuous w := CounterflowRange.continuous_stopped hDc
  have hw0 : w 0 = 0 := by simpa only [w, ENNReal.coe_zero, zero_min, ENNReal.toNNReal_zero] using hD0
  have hαs : IsGeneratingTrace w (T' : ℝ≥0∞) α := by rw [hT'e]; exact CounterflowRange.isGeneratingTrace_stopped hα
  have hhull : fwdHull (stopDrv ⊤ D) (stopTime ⊤ D) = InteractingSLE.fillH (α '' Icc 0 T') := by
    have h := SB.Lk.fwdHull_eq_fillH_horizon hw hw0 hαs
    have e1 : stopDrv ⊤ D = fun s : ℝ => w s.toNNReal := by
      funext r
      simp only [stopDrv_def, w, min_eq_right (le_top : D.2 ≤ ⊤)]
    have e2 : stopTime ⊤ D = (T' : ℝ) := by
      simp only [stopTime, min_eq_right (le_top : D.2 ≤ ⊤), hT']
    rw [e1, e2]
    exact h
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.2 → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hDc.mono fun _ ht => mem_ofPred.2 (le_of_lt ht)) hD0 ht
  have hcpt : IsCompact (α '' Icc 0 T') := by
    refine isCompact_Icc.image_of_continuousOn (hα.2.1.mono fun t ht => ?_)
    change (t : ℝ≥0∞) ≤ D.2
    rw [← hT'e]
    exact ENNReal.coe_le_coe.2 ht.2
  have hsub : α '' Icc 0 T' ⊆ Hbar := by
    rintro _ ⟨t, ht, rfl⟩
    refine hαH t ?_
    rw [← hT'e]
    exact ENNReal.coe_le_coe.2 ht.2
  rw [hhull] at hcl
  obtain ⟨_, ⟨t, ht, rfl⟩, hαt, hαle⟩ := Sec7.R6Fd.exists_real_le_of_mem_closure_fillH hcpt hsub hcl
  have htS : (t : ℝ≥0∞) ≤ D.2 := by rw [← hT'e]; exact ENNReal.coe_le_coe.2 ht.2
  -- the real trace point is the image of a point of the untouched ray
  obtain ⟨x₃, hx₃r, hx₃x, hx₃e⟩ := hs.exists_eq hx₂r hαle
  have hαx : α t = c.1 x₃ := by
    rw [hc.eq_ofReal x₃, hx₃e]
    exact Complex.ext rfl (by simp [hαt])
  obtain ⟨hC₃, hF₃⟩ := hSf x₃ hx₃r
  have hg₃ : g (c.1 x₃) = x₃ := bdry_eq_of_chartFree hcc hgc hgi hC₃ hF₃ (hc x₃)
  -- it is a real point of the new piece
  refine ⟨(c, fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) (min ⊤ D.2)).toNNReal, min ⊤ D.2), ?_, (x₃ : ℂ), ?_, by simp,
    by simp only [Complex.ofReal_re]; linarith⟩
  · rw [CounterflowRange.pieces_launch]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  · refine ⟨t, by rwa [min_eq_right (le_top : D.2 ≤ ⊤)], ?_⟩
    have hV' : (fun r : ℝ => (fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) (min ⊤ D.2)).toNNReal) r.toNNReal) =
        stopDrv ⊤ D := rfl
    rw [hV']
    have htip : Tendsto (fwdMapInv (stopDrv ⊤ D) t) (𝓝[H] 0) (𝓝 (α t)) := by
      simpa only [stopDrv_def, min_eq_right (le_top : D.2 ≤ ⊤)] using
        GW1WalkExit.tendsto_inverse_trace_le (CounterflowRange.isGeneratingTrace_stopped hα) hw hw0 htS
    have hrad : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝[>] 0) (𝓝[H] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
      · have hcm : Continuous fun y : ℝ => (y : ℂ) * Complex.I :=
          Complex.continuous_ofReal.mul continuous_const
        have h := hcm.tendsto 0
        simp only [Complex.ofReal_zero, zero_mul] at h
        exact h.mono_left nhdsWithin_le_nhds
      · show 0 < ((y : ℂ) * Complex.I).im
        simpa using hy
    have hin : Tendsto (fun y : ℝ => fwdMapInv (stopDrv ⊤ D) t ((y : ℂ) * Complex.I)) (𝓝[>] 0)
        (𝓝[{z : ℂ | 0 ≤ z.im}] (α t)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨htip.comp hrad, ?_⟩
      filter_upwards [hrad.eventually (self_mem_nhdsWithin : H ∈ 𝓝[H] (0 : ℂ))] with y hy
      exact (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hV hV0 t.coe_nonneg hy).1.le
    have hgα : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (α t) := hgc (α t) (hαH t htS)
    have h1 := hgα.tendsto.comp hin
    rw [hαx, hg₃] at h1
    refine h1.congr' ?_
    filter_upwards [hrad.eventually (self_mem_nhdsWithin : H ∈ 𝓝[H] (0 : ℂ))] with y hy
    exact hgi (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hV hV0 t.coe_nonneg hy).1

end InteractingSLE.Theorem14.GW1W
