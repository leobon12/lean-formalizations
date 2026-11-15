/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitInverse
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-! # GW1: actual real contacts are bounded by the recorded outward extremum -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv IsForwardSol)

namespace InteractingSLE.Theorem14.GW1WalkExit

open Exist Exist.Staged Exist.StagedLaw GW1WalkFinish GW1WalkChain GW1Bookkeep

def OwnProfile (right : Bool) (s : ExplState) : Prop :=
  if right then GW1W.RProf s else GW1W.LProf s

def RawRecordBound (right : Bool) (root : ℝ) (s : ExplState) : Prop :=
  ∀ x : ℝ, (x : ℂ) ∈ statePhysicalSet root s → sideCoord right x ≤ outwardRecord right s

theorem rawRecordBound_init (right : Bool) (root : ℝ) :
    RawRecordBound right root (ExplState.init root) := by
  simpa only [RawRecordBound, RealPrefixBound, outwardRecord, sideCoord,
    ExplState.init] using realPrefixBound_init right root

theorem rawRecordBound_moveAlong {right : Bool} {root : ℝ} {s : ExplState}
    (h : RawRecordBound right root s) (w : ℝ) :
    RawRecordBound right root (ExplState.moveAlong s right w true) := by
  intro x hx
  rw [statePhysicalSet_moveAlong] at hx
  cases right
  · have he : stRecL (ExplState.moveAlong s false w true) = min (stRecL s) w := by
      cases s; rfl
    change -x ≤ -stRecL (ExplState.moveAlong s false w true)
    rw [he]
    rcases hx with hx | ⟨y, hy, hyx⟩
    · have hb : -x ≤ -stRecL s := h x hx
      linarith only [hb, min_le_left (stRecL s) w]
    · have heq : y = x := Complex.ofReal_injective hyx
      subst y
      exact neg_le_neg ((min_le_right (stRecL s) w).trans (mem_Icc.1 hy).1)
  · change x ≤ stRecR (ExplState.moveAlong s true w true)
    rw [GW1W.stRecR_moveAlong_true]
    rcases hx with hx | ⟨y, hy, hyx⟩
    · exact (h x hx).trans (le_max_left (stRecR s) w)
    · have heq : y = x := Complex.ofReal_injective hyx
      subst y
      exact (mem_Icc.1 hy).2.trans (le_max_right (stRecR s) w)

theorem outwardRecord_le_launch {right : Bool} {s : ExplState} (hs : OwnProfile right s)
    (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤) :
    outwardRecord right s ≤ outwardRecord right (ExplState.launch s k D θ ⊤) := by
  cases right
  · exact neg_le_neg (launch_le_recL hs k θ hreg hgood hfin)
  · exact recR_le_launch hs k θ hreg hgood hfin

/-- An original point beyond the updated record was beyond the old record and remains alive. -/
theorem alive_of_lt_outwardRecord {right : Bool} {s : ExplState} (hs : OwnProfile right s)
    (k : ℕ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hreg : IsRegularDriver D)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    {x : ℝ} (hx : outwardRecord right (ExplState.launch s k D θ ⊤) < sideCoord right x) :
    outwardRecord right s < sideCoord right x ∧ lAlive (stChart s) ⊤ D x := by
  have hflow := isRealFlow_stop hreg hgood
  cases right
  · obtain ⟨-, -, -, hrec, -, -⟩ :=
      launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
    change -stRecL (ExplState.launch s k D θ ⊤) < -x at hx
    rw [hrec, lRecL_eq_newRec hs.1, neg_neg] at hx
    obtain ⟨-, ha⟩ := pos_alive_of_newRec_lt hs.2.1 hflow.2 hx
    refine ⟨(le_newRec hs.2.1 hflow.2).trans_lt hx, ?_⟩
    unfold lAlive
    rw [hs.1.eq_ofReal x]
    simpa only [GW1W.lProf_eq, neg_neg] using ha
  · obtain ⟨-, -, hrec, -, -, -⟩ :=
      launch_eq_of_ne_top s k D θ ⊤ (GW1W.min_top_ne_top hfin)
    change stRecR (ExplState.launch s k D θ ⊤) < x at hx
    rw [hrec, lRecR_eq_newRec hs.1] at hx
    obtain ⟨-, ha⟩ := pos_alive_of_newRec_lt hs.2.1 hflow.1 hx
    refine ⟨(le_newRec hs.2.1 hflow.1).trans_lt hx, ?_⟩
    unfold lAlive
    rw [hs.1.eq_ofReal x]
    exact ha

/-- The fibre theorem and the alive-point tip exclusion identify the real record
geometrically. All earlier raw points occur in `A`, not only the last piece. -/
theorem piece_real_bound_of_exteriorInverse {right : Bool} {root a : ℝ} {s : ExplState}
    (hOld : RawRecordBound right root s) (hInv : ExteriorInverse right s)
    (hc : IsRealChart (stChart s)) (ha : outwardRecord right s ≤ a)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : GW1P.PieceRegular D.1 D.2) (hfin : D.2 ≠ ⊤)
    (hAlive : ∀ x : ℝ, a < sideCoord right x → lAlive (stChart s) ⊤ D x)
    (hF : GW1Z.FiberGood (stChart s) (statePhysicalSet root s)) :
    ∀ x : ℝ, (x : ℂ) ∈ (stChart s).tipSet
      (fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal) D.2 → sideCoord right x ≤ a := by
  obtain ⟨f, C, hf, -, hfib⟩ := hF
  obtain ⟨hW0, hWc, α, hα, -⟩ := hP
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ D.2 → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα
      (hWc.mono fun _ ht => mem_ofPred.2 (le_of_lt ht)) hW0 ht
  have hset := CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0
    (fun t ht => hf _ (hαH t ht))
  intro x hx
  by_contra hn
  have hax : a < sideCoord right x := lt_of_not_ge hn
  have hxold : outwardRecord right s < sideCoord right x := ha.trans_lt hax
  have hxA : (x : ℂ) ∉ statePhysicalSet root s :=
    fun hx => (not_le.2 hax) ((hOld x hx).trans ha)
  rw [hset] at hx
  obtain ⟨_, ⟨t, ht, rfl⟩, hphys⟩ := hx
  have htS : (t : ℝ≥0∞) ≤ D.2 := ht
  have hxH : (stChart s).1 (x : ℂ) ∈ Hbar := by
    show 0 ≤ ((stChart s).1 (x : ℂ)).im
    rw [hc x]
  have : (𝓝[H] ((stChart s).1 (x : ℂ))).NeBot := GW1P.neBot_nhdsWithin_H hxH
  have hFx : f ((stChart s).1 (x : ℂ)) = (x : ℂ) :=
    tendsto_nhds_unique (hf _ hxH) (hInv x hxold)
  have heq : α t = (stChart s).1 (x : ℂ) :=
    hfib _ (hαH t ht) _ hxH (hphys.trans hFx.symm) (hphys.symm ▸ hxA)
  obtain ⟨u, hu⟩ := hAlive x hax
  have htT : (t : ℝ) ≤ stopTime ⊤ D := by
    dsimp only [stopTime]
    rw [min_eq_right (le_top : D.2 ≤ ⊤)]
    have ht' : t ≤ D.2.toNNReal := ENNReal.coe_le_coe.1 (by
      simpa only [ENNReal.coe_toNNReal hfin] using htS)
    exact_mod_cast ht'
  have hu' := QuantumZipper.isForwardSol_restrict hu t.coe_nonneg htT
  rw [← heq] at hu'
  let w : ℝ≥0 → ℝ := fun r => D.1 (min (r : ℝ≥0∞) D.2).toNNReal
  have hw : Continuous w := CounterflowRange.continuous_stopped hWc
  have hw0 : w 0 = 0 := by simpa only [w, ENNReal.coe_zero, zero_min,
    ENNReal.toNNReal_zero] using hW0
  have htip : Tendsto (fwdMapInv (stopDrv ⊤ D) t) (𝓝[H] 0) (𝓝 (α t)) := by
    simpa only [stopDrv_def, min_eq_right (le_top : D.2 ≤ ⊤)] using
      tendsto_inverse_trace_le (CounterflowRange.isGeneratingTrace_stopped hα) hw hw0 ht
  have hWr : Continuous (stopDrv ⊤ D) := by
    have he : stopDrv ⊤ D = fun r : ℝ => w r.toNNReal := by
      funext r
      simp only [stopDrv_def, w, min_eq_right (le_top : D.2 ≤ ⊤)]
    rw [he]
    exact hw.comp continuous_real_toNNReal
  have hWr0 : stopDrv ⊤ D 0 = 0 := by
    simpa only [stopDrv_def, min_eq_right (le_top : D.2 ≤ ⊤), Real.toNNReal_zero] using hw0
  exact InteractingSLE.Supp8.GB6.not_isForwardSol_of_tip hWr hWr0 t.coe_nonneg htip hu'

end InteractingSLE.Theorem14.GW1WalkExit
