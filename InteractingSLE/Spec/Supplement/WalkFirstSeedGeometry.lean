/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkSeedFiniteMain
import InteractingSLE.Spec.Supplement.GW1WalkExitFinite

/-! # Physical endpoint of the first piece, without an ambient side bound -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkFirstSeed

open Exist.Staged Exist.StagedLaw GW1WalkExit GW1WalkFinish

/-- The untranslated root has both exterior profiles. -/
theorem ownProfile_init (right : Bool) : OwnProfile right (ExplState.init 0) := by
  have hr : rProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [rProf, ExplState.init, Chart.id, Chart.recenter]
  have hl : lProf (stChart (ExplState.init 0)) = fun x => x := by
    funext x
    simp [lProf, ExplState.init, Chart.id, Chart.recenter]
  have hp : RightGood (fun x : ℝ => x) 0 :=
    ⟨strictMonoOn_id, continuousOn_id, fun M => ⟨max M 0 + 1, by positivity, by
      linarith only [le_max_left M 0]⟩⟩
  have hreal : IsRealChart (stChart (ExplState.init 0)) := by
    intro x
    simp [stChart, ExplState.init, Chart.id, Chart.recenter]
  cases right
  · change IsRealChart _ ∧ RightGood _ _ ∧ _
    rw [hl]
    simp only [stRecL, ExplState.init, neg_zero]
    exact ⟨hreal, hp, fun x hx => hx, fun ε hε => ⟨ε / 2, half_pos hε, by linarith⟩⟩
  · change IsRealChart _ ∧ RightGood _ _ ∧ _
    rw [hr]
    exact ⟨hreal, hp, fun x hx => hx, fun ε hε => ⟨ε / 2, half_pos hε, by linarith⟩⟩

/-- Exterior correspondence at a threshold needs its actual side, rather
than a globally prescribed direction or an outward-height hypothesis. -/
theorem exteriorRecord_launch_of_threshold {right : Bool} {s : ExplState}
    (hs : OwnProfile right s) (hI : ExteriorInverse right s) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (θ : ℝ) (hreg : IsRegularDriver D)
    (hP : GW1P.PieceRegular D.1 D.2)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hthr : stStatus (ExplState.launch s k D θ ⊤) = stThr (some right))
    (hB : HasBdryLimits (stChart (ExplState.launch s k D θ ⊤)).2.1) :
    ExteriorRecord right (ExplState.launch s k D θ ⊤) := by
  have hinv := exteriorInverse_launch hI hs.isRealChart k θ hP hfin
    (fun x hx => alive_of_lt_outwardRecord hs k θ hreg hgood hfin hx)
  apply exteriorRecord_of_profile_inverse hB _ _ hinv
  · cases right
    · exact (GW1W.lProf_launch hs k θ hreg hgood hfin
        (GW1W.launch_thr_false hfin hthr).2.1).1
    · exact (GW1W.rProf_launch hs k θ hreg hgood hfin
        (GW1W.launch_thr_true hfin hthr).2.1).1
  · cases right
    · exact congrArg Neg.neg (GW1W.launch_thr_false hfin hthr).2.2.1
    · exact (GW1W.launch_thr_true hfin hthr).2.2.1

/-- At a finite threshold of a regular first piece, the physical generating
trace ends exactly at the point recorded by the exploration machine. -/
theorem trace_endpoint_eq_launch_point {right : Bool} {D : (ℝ≥0 → ℝ) × ℝ≥0∞}
    {θ : ℝ} (hreg : IsRegularDriver D) (hP : GW1P.PieceRegular D.1 D.2)
    (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hthr : stStatus (ExplState.launch (ExplState.init 0) 0 D θ ⊤) = stThr (some right))
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace D.1 D.2 α) :
    α D.2.toNNReal = (stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) : ℂ) := by
  have hch := (launch_eq_of_ne_top (ExplState.init 0) 0 D θ ⊤ (GW1W.min_top_ne_top hfin)).1
  have hB : HasBdryLimits (stChart (ExplState.launch (ExplState.init 0) 0 D θ ⊤)).2.1 := by
    rw [hch]
    simpa only [stChart, ExplState.init, Chart.loewner, Chart.recenter, Chart.id,
      Complex.ofReal_zero, add_zero, stopDrv_def, stopTime,
      min_eq_right (le_top : D.2 ≤ ⊤)] using hP.hasBdryLimits hfin
  have hE := exteriorRecord_launch_of_threshold (ownProfile_init right)
    (exteriorInverse_init right 0) 0 θ hreg hP hgood hfin hthr hB
  have hpoint := boundary_limit_of_exteriorRecord hB hE
  have htrace := tendsto_inverse_trace_le (CounterflowRange.isGeneratingTrace_stopped hα)
    (CounterflowRange.continuous_stopped hP.2.1) (by simpa using hP.1)
    (ENNReal.coe_toNNReal hfin).le
  have hpoint' : Tendsto (QuantumZipper.fwdMapInv (stopDrv ⊤ D) (stopTime ⊤ D))
      (𝓝[H] 0) (𝓝 (stPt (ExplState.launch (ExplState.init 0) 0 D θ ⊤) : ℂ)) := by
    rw [hch] at hpoint
    simpa only [stChart, ExplState.init, Chart.loewner, Chart.recenter, Chart.id,
      Complex.ofReal_zero, add_zero] using hpoint
  have : (𝓝[H] (0 : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (by simp [QuantumZipper.Hbar])
  apply tendsto_nhds_unique _ hpoint'
  simpa only [stopDrv_def, stopTime, min_eq_right (le_top : D.2 ≤ ⊤)] using htrace

end InteractingSLE.Theorem14.WalkFirstSeed
