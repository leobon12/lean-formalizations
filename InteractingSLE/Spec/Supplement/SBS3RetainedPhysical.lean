/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedLaw
import InteractingSLE.Spec.Supplement.SBS3TerminalStep
import InteractingSLE.Spec.Supplement.SBS3MarkedPostReg

/-!
# S3: transport and physical provenance through every finite instruction
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- Both branches of the actual word update preserve sorting. -/
theorem isSorted_nextRetainedWord {Ω : Type u} {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {spec : ExplSpec} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {k : ℕ} {β : Ω → BoundaryWord} {ω : Ω} (hs : (β ω).IsSorted) :
    (nextRetainedWord κ b jumps spec E k β ω).IsSorted := by
  classical
  unfold nextRetainedWord
  split
  · exact BoundaryWord.isSorted_shiftW hs _
  · exact isSorted_stopWord κ _

/-- A nonlaunch instruction preserves physical side provenance in the
actual recentered chart, including in a terminal state. -/
theorem interior_stageSide_noLaunch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : LuM.RegLaunches κ b jumps spec D) {k : ℕ}
    (hn : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none)
    {word : BoundaryWord} (hOld : HasInteriorStageSides κ b jumps spec D k word) :
    HasInteriorStageSides κ b jumps spec D (k + 1)
      (BoundaryWord.shiftW
        (((ExplState.run κ b jumps spec D k).2.2.2.2.1.1 0 -
          (ExplState.run κ b jumps spec D (k + 1)).2.2.2.2.1.1 0).re) word) := by
  let a := ((ExplState.run κ b jumps spec D k).2.2.2.2.1.1 0 -
    (ExplState.run κ b jumps spec D (k + 1)).2.2.2.2.1.1 0).re
  intro y hy hyH
  change LuM.bdVal (ExplState.run κ b jumps spec D (k + 1)).2.2.2.2.1 (y : ℂ) ∈ H at hyH
  rw [chart_recenter_of_noLaunch spec D hn,
    bdVal_recenter_real (GW1WalkFinish.hasBdryLimits_chart_run spec D hR k)] at hyH
  have hyJ : y + a ∉ word.jumps := by
    intro hj
    apply hy
    rw [BoundaryWord.jumps_shiftW]
    exact Finset.mem_image.2 ⟨y + a, hj, by ring⟩
  rw [BoundaryWord.fn_shiftW]
  exact (hOld (y + a) hyJ hyH).mono (Nat.le_succ k)

/-- The actual update preserves both the physical chart transport of the
field and the physical interior-side labels, with no launch assumption. -/
theorem ae_nextRetained_transport_sides {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ} (htime : ∀ ω, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      min (instrTime spec k) (E k ω).2 ≠ ⊤)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (htr : ∀ᵐ ω ∂P, IsChartTransport
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1 1 0 (chiC κ) (h ω) (Y ω))
    (hSide : ∀ᵐ ω ∂P, HasInteriorStageSides κ b jumps spec (fun j => E j ω) k (β ω)) :
    ∀ᵐ ω ∂P,
      IsChartTransport (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1
        1 0 (chiC κ) (h ω) (nextRetainedField κ b jumps spec E k Y ω) ∧
      HasInteriorStageSides κ b jumps spec (fun j => E j ω) (k + 1)
        (nextRetainedWord κ b jumps spec E k β ω) := by
  classical
  have hPost := post_stage (spec := spec) (E := E) (ℓ := k) (β := β) (Y := Y)
    (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh
    (fun j _ => hE.1 j) (fun j _ => hreg j) (hE.2.2.2 k)
    hW.1 hW.2.1 hW.2.2.1 hW.2.2.2
  have hTransport := ae_postTransport_of_stageWitness hW
    (Eventually.of_forall fun _ => rfl)
  filter_upwards [htr, hSide, hPost.1, hTransport,
    GW1W.regLaunches_of_stagedPiecesRegular hR] with ω ht hs hg htp hr
  have hconf := GW2aCont.isConformal_runChart spec (fun j => E j ω) k
    (fun j _ c θ hl => hr j c θ hl)
  by_cases hn : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none
  · simp only [nextRetainedField, nextRetainedWord, ite_eq_left hn]
    refine ⟨?_, interior_stageSide_noLaunch hr hn hs⟩
    rw [chart_recenter_of_noLaunch spec (fun j => E j ω) hn]
    exact isChartTransport_recenter_word hconf.1 hconf.2 ht _
  · have hfin := htime ω hn
    simp only [nextRetainedField, nextRetainedWord, ite_eq_right hn, pastMap_last_of_launch hn]
    refine ⟨?_, interior_stageSide_post_launch hκ hr hn hfin (hreg k ω) (hg hn hfin) hs⟩
    have ht' := htp hn
    rw [pastMap_last_of_launch hn, recChart_eq_loewner (hreg k ω) (hg hn hfin),
      Sec5.CrossCond.Staged.trans_id_loewner] at ht'
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hn
    obtain ⟨-, he, -⟩ := eq_launch_of_launches spec (fun j => E j ω) hcθ
    rw [he, chart_launch _ _ _ _ _ hfin]
    exact ht'

end InteractingSLE.Theorem14.SB.S3
