/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvPt
import InteractingSLE.Spec.Supplement.WalkInfVersion

/-!
# SB2(2)'s v6 measurability: the relative chart read through the version chart

Packet PROVE-GW2-GEOM2, round 10 (D28, item (A)). For a relative family `F` measurable and regular before stage `j`,
the version chart of its truncation, `relVer`, is a measurable random chart (`WalkInf.isMeasChart_verChart`), and on
the event `recGoodEv` (the earlier launched relative records with finite stop are good) it is the relative run chart
(`WalkInf.verChart_eq_run`):

* `relVer`, **`isMeasChart_relVer`** (for the ambient σ-algebra);
* **`stChart_eq_relVer`**: on `recGoodEv`, the relative chart at stage `j` is `relVer`;
* **`measurableSet_recGoodEv`**: the event is measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal LuM GW1W GW1Bookkeep

section Rel

variable {Ω : Type*} [MeasurableSpace Ω] {κ θ : ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ}

/-- **The version chart of the truncated relative family at stage `j`.** -/
abbrev relVer (κ θ : ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (j : ℕ) (F : ℕ → Ω → Drv) : Ω → Chart :=
  WalkInf.verChart κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncE j F) j

/-- **The version chart is a measurable random chart** for the ambient σ-algebra. -/
theorem isMeasChart_relVer [StandardBorelSpace Ω] (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) {j : ℕ}
    {F : ℕ → Ω → Drv} (hFm : ∀ i < j, Measurable (F i)) (hFr : ∀ i < j, ∀ ω, IsRegularDriver (F i ω)) :
    WalkInf.IsMeasChart ‹MeasurableSpace Ω› (relVer κ θ b₂ J₂ j F) := by
  have hm := measurable_truncE hFm
  have hr := isRegularDriver_truncE hFr
  have hpm : Measurable (pastMap κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncE j F) j) :=
    measurable_pastMap runMeasStatement hb₂ _ (fun i _ => hm i) (fun i _ => hr i) j le_rfl
  have hle : pastSigma κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncE j F) j ≤ ‹MeasurableSpace Ω› := by
    rw [pastSigma_eq_comap]; exact hpm.comap_le
  exact (WalkInf.isMeasChart_verChart hb₂ hm hr j).mono hle

omit [MeasurableSpace Ω] in
/-- **On the record-good event the relative chart at stage `j` is the version chart.** -/
theorem stChart_eq_relVer {j : ℕ} {F : ℕ → Ω → Drv} (hFr : ∀ i < j, ∀ ω, IsRegularDriver (F i ω)) {ω : Ω}
    (hω : ω ∈ recGoodEv κ θ b₂ J₂ j F) :
    stChart (wRun κ θ b₂ J₂ (fun i => F i ω) j) = relVer κ θ b₂ J₂ j F ω := by
  have hrun : ∀ n ≤ j, ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun i => truncE j F i ω) n =
      ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (fun i => F i ω) n := fun n hn =>
    run_truncE _ F hn ω
  have h := WalkInf.verChart_eq_run (κ := κ) (b := b₂) (jumps := J₂) (spec := boundaryWalkSpec b₂ J₂ θ true)
    (E := truncE j F) (ω := ω) (fun i => isRegularDriver_truncE hFr i ω) (N := j) (fun i hi hl hfin => ?_) j le_rfl
  · show _ = WalkInf.verChart κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) (truncE j F) j ω
    rw [h, hrun j le_rfl]
  · have hTi : truncE j F i = F i := truncE_of_lt F hi
    rw [hTi] at hfin ⊢
    rw [hrun (i + 1) hi] at hl
    exact hω i hi hl hfin

/-- **The record-good event is measurable.** -/
theorem measurableSet_recGoodEv (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) {j : ℕ} {F : ℕ → Ω → Drv}
    (hFm : ∀ i < j, Measurable (F i)) (hFr : ∀ i < j, ∀ ω, IsRegularDriver (F i ω)) :
    MeasurableSet (recGoodEv κ θ b₂ J₂ j F) := by
  have hm := measurable_truncE hFm
  have hr := isRegularDriver_truncE hFr
  have e : recGoodEv κ θ b₂ J₂ j F = ⋂ i ∈ Finset.range j,
      ({ω | (wRun κ θ b₂ J₂ (fun i => truncE j F i ω) (i + 1)).2.2.2.1 i ≠ none}ᶜ ∪
        ({ω | min (instrTime (boundaryWalkSpec b₂ J₂ θ true) i) (truncE j F i ω).2 ≠ ⊤}ᶜ ∪
          {ω | LocalExt.IsDrvGood (recHist (recOf (instrTime (boundaryWalkSpec b₂ J₂ θ true) i)
            (truncE j F i ω)))})) := by
    ext ω
    simp only [recGoodEv, mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_union, mem_compl_iff]
    refine forall₂_congr fun i hi => ?_
    simp only [wRun]
    rw [truncE_of_lt F hi, run_truncE _ F (Nat.succ_le_of_lt hi) ω]
    tauto
  rw [e]
  refine MeasurableSet.biInter (Finset.range j).countable_toSet fun i _ => ?_
  refine (runMeasStatement κ b₂ J₂ hb₂ _ (truncE j F) hm hr i).1.compl.union
    ((measurableSet_eq_fun ?_ measurable_const).compl.compl.union ?_)
  · exact measurable_const.min (measurable_snd.comp (hm i))
  · exact (measurable_recHist.comp (measurable_recOf (hm i) (hr i) _)) LocalExt.measurableSet_isDrvGood

end Rel

end InteractingSLE.Theorem14.SB.Nv
