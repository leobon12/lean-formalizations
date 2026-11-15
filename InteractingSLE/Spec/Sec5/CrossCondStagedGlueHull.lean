/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueLoc
import InteractingSLE.Spec.Coupling.Locality11Hull
import InteractingSLE.GFF.LocalSets.GermVersion

/-!
# The hull of the staged prefix of an extreme-angle schedule: the flow-side inputs of the staged glued law

Packet PROVE-STAGED5 (PROVE-CROSSCOND-STAGED4 §5.1). The staged glued law (`Staged.ae_condExp_union_cfGlueT_add_eq`)
and the staged own mean (`StagedFinal.exists_rep_stageMeanW`) take as flow side the **hull** left by the stopped pieces
(the complement of the stage chart's domain, `hAD`), read from the retained past `Yf = pastMap (n + 1)`, with inputs
`h𝔄` (hitting-measurability in the records), `hAl` (local set) and `hAloc` (history-avoidance local for the records).
`CrossCondStagedGlueLoc` proved `hAloc` for the trace set. Here:

* **`isHistoryAvoidanceLocal_of_subset`** (generic): a random set `K` containing a history-marked local set `T` almost
  surely is history-marked local for the same marks if its own avoidance events are marks (the hull is filled in from
  the recorded trace);
* `recDrvOf_continuous`, `recDrvOf_zero`, `measurable_recDrvOf_apply`; **`recHull`** (the hull of the joined record
  driver, `ℍ ∖` the domain of the recentred Loewner chart of the concatenated records) and **`measurable_recHull`**
  (`h𝔄`);
* **`IsGoodSched.subset_recHull`**: on the good event the explored set `α([0, S_{n+1}]) ∩ ℍ` lies in the hull;
* **`exists_flowSide_schedule`**: for every `n + 1 ≤ L`, the hull `recHull s n (pastMap (n + 1) ω)` is
  history-avoidance local for `pastSigma (n + 1)` (`hAloc`, R48-safe) and a local set (`hAl`) of the centred field, and
  `recHull s n` is hitting-measurable (`h𝔄`); it is `ℍ` minus the domain of STAGED2's `stageChart` (`recHull_eq`).

R48: nothing here uses Theorem 1.2/1.3; the only named input is `AdmCode.Theorem12ParamCond44Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedGlue

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule
open Theorem14.GW2Schedule (schedDelta)
open Restart (BoundaryWord)
open InteractingSLE.Sec5.CrossCond.Staged (catN cumT catChartN continuous_catN catN_zero stageChart stageDrv)
open InteractingSLE.Sec5.CrossCond.StagedFinal (startN)

/-! ### A filled-in set of a marked local set -/

section Subset

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **A filled-in set of a history-marked local set is history-marked local** for the same marks, when its own
avoidance events of open subsets of `ℍ` are marks: `{K ∩ U = ∅} ∩ F = {T ∩ U = ∅} ∩ ({K ∩ U = ∅} ∩ F)` almost surely,
since `T ⊆ K`. -/
theorem isHistoryAvoidanceLocal_of_subset {T K : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hTK : ∀ᵐ ω ∂P, T ω ⊆ K ω)
    (hK : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (K ω) U})
    (hT : WholeField.IsHistoryAvoidanceLocal ℋ T h P) : WholeField.IsHistoryAvoidanceLocal ℋ K h P := by
  intro U G hUH hG hd F hF
  obtain ⟨g, hg, hge⟩ := hT U G hUH hG hd ({ω | Disjoint (K ω) U} ∩ F) ((hK U hUH).inter hF)
  refine ⟨g, hg, Filter.EventuallyEq.trans ?_ hge⟩
  refine condExp_congr_ae (indicator_ae_eq_of_ae_eq_set ?_)
  filter_upwards [hTK] with ω hω
  change (ω ∈ {ω | Disjoint (K ω) (U : Set ℂ)} ∩ F) =
    (ω ∈ {ω | Disjoint (T ω) (U : Set ℂ)} ∩ ({ω | Disjoint (K ω) (U : Set ℂ)} ∩ F))
  exact propext ⟨fun h' => ⟨Disjoint.mono_left hω h'.1, h'⟩, fun h' => h'.2⟩

end Subset

/-! ### The hull of the joined record driver -/

section Hull

theorem recDrvOf_continuous {k : ℕ} (u : PastData k) (j : ℕ) : Continuous (recDrvOf u j) := by
  unfold recDrvOf
  split_ifs
  · exact LocalExt.continuous_histDrv _
  · exact continuous_const

theorem recDrvOf_zero {k : ℕ} (u : PastData k) (j : ℕ) : recDrvOf u j 0 = 0 := by
  unfold recDrvOf
  split_ifs
  · exact LocalExt.histDrv_zero _
  · rfl

theorem measurable_recDrvOf_apply (k j : ℕ) (t : ℝ≥0) : Measurable fun u : PastData k => recDrvOf u j t := by
  unfold recDrvOf
  split_ifs with hj
  · exact (LocalExt.measurable_histDrv_apply (nL := 0) (nR := 0) t).comp
      (measurable_recHist.comp (measurable_pi_apply _))
  · exact measurable_const

/-- **The hull of the joined record driver** of the pieces `0, …, n` of a schedule, read off a retained past: `ℍ`
minus the domain of the recentred Loewner chart of the concatenated record drivers. -/
def recHull (s : Schedule) (n : ℕ) (u : PastData (n + 1)) : Set ℂ :=
  H \ ((catChartN 0 (recDrvOf u) (schedD s) n).dom : Set ℂ)

theorem disjoint_recHull_iff (s : Schedule) (n : ℕ) (u : PastData (n + 1)) {U : Set ℂ} (hU : IsOpen U)
    (hUH : U ⊆ H) : Disjoint (recHull s n u) U ↔ ∀ b : ℚ × ℚ × ℚ, Coupling.ratCBall b ⊆ U →
      Coupling.ratCBall b ⊆ ((catChartN 0 (recDrvOf u) (schedD s) n).dom : Set ℂ) := by
  rw [Coupling.disjoint_iff_forall_ratCBall hU]
  refine forall_congr' fun b => forall_congr' fun hb => ⟨fun h z hz => ?_, fun h => ?_⟩
  · by_contra hn
    exact Set.disjoint_left.1 h hz ⟨hUH (hb hz), hn⟩
  · exact Set.disjoint_left.2 fun z hz hK => hK.2 (h hz)

theorem measurableSet_disjoint_recHull (s : Schedule) (n : ℕ) {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) :
    MeasurableSet {u : PastData (n + 1) | Disjoint (recHull s n u) U} := by
  have e : {u : PastData (n + 1) | Disjoint (recHull s n u) U} = ⋂ b : ℚ × ℚ × ℚ, ⋂ (_ : Coupling.ratCBall b ⊆ U),
      {u | Coupling.ratCBall b ⊆ ((catChartN 0 (recDrvOf u) (schedD s) n).dom : Set ℂ)} := by
    ext u
    simp only [mem_ofPred_eq, mem_iInter]
    exact disjoint_recHull_iff s n u hU hUH
  rw [e]
  refine MeasurableSet.iInter fun b => MeasurableSet.iInter fun _ => ?_
  exact Staged.measurableSet_closedBall_subset_dom_catChartN (W := fun j u => recDrvOf u j) (schedD s) 0
    (fun j u => recDrvOf_continuous u j) (fun j u => recDrvOf_zero u j)
    (fun j t => measurable_recDrvOf_apply (n + 1) j t) n _ _

/-- **The hull of the joined record driver is hitting-measurable in the records** (`h𝔄`). -/
theorem measurable_recHull (s : Schedule) (n : ℕ) : Measurable[_, hittingSigma] (recHull s n) := by
  refine @measurable_generateFrom _ _ _ _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : recHull s n ⁻¹' {A : Set ℂ | (A ∩ U).Nonempty} = {u | Disjoint (recHull s n u) U}ᶜ := by
    ext u
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, not_disjoint_iff_nonempty_inter]
  rw [e]
  exact (measurableSet_disjoint_recHull s n hU hUH).compl

/-- The hull is `ℍ` minus the domain of STAGED2's stage chart (for the schedule program). -/
theorem recHull_eq {κ : ℝ} {c₀ : BoundaryWord} {s : Schedule} {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (n : ℕ) (ω : Ω) :
    recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω) =
      H \ ((stageChart κ c₀.fn c₀.jumps (scheduleSpec s) (schedDelta 0 (scheduleList s)) E n ω).dom : Set ℂ) :=
  rfl

variable {κ : ℝ} {c₀ : BoundaryWord} {s : Schedule} {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

/-- **On the good event the explored set lies in the hull.** -/
theorem IsGoodSched.subset_recHull (hg : IsGoodSched s E ω) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (joinW s E ω) ⊤ α) {n : ℕ} (hn : n + 1 ≤ schedL s) :
    α '' Icc 0 (startN (schedD s) (n + 1)) ∩ H ⊆
      recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω) := by
  have hVk : ∀ t ≤ cumT (schedD s) n,
      joinW s E ω t = catN (recDrvOf (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω)) (schedD s) n t := by
    intro t ht
    rw [joinW, catN_of_le_cumT (by omega : n ≤ schedL s - 1) ht]
    refine catN_congr_cumT (fun j hj r hr => ?_) t ht
    rw [pieceW_of_lt s E ω (by omega), hg.recDrvOf_eq hreg hn (by omega), min_eq_left hr]
  obtain ⟨z₀, hdom⟩ := dom_catChartN_eq (w := recDrvOf (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω))
    (fun j => recDrvOf_continuous _ j) (fun j => recDrvOf_zero _ j) n hg.continuous_joinW hVk hα
  rintro z ⟨hz, hzH⟩
  refine ⟨hzH, fun hzd => ?_⟩
  have hz' := (connectedComponentIn_subset _ _) (hdom ▸ hzd : z ∈ connectedComponentIn _ z₀)
  exact hz'.2 hz

end Hull

/-! ### The flow-side inputs -/

section Inputs

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4

/-- **The flow-side inputs of the staged glued law for an extreme-angle schedule** (R48-safe; PROVE-CROSSCOND-STAGED4
§5.1 item 1): for every `n + 1 ≤ L`, the hull `𝔄 (Yf ω) = recHull s n (pastMap (n + 1) ω)` left by the pieces
`0, …, n` (`ℍ` minus the domain of the stage chart, `recHull_eq`) satisfies `h𝔄` (hitting-measurable in the records),
`hAloc` (history-avoidance local for the records `σ(pastMap (n + 1)) = pastSigma (n + 1)`) and `hAl` (a local set) for
the centred field `h − u₀`. -/
theorem exists_flowSide_schedule (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀) {n : ℕ} (hn : n + 1 ≤ schedL s) :
    Measurable[_, hittingSigma] (recHull s n) ∧
      WholeField.IsHistoryAvoidanceLocal
        (MeasurableSpace.comap (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1)) inferInstance)
        (fun ω => recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω))
        (WholeField.centredField h u₀) P ∧
      IsLocalSet (fun ω => recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω))
        (WholeField.centredField h u₀) P := by
  obtain ⟨α, -, -, -, hαtr, hloc⟩ := exists_isHistoryAvoidanceLocal_schedule h44 hκ hκ4 c₀ hc₀ hh s hE hreg hu₀
  have hG := ae_isGoodSched h44 hκ hκ4 c₀ hc₀ hh s hE hreg
  have hm := measurable_recHull s n
  have hpm : Measurable (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1)) :=
    measurable_pastMap runMeasStatement c₀.isPiecewiseConstantBoundaryData (scheduleSpec s) (k := n + 1)
      (fun j _ => hE.1 j) (fun j _ => hreg j) (n + 1) le_rfl
  have hloc' : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1)) inferInstance)
      (fun ω => recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω))
      (WholeField.centredField h u₀) P := by
    refine isHistoryAvoidanceLocal_of_subset (T := fun ω => α ω '' Icc 0 (startN (schedD s) (n + 1)) ∩ H) ?_
      (fun U hUH => ⟨_, measurableSet_disjoint_recHull s n U.isOpen hUH, rfl⟩) (hloc n hn)
    filter_upwards [hG, hαtr] with ω hg hα
    exact hg.subset_recHull hreg hα hn
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hAm : Measurable[mΩ, hittingSigma]
      fun ω => recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω) :=
    hm.comp hpm
  have hAc : ∀ᵐ ω ∂P, recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω) ⊆ H ∧
      IsOpen (H \ recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω)) := by
    refine Eventually.of_forall fun ω => ⟨sdiff_subset, ?_⟩
    have hconf := Staged.isConformal_catChartN (T := schedD s) 0
      (fun j => recDrvOf_continuous (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω) j)
      (fun j => recDrvOf_zero (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω) j) n
    have e : H \ recHull s n (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω) =
        H ∩ ((catChartN 0 (recDrvOf (pastMap κ c₀.fn c₀.jumps (scheduleSpec s) E (n + 1) ω)) (schedD s) n).dom :
          Set ℂ) := by
      unfold recHull
      rw [sdiff_sdiff_right_self]
    rw [e]
    exact QuantumZipper.isOpen_H.inter (Opens.isOpen _)
  exact ⟨hm, hloc', ((LocalSets.isLocalSet_tfae hh0 hAm hAc).out 1 4).1
    (WholeField.IsHistoryAvoidanceLocal.isAvoidanceLocal hloc')⟩

end Inputs

end InteractingSLE.Sec5.CrossCond.StagedGlue
