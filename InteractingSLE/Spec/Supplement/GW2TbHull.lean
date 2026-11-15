/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TbFillOn

/-!
# The explored hull of the schedule is marked local, from the locality of the explored curve

Packet PROVE-GW2-RELDET, ruling R113. Round 16's `GW2SzLoc.SchedHullLocalStatement` is false where the history fails
(round 17: off `oldSuccess` the hull is a deterministic slit). The corrected explored sets use the whole half-plane
off the mark `oldSuccess`:

* `schedCurveL q`: the explored trace on `[0, q]` on `oldSuccess`, `ℍ` off it;
* `schedHullL q`: the explored hull `fwdHull schedW q` on `oldSuccess`, `ℍ` off it.

**`SchedCurveLocalStatement`** (the corrected named input, at the level of CURVES): at root `0` and every physical time
`q` after the history, the explored curve set is marked local for field-determined marks. The marks contain the null
sets, the explored path on `[0, q]` and the history's piece records, and their avoidance events are marks.

**`SchedHullLocalStatementL`** is the same statement for the HULL. **`schedHullLocalStatementL_of_curve`** derives
it from the curve statement and Theorem 1.3. The proof:
* the hull fills the trace almost surely (`IsGeneratingTrace`, `GW2SyJoin.ae_schedW_trace`);
* `ℍ \ trace` is open, the trace being compact;
* the hull misses a far half-plane (`exists_halfIm_subset_compl_fwdHull`);
* `oldSuccess` is a mark, read from the history records;
* then `isHistoryAvoidanceLocal_fill_on_ae`.

What remains in the curve statement: on `oldSuccess` the explored trace is the physical stage set of the capped
program (GEOM2's `Gm.prefixSet_*_eq`). After a death it is that set together with a path-determined continuation, so
`isHistoryAvoidanceLocal_union_marks` applies. The stage set is marked local by round 10's tools.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Restart Exist Exist.Staged Exist.StagedLaw LocalSets WholeField Supp8 GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31

section Defs

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

open scoped Classical in
/-- The explored curve on `[0, q]` where the history succeeded, the whole half-plane elsewhere. -/
def schedCurveL (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  if oldSuccess c r l ω then schedTr c r l a ω '' Icc 0 q else H

open scoped Classical in
/-- The explored hull at `q` where the history succeeded, the whole half-plane elsewhere. -/
def schedHullL (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  if oldSuccess c r l ω then schedHull c r l a q ω else H

/-- **Named input (corrected): the explored curve of the schedule is marked local** (root `0`, after the history). -/
def SchedCurveLocalStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), rootPt r.1 = 0 → ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension c.b c.jumps u₀ →
    ∀ q : ℝ≥0, historyTime c r l ≤ q → ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets c.P ≤ 𝓜.1 ∧
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (schedCurveL c r l a q ω) U}) ∧
      IsHistoryAvoidanceLocal 𝓜.1 (schedCurveL c r l a q) (centredField c.h u₀) c.P

/-- **The corrected filled-hull locality** (replaces `GW2SzLoc.SchedHullLocalStatement`). -/
def SchedHullLocalStatementL : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), rootPt r.1 = 0 → ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension c.b c.jumps u₀ →
    ∀ q : ℝ≥0, historyTime c r l ≤ q → ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets c.P ≤ 𝓜.1 ∧
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (schedHullL c r l a q ω) U}) ∧
      IsHistoryAvoidanceLocal 𝓜.1 (schedHullL c r l a q) (centredField c.h u₀) c.P

end Defs

/-- `oldSuccess` is an event of any σ-algebra reading the history's piece records. -/
theorem measurableSet_oldSuccess_of_records {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (M : {m : MeasurableSpace Ω // m ≤ mΩ})
    (hrec : ∀ j : Fin ((entryList l).length + 1),
      @Measurable Ω RecData M.1 _ (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) :
    @MeasurableSet Ω M.1 {ω | oldSuccess c r l ω} := by
  have hlen : (historyProgram c r l).length = (entryList l).length + 1 := by
    simp only [historyProgram, schedOf, List.length_cons, List.length_reverse]
  have e : {ω | oldSuccess c r l ω} = ⋂ j : Fin (historyProgram c r l).length,
      {ω | (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (historyProgram c r l)) j ω).2.2 = false} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    rfl
  rw [e]
  refine @MeasurableSet.iInter Ω _ M.1 _ _ fun j => ?_
  have hj : @Measurable Ω RecData M.1 _
      (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (historyProgram c r l)) j) :=
    hrec ⟨j.1, hlen ▸ j.2⟩
  exact ((measurable_snd.comp measurable_snd).comp hj) (measurableSet_singleton false)

/-- **The explored hull of the schedule is marked local, from the locality of its curve** (Theorem 1.3). -/
theorem schedHullLocalStatementL_of_curve (h13 : Exist.Theorem13Statement.{u}) (hC : SchedCurveLocalStatement.{u}) :
    SchedHullLocalStatementL.{u} := by
  intro Ω mΩ _ c r l a hr0 u₀ hu₀ q hq
  obtain ⟨𝓜, hnull, hW, hrec, hd, hSm, hloc⟩ := hC c r l a hr0 u₀ hu₀ q hq
  have hE : MeasurableSet[𝓜.1] {ω | oldSuccess c r l ω} := measurableSet_oldSuccess_of_records c r l 𝓜 hrec
  have hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P :=
    isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hKm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet {ω | Disjoint (schedHull c r l a q ω) U} :=
    fun U hUH => measurable_schedHull_of c r l a ⟨mΩ, le_rfl⟩ (fun t _ => measurable_schedW c r l a t)
      (measurableSet_avoid U.isOpen hUH)
  have hgood : ∀ᵐ ω ∂c.P, ω ∈ {ω | oldSuccess c r l ω} →
      IsFilling (schedHull c r l a q ω) (schedCurveL c r l a q ω) ∧ IsOpen (H \ schedCurveL c r l a q ω) ∧
        ∃ R : ℝ, {w : ℂ | R < w.im} ⊆ H \ schedHull c r l a q ω := by
    filter_upwards [ae_schedW_trace c r l a h13] with ω hω hωE
    have hS : schedCurveL c r l a q ω = schedTr c r l a ω '' Icc 0 q := by
      simp only [schedCurveL, show oldSuccess c r l ω from hωE, ↓reduceIte]
    rw [hS]
    have hcont : ContinuousOn (schedTr c r l a ω) (Icc 0 q) :=
      hω.1.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top
    refine ⟨hω.1.2.2 q ENNReal.coe_lt_top, QuantumZipper.isOpen_H.sdiff
      ((isCompact_Icc.image_of_continuousOn hcont).isClosed), ?_⟩
    exact exists_halfIm_subset_compl_fwdHull ((continuous_schedW c r l a ω).comp continuous_real_toNNReal) q
  obtain ⟨hAm, hAloc⟩ := isHistoryAvoidanceLocal_fill_on_ae (measurable_centredField c.hh.1 u₀) hh 𝓜.2 hnull hloc
    hSm hKm hd hE hgood
  exact ⟨𝓜, hnull, hW, hrec, hd, hAm, hAloc⟩

end InteractingSLE.Theorem14.GW2Rd
