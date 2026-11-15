/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TcTrace

/-!
# The explored hull's locality reduced to a physical curve inside the explored trace

Packet PROVE-GW2-RELDET, ruling R113. Round 18's curve statement `GW2TbHull.SchedCurveLocalStatement` uses the chosen
trace `schedTr`, whose avoidance events are not known to be measurable. Here the curve is read through measurable
samples (`GW2TcTrace.schedSamples`), and the remaining input is sharpened.

* `schedCurveS q`: the samples' closure on `oldSuccess`, `ℍ` off it. Its avoidance events are marks for any marks
  reading the explored path on `[0, q]` and the history records.
* `SchedCurveLocalStatementS`: round 18's curve statement for `schedCurveS`.
* **`schedHullLocalStatementL_of_curveS`**: `Theorem13Statement → SchedCurveLocalStatementS → SchedHullLocalStatementL`
  (round 18's hull statement).
* **`SchedPhysCurveStatement`** (named input): marks as before, and a marked local set with marks as avoidance events
  that lies, almost surely on `oldSuccess`, in the explored trace on `[0, q]`. This is the physical explored curve:
  round 10's stage set of the program capped at `q`. On `oldSuccess` it is inside the trace (GEOM2's
  `Gm.prefixSet_*_eq`).
* **`schedCurveLocalStatementS_of_phys`**: `Theorem13Statement → SchedPhysCurveStatement → SchedCurveLocalStatementS`.
  The proof uses `isHistoryAvoidanceLocal_of_superset_marks` and `isHistoryAvoidanceLocal_ite_H`.
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
/-- The explored curve on `[0, q]` through measurable samples where the history succeeded, `ℍ` elsewhere. -/
def schedCurveS (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0)
    (ω : Ω) : Set ℂ :=
  if oldSuccess c r l ω then schedSamples c r l a q ω else H

/-- **Round 18's curve statement for the sampled curve.** -/
def SchedCurveLocalStatementS : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), rootPt r.1 = 0 → ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension c.b c.jumps u₀ →
    ∀ q : ℝ≥0, historyTime c r l ≤ q → ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets c.P ≤ 𝓜.1 ∧
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (schedCurveS c r l a q ω) U}) ∧
      IsHistoryAvoidanceLocal 𝓜.1 (schedCurveS c r l a q) (centredField c.h u₀) c.P

/-- **Named input: a marked local physical curve inside the explored trace** (root `0`, after the history). -/
def SchedPhysCurveStatement : Prop :=
  ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), rootPt r.1 = 0 → ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension c.b c.jumps u₀ →
    ∀ q : ℝ≥0, historyTime c r l ≤ q → ∃ 𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}, Ito.nullSets c.P ≤ 𝓜.1 ∧
      (∀ t ≤ q, Measurable[𝓜.1] (schedW c r l a t)) ∧
      (∀ j : Fin ((entryList l).length + 1),
        Measurable[𝓜.1] (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpecOf r.1 l) j)) ∧
      𝓜.1 ≤ aeSigma (MeasurableSpace.comap (centredField c.h u₀) inferInstance) c.P ∧
      ∃ S : Ω → Set ℂ, (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (S ω) U}) ∧
        IsHistoryAvoidanceLocal 𝓜.1 S (centredField c.h u₀) c.P ∧
        ∀ᵐ ω ∂c.P, oldSuccess c r l ω → S ω ∩ H ⊆ schedTr c r l a ω '' Icc 0 q

end Defs

/-- **The explored hull is marked local, from the locality of the sampled curve** (Theorem 1.3). -/
theorem schedHullLocalStatementL_of_curveS (h13 : Exist.Theorem13Statement.{u})
    (hC : SchedCurveLocalStatementS.{u}) : SchedHullLocalStatementL.{u} := by
  intro Ω mΩ _ c r l a hr0 u₀ hu₀ q hq
  obtain ⟨𝓜, hnull, hW, hrec, hd, hSm, hloc⟩ := hC c r l a hr0 u₀ hu₀ q hq
  have hE : MeasurableSet[𝓜.1] {ω | oldSuccess c r l ω} := measurableSet_oldSuccess_of_records c r l 𝓜 hrec
  have hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P :=
    isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData c.hh hu₀
  have hKm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet {ω | Disjoint (schedHull c r l a q ω) U} :=
    fun U hUH => measurable_schedHull_of c r l a ⟨mΩ, le_rfl⟩ (fun t _ => measurable_schedW c r l a t)
      (measurableSet_avoid U.isOpen hUH)
  have hgood : ∀ᵐ ω ∂c.P, ω ∈ {ω | oldSuccess c r l ω} →
      IsFilling (schedHull c r l a q ω) (schedCurveS c r l a q ω) ∧ IsOpen (H \ schedCurveS c r l a q ω) ∧
        ∃ R : ℝ, {w : ℂ | R < w.im} ⊆ H \ schedHull c r l a q ω := by
    filter_upwards [ae_schedW_trace c r l a h13, ae_schedSamples_eq c r l a h13 q] with ω hω hsω hωE
    have hS : schedCurveS c r l a q ω = schedSamples c r l a q ω := by
      simp only [schedCurveS, show oldSuccess c r l ω from hωE, ↓reduceIte]
    rw [hS]
    refine ⟨?_, QuantumZipper.isOpen_H.sdiff isClosed_closure, ?_⟩
    · rw [hsω]
      exact hω.1.2.2 q ENNReal.coe_lt_top
    · exact exists_halfIm_subset_compl_fwdHull ((continuous_schedW c r l a ω).comp continuous_real_toNNReal) q
  obtain ⟨hAm, hAloc⟩ := isHistoryAvoidanceLocal_fill_on_ae (measurable_centredField c.hh.1 u₀) hh 𝓜.2 hnull hloc
    hSm hKm hd hE hgood
  exact ⟨𝓜, hnull, hW, hrec, hd, hAm, hAloc⟩

/-- **The sampled curve is marked local, from a marked local physical curve inside the trace** (Theorem 1.3). -/
theorem schedCurveLocalStatementS_of_phys (h13 : Exist.Theorem13Statement.{u})
    (hP : SchedPhysCurveStatement.{u}) : SchedCurveLocalStatementS.{u} := by
  classical
  intro Ω mΩ _ c r l a hr0 u₀ hu₀ q hq
  obtain ⟨𝓜, hnull, hW, hrec, hd, S, hSm, hloc, hST⟩ := hP c r l a hr0 u₀ hu₀ q hq
  have hhm := measurable_centredField c.hh.1 u₀
  have hE : MeasurableSet[𝓜.1] {ω | oldSuccess c r l ω} := measurableSet_oldSuccess_of_records c r l 𝓜 hrec
  -- the sampled curve's avoidance events are marks
  have hev0 : ∀ U : Opens ℂ, (U : Set ℂ) = ∅ → ∀ X : Ω → Set ℂ, {ω | Disjoint (X ω) U} = univ := by
    intro U hU X
    ext ω
    simp only [hU, mem_ofPred_eq, disjoint_empty, mem_univ]
  have hCm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[𝓜.1] {ω | Disjoint (schedCurveS c r l a q ω) U} := by
    intro U hUH
    by_cases hU : (U : Set ℂ) = ∅
    · rw [hev0 U hU]
      exact MeasurableSet.univ
    · obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hU
      have e : {ω | Disjoint (schedCurveS c r l a q ω) U} =
          {ω | oldSuccess c r l ω} ∩ {ω | Disjoint (schedSamples c r l a q ω) U} := by
        ext ω
        by_cases hω : oldSuccess c r l ω
        · simp only [schedCurveS, hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, true_and]
        · simp only [schedCurveS, hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, false_and, iff_false]
          exact fun hd' => disjoint_left.1 hd' (hUH hz) hz
      rw [e]
      exact hE.inter (measurableSet_disjoint_schedSamples c r l a 𝓜 hW U.isOpen)
  obtain ⟨hAm, hAloc⟩ := isHistoryAvoidanceLocal_ite_H hhm hloc hSm hd hE
  refine ⟨𝓜, hnull, hW, hrec, hd, hCm, isHistoryAvoidanceLocal_of_superset_marks hhm hAloc hAm hCm hd ?_⟩
  filter_upwards [hST, ae_schedSamples_eq c r l a h13 q] with ω hω hsω
  by_cases hωE : oldSuccess c r l ω
  · have h1 : (if oldSuccess c r l ω then S ω else H) = S ω := by
      simp only [hωE, ↓reduceIte]
    have h2 : schedCurveS c r l a q ω = schedTr c r l a ω '' Icc 0 q := by
      simp only [schedCurveS, hωE, ↓reduceIte, hsω]
    rw [h1, h2]
    exact hω hωE
  · have h1 : (if oldSuccess c r l ω then S ω else H) = H := by
      simp only [hωE, ↓reduceIte]
    have h2 : schedCurveS c r l a q ω = H := by simp only [schedCurveS, hωE, ↓reduceIte]
    rw [h1, h2]
    exact inter_subset_left

end InteractingSLE.Theorem14.GW2Rd
