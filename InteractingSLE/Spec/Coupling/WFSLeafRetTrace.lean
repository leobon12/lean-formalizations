/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.LawUniqueTransfer
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.GFF.LocalSets.HittingSigma

/-!
# The retained trace set, read from a killed dyadic history

The reader takes the relative closure in `H` of the trace values at dyadic
times strictly before the recorded cutoff. At a terminal cutoff the reader
includes accumulation points in `H`; no endpoint continuity is assumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique LocalSets QuantumZipper

variable {nL nR : ℕ}

/-- The driving path decoded by limits of the dyadic samples from below. -/
def retainedDriver (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ :=
  limUnder atTop fun n => (γ.2 (lowerDyadic t n)).1

theorem measurable_retainedDriver :
    Measurable (retainedDriver (nL := nL) (nR := nR)) := by
  refine Measurable.of_eval fun t => ?_
  exact (StronglyMeasurable.limUnder fun n =>
    (((measurable_pi_apply (lowerDyadic t n)).comp measurable_snd).fst).stronglyMeasurable).measurable

/-- The retained trace set including its relative accumulation points at the cutoff. -/
def retainedTraceReader (γ : HistorySpace nL nR) : Set ℂ :=
  relClosureH {z | ∃ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < γ.1 ∧
    LP.traceAt (dyadicTime p) (retainedDriver γ) = z}

theorem measurable_retainedTraceReader :
    Measurable[inferInstance, hittingSigma] (retainedTraceReader (nL := nL) (nR := nR)) := by
  apply measurable_relClosureH.comp
  apply measurable_iff_comap_le.2
  rw [hittingSigma, MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨_, ⟨U, hU, _, rfl⟩, rfl⟩
  have heq : {γ : HistorySpace nL nR |
      ({z | ∃ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < γ.1 ∧
        LP.traceAt (dyadicTime p) (retainedDriver γ) = z} ∩ U).Nonempty} =
      ⋃ p : ℕ × ℕ, {γ | (dyadicTime p : ℝ≥0∞) < γ.1} ∩
        (fun γ => LP.traceAt (dyadicTime p) (retainedDriver γ)) ⁻¹' U := by
    ext γ
    simp only [mem_ofPred_eq, Set.Nonempty, mem_inter_iff, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨z, ⟨p, hp, rfl⟩, hz⟩
      exact ⟨p, hp, hz⟩
    · rintro ⟨p, hp, hz⟩
      exact ⟨_, ⟨p, hp, rfl⟩, hz⟩
  change MeasurableSet {γ : HistorySpace nL nR |
    ({z | ∃ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < γ.1 ∧
      LP.traceAt (dyadicTime p) (retainedDriver γ) = z} ∩ U).Nonempty}
  rw [heq]
  exact MeasurableSet.iUnion fun p => (measurableSet_lt measurable_const measurable_fst).inter
    (((LP.measurable_traceAt _).comp measurable_retainedDriver) hU.measurableSet)

theorem retainedTraceReader_geometry (γ : HistorySpace nL nR) :
    retainedTraceReader γ ⊆ H ∧ IsOpen (H \ retainedTraceReader γ) :=
  ⟨relClosureH_subset _, isOpen_H_diff_relClosureH _⟩

section Identification

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {ω : Ω}

/-- Decoding recovers the driving path strictly before the recorded cutoff. -/
theorem retainedDriver_killedHistory
    (hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hVζ : V ω ≤ ζ ω)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < V ω) :
    retainedDriver (killedHistory W VL VR V ω) t = W t ω := by
  have heq : (fun n => ((killedHistory W VL VR V ω).2 (lowerDyadic t n)).1) =
      fun n => W (dyadicTime (lowerDyadic t n)) ω := by
    funext n
    have hlt := lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le t n)) ht
    simp only [killedHistory, hlt, ↓reduceIte]
  unfold retainedDriver
  rw [heq]
  exact (tendsto_lowerDyadic_of_continuousOn hw (ht.trans_le hVζ)).limUnder_eq

/-- The decoded trace value is the actual trace value before the cutoff. -/
theorem traceAt_retainedDriver_killedHistory {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (W · ω) (ζ ω) η)
    (hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hw0 : W 0 ω = 0)
    (hVζ : V ω ≤ ζ ω) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < V ω) :
    LP.traceAt t (retainedDriver (killedHistory W VL VR V ω)) = η t := by
  rw [LP.traceAt_congr (w' := fun s => W s ω) fun r hr =>
    retainedDriver_killedHistory hw hVζ (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) ht)]
  exact LP.traceAt_eq_of_isGeneratingTrace hη hw hw0 (ht.trans_le hVζ)

/-- The reader is exactly the relative closure of the pre-cutoff trace range.
This also identifies the reader at infinite or terminal cutoffs. -/
theorem retainedTraceReader_killedHistory {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (W · ω) (ζ ω) η)
    (hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω}) (hw0 : W 0 ω = 0)
    (hVζ : V ω ≤ ζ ω) :
    retainedTraceReader (killedHistory W VL VR V ω) =
      relClosureH (η '' {t : ℝ≥0 | (t : ℝ≥0∞) < V ω}) := by
  let S : Set ℂ := {z | ∃ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < V ω ∧
    LP.traceAt (dyadicTime p) (retainedDriver (killedHistory W VL VR V ω)) = z}
  have hS : S ⊆ η '' {t : ℝ≥0 | (t : ℝ≥0∞) < V ω} := by
    rintro z ⟨p, hp, rfl⟩
    exact ⟨dyadicTime p, hp, (traceAt_retainedDriver_killedHistory hη hw hw0 hVζ hp).symm⟩
  have hηV : ContinuousOn η {t : ℝ≥0 | (t : ℝ≥0∞) < V ω} :=
    hη.2.1.mono fun t ht => (ht.trans_le hVζ).le
  have hback : (η '' {t : ℝ≥0 | (t : ℝ≥0∞) < V ω}) ∩ H ⊆ closure (S ∩ H) := by
    rintro z ⟨⟨t, ht, rfl⟩, hzH⟩
    have hlim := tendsto_lowerDyadic_of_continuousOn hηV ht
    apply isClosed_closure.mem_of_tendsto hlim
    filter_upwards [hlim.eventually (isOpen_H.mem_nhds hzH)] with n hn
    have hp := lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le t n)) ht
    exact subset_closure ⟨⟨lowerDyadic t n, hp,
      traceAt_retainedDriver_killedHistory hη hw hw0 hVζ hp⟩, hn⟩
  change relClosureH S = _
  unfold relClosureH
  congr 1
  exact Subset.antisymm (closure_mono (inter_subset_inter_left H hS))
    (closure_minimal hback isClosed_closure)

end Identification

end InteractingSLE.WFS
