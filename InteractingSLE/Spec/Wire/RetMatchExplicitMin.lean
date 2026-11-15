/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchMeyerWire
import InteractingSLE.Spec.Exist.Param12Sampled
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Attained minima of raw stopping times

A countable minimum, returned as infinity when it is not attained, is a raw
stopping time. The minimizing event is measurable at the candidate time.
This avoids the right-continuity premise of the usual countable-infimum lemma.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchExplicit

open Classical in
/-- The minimum of a sequence when attained, and infinity otherwise. -/
def attainedMin {α : Type*} [LinearOrder α] [OrderTop α] (r : ℕ → α) : α :=
  if h : ∃ k, ∀ j, r k ≤ r j then r (Classical.choose h) else ⊤

theorem attainedMin_eq_of_min {α : Type*} [LinearOrder α] [OrderTop α]
    {r : ℕ → α} {k : ℕ} (hk : ∀ j, r k ≤ r j) : attainedMin r = r k := by
  unfold attainedMin
  split_ifs with h
  · exact le_antisymm (Classical.choose_spec h k) (hk _)
  · exact (h ⟨k, hk⟩).elim

/-- An attained countable minimum is stopping even in a raw filtration. -/
theorem isStoppingTime_attainedMin {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {r : ℕ → Ω → WithTop ℝ≥0}
    (hr : ∀ k, IsStoppingTime 𝓕 (r k)) :
    IsStoppingTime 𝓕 (fun ω => attainedMin (fun k => r k ω)) := by
  classical
  intro t
  have heq : {ω | attainedMin (fun k => r k ω) ≤ t} =
      ⋃ k, {ω | ∀ j, r k ω ≤ r j ω} ∩ {ω | r k ω ≤ t} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro hle
      by_cases h : ∃ k, ∀ j, r k ω ≤ r j ω
      · exact ⟨Classical.choose h, Classical.choose_spec h,
          (attainedMin_eq_of_min (r := fun j => r j ω) (Classical.choose_spec h)) ▸ hle⟩
      · have htop : attainedMin (fun k => r k ω) = ⊤ := by
          unfold attainedMin
          exact dite_eq_right h
        exact (not_le_of_gt (WithTop.coe_lt_top t) (htop ▸ hle)).elim
    · rintro ⟨k, hk, hkt⟩
      exact (attainedMin_eq_of_min hk).trans_le hkt
  rw [heq]
  apply MeasurableSet.iUnion
  intro k
  have hk : MeasurableSet[(hr k).measurableSpace] {ω | ∀ j, r k ω ≤ r j ω} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun j => (hr k).measurableSet_le_stopping_time (hr j)
  exact (((hr k).measurableSet _).1 hk).2 t

/-- A convergent ordered sequence with one value below its limit attains
its minimum: all sufficiently late values exceed that one value. -/
theorem exists_min_of_tendsto {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {r : ℕ → α} {v : α} (hv : Tendsto r atTop (𝓝 v))
    (hbelow : ∃ k, r k < v) : ∃ k, ∀ j, r k ≤ r j := by
  obtain ⟨k, hk⟩ := hbelow
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hv.eventually (Ioi_mem_nhds hk))
  let K := max N (k + 1)
  have hkK : k ∈ Finset.range K :=
    Finset.mem_range.2 ((Nat.lt_succ_self k).trans_le (le_max_right _ _))
  obtain ⟨m, hm, hmin⟩ := (Finset.range K).exists_min_image r ⟨k, hkK⟩
  refine ⟨m, fun j => ?_⟩
  by_cases hj : j < K
  · exact hmin j (Finset.mem_range.2 hj)
  · exact (hmin k hkK).trans (hN j ((le_max_left _ _).trans (not_lt.1 hj))).le

end InteractingSLE.Wire.RetMatchExplicit
