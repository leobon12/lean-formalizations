/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TestCross

/-!
# Alive and unit events for GW2's repaired root tests

Packet PROVE-GW2-TEST. Alive events remember passed tests on each prefix; unit
events are the actual increase of the regularized capacity. Their structural
claims follow from observable tests and measurable capacity. Neither capacity
measurability nor the retained stage law is asserted here without a proof.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem

namespace TestEvents

section Tree

variable {Ω Θ Q : Type*}

/-- Alive means that every earlier switch passed a test with its prescribed
angle, for some buffer parameter. Lists have the most recent switch first. -/
def aliveTests (G : Set Ω) (ang : ℕ → Θ)
    (T : List (Θ × Q) → ℕ → Q → Set Ω) : List (Θ × Q) → Set Ω
  | [] => G
  | x :: l => aliveTests G ang T l ∩ ⋃ a, ⋃ (_ : ang a = x.1), T l a x.2

/-- A unit is an increase of at least one in the actual capacity. There is no
unit to check at the empty schedule. -/
def capacityUnit (cap : List (Θ × Q) → Ω → ℝ) : List (Θ × Q) → Set Ω
  | [] => ∅
  | x :: l => {ω | cap l ω + 1 ≤ cap (x :: l) ω}

/-- A passed test extends the alive event. -/
theorem aliveTests_inter_subset {G : Set Ω} {ang : ℕ → Θ}
    {T : List (Θ × Q) → ℕ → Q → Set Ω} (l : List (Θ × Q)) (a : ℕ) (q : Q) :
    aliveTests G ang T l ∩ T l a q ⊆ aliveTests G ang T ((ang a, q) :: l) := by
  rintro ω ⟨hωA, hωT⟩
  exact ⟨hωA, mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨rfl, hωT⟩⟩⟩

variable {σ : List (Θ × Q) → MeasurableSpace Ω}

/-- Observable tests give observable alive events by induction over a schedule.
Only the completed pieces enter the conditioning sigma-algebra. -/
theorem measurableSet_aliveTests (hmono : ∀ l x, σ l ≤ σ (x :: l))
    {G : Set Ω} (hG : MeasurableSet[σ []] G) {ang : ℕ → Θ}
    {T : List (Θ × Q) → ℕ → Q → Set Ω}
    (hT : ∀ l a q, MeasurableSet[σ ((ang a, q) :: l)] (T l a q))
    (l : List (Θ × Q)) : MeasurableSet[σ l] (aliveTests G ang T l) := by
  induction l with
  | nil => exact hG
  | cons x l ih =>
    refine (hmono l x _ ih).inter (MeasurableSet.iUnion fun a =>
      MeasurableSet.iUnion fun ha => ?_)
    have he : (ang a, x.2) = x := Prod.ext ha rfl
    exact he ▸ hT l a x.2

/-- Measurable capacities give observable unit events. The previous capacity
is measurable in the extended record by monotonicity of the past. -/
theorem measurableSet_capacityUnit (hmono : ∀ l x, σ l ≤ σ (x :: l))
    {cap : List (Θ × Q) → Ω → ℝ} (hcap : ∀ l, Measurable[σ l] (cap l))
    (l : List (Θ × Q)) : MeasurableSet[σ l] (capacityUnit cap l) := by
  cases l with
  | nil => exact @MeasurableSet.empty Ω (σ [])
  | cons x l =>
    let : MeasurableSpace Ω := σ (x :: l)
    exact measurableSet_le (((hcap l).mono (hmono l x) le_rfl).add_const 1)
      (hcap (x :: l))

end Tree

end TestEvents

end InteractingSLE.Theorem14.GW2TipSystem
