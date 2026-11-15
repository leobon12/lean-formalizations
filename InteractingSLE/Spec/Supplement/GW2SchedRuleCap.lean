/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SchedRuleSigma
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# GW2's schedule prefixes, their joint-chart images and relative capacity

Packet PROVE-GW2-SCHED. Follow-up note A.5 (`source/external/AstraIG1/ig1_followup_a_e_audited.txt` L222–L241): "On
perpetual success infinitely many increments are at least one. Relative capacity is therefore unbounded. A bounded
relative trace range would bound its filled hull in a rectangle, and hence bound its half-plane capacity. The selected
ranges are consequently unbounded in the joint chart"; "Every successful finite history uses only `Θ` and `Q`.
Canonical field determination and consistency identify it with a member of the originally fixed countable family".

This file supplies the capacity bookkeeping of the schedule rule (`GW2TipSystem.SchedRule.IsValid`'s `hcapMono` and
`hcapB`), deterministically:

* `prefixSet`: the physical set of a schedule's canonical pieces (`GW2Tip.canonSpecFam`); **`prefixSet_subset_family`**:
  for a `Θ`-schedule with times in `Q` from `0` or a root of the first low right arc it lies in GW2's light-cone family
  (`boundaryLightConeFamily`, the frozen definition);
* `prefixImage`: its joint-chart image off the counterflow hull; **`prefixImage_subset_jointTarget`**;
* `capOf`: half the capacity of the filling of a bounded attached set (`0` otherwise), with **`capOf_le_of_subset`**
  (`hcap(fill A) ≤ ρ²` for `A ⊆ B̄(0, ρ)`);
* `schedCap`: the relative capacity of a schedule, the running maximum of `capOf` over its initial segments (equal to
  the capacity of its prefix image whenever the latter increases, and monotone along extensions by construction):
  **`schedCap_le_cons`** (`hcapMono`) and **`schedCap_le_of_subset`** (`hcapB`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2TipSystem

open GW2Schedule GW2Cone GW2Later GW2Tip GW2TipStage Exist Staged StagedLaw Restart LQGMetric

/-! ### Capacity of a set -/

/-- Half the half-plane capacity of the filling of a bounded set attached to the real line (`A ∪ {Im ≤ 0}`
preconnected); `0` otherwise. -/
def capOf (A : Set ℂ) : ℝ :=
  open scoped Classical in
  if hA : Bornology.IsBounded A ∧ IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) then hcapFill A hA.1 hA.2 / 2 else 0

/-- **The capacity of a set inside a closed disc of radius `ρ` about `0` is at most `2ρ²`** (A.5: "A bounded relative
trace range would bound its filled hull … and hence bound its half-plane capacity"; [Law05] (3.8)). -/
theorem capOf_le_of_subset {A : Set ℂ} {ρ : ℝ} (hA : A ⊆ Metric.closedBall 0 ρ) : capOf A ≤ 2 * ρ ^ 2 := by
  unfold capOf
  split_ifs with h
  · have h1 : hcapFill A h.1 h.2 ≤ ρ ^ 2 :=
      hcapFill_le_sq_of_subset_closedBall h.1 h.2 (x := 0) (by simpa using hA)
    nlinarith [sq_nonneg ρ]
  · positivity

/-! ### Prefixes of schedules and the light-cone family -/

section Prefix

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)

/-- **The physical set of a schedule's canonical pieces** (the frozen `ExplState.physSet` of the history
`schedSpec x l` with the canonical pieces of the field sample `ω`). -/
def prefixSet (x : ℝ) (l : List (ℝ × ℝ≥0)) (ω : Ω) : Set ℂ :=
  ExplState.physSet κ b jumps (schedSpec x l) (fun k => canonSpecFam hκ h12p βA c₀ h (schedSpec x l) k ω)

/-- **A schedule's prefix lies in GW2's light-cone family** when it is a `Θ`-schedule with times in `Q` from the root
`0` or from a root of the first low right arc (the frozen `boundaryLightConeFamily`). -/
theorem prefixSet_subset_family {Θ : Set ℝ} {Q : Set ℝ≥0} {x : ℝ} (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps)
    {l : List (ℝ × ℝ≥0)} (hl : IsSchedule Θ Q l) (ω : Ω) :
    prefixSet hκ h12p βA b jumps c₀ h x l ω ⊆
      boundaryLightConeFamily κ b jumps Θ Q (fun spec k => canonSpecFam hκ h12p βA c₀ h spec k ω) := by
  intro z hz
  unfold boundaryLightConeFamily
  rcases hx with rfl | hv
  · exact Or.inl (mem_iUnion₂.2 ⟨l, hl, hz⟩)
  · exact Or.inr (mem_iUnion₂.2 ⟨x, hv, Or.inr (mem_iUnion₂.2 ⟨l, hl, hz⟩)⟩)

/-- **The joint-chart image of a schedule's prefix off the counterflow hull at `s`** (the chart of
`GW2TipStage.jointTarget`). -/
def prefixImage (W' : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (x : ℝ) (l : List (ℝ × ℝ≥0)) (ω : Ω) : Set ℂ :=
  (GW2JointKernel.jointChart (fun r : ℝ => W' r.toNNReal ω) s).1 ''
    (prefixSet hκ h12p βA b jumps c₀ h x l ω ∩
      (fun z : ℂ => -z⁻¹) '' (H \ QuantumZipper.fwdHull (fun r : ℝ => W' r.toNNReal ω) s))

/-- **The image of a schedule's prefix lies in the joint target** (`GW2TipStage.jointTarget`). -/
theorem prefixImage_subset_jointTarget {Θ : Set ℝ} {Q : Set ℝ≥0} (W' : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) {x : ℝ}
    (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)} (hl : IsSchedule Θ Q l) (ω : Ω) :
    prefixImage hκ h12p βA b jumps c₀ h W' s x l ω ⊆ jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s ω := by
  unfold prefixImage jointTarget
  exact image_mono (inter_subset_inter_left _ (prefixSet_subset_family hκ h12p βA b jumps c₀ h hx hl ω))

end Prefix

/-! ### The relative capacity of a schedule -/

section Cap

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u}) (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (b : ℝ → ℝ) (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u} (h : Ω → DistOn upperHalfPlaneOpens)
  (W' : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (Θ : Set ℝ) (Q : Set ℝ≥0)

/-- The schedule `schedOf e₀ xs` from the root `x` is admissible for the family: a `Θ`-schedule with times in `Q` from
`0` or a root of the first low right arc. -/
def SchedAdm (x : ℝ) (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) : Prop :=
  (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) ∧ IsSchedule Θ Q (schedOf e₀ xs)

/-- The capacity of the prefix image of one schedule (`0` if the schedule is not admissible). -/
def capV (x : ℝ) (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) (ω : Ω) : ℝ :=
  open scoped Classical in
  if SchedAdm b jumps Θ Q (κ := κ) x e₀ xs then
    capOf (prefixImage hκ h12p βA b jumps c₀ h W' s x (schedOf e₀ xs) ω) else 0

/-- **The relative capacity of a schedule**: the running maximum, over its initial segments, of the capacity of their
prefix images (latest entry first). -/
def schedCap (x : ℝ) (e₀ : ℝ × ℝ≥0) : List (ℝ × ℝ≥0) → Ω → ℝ
  | [], ω => capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ [] ω
  | y :: xs, ω => max (schedCap x e₀ xs ω) (capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ (y :: xs) ω)

/-- **The relative capacity increases along extensions** (field `hcapMono` of `SchedRule.IsValid`). -/
theorem schedCap_le_cons (x : ℝ) (e₀ y : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) (ω : Ω) :
    schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω ≤ schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ (y :: xs) ω :=
  le_max_left _ _

/-- The capacity of one schedule is at most `2ρ²` when the joint target lies in `B̄(0, ρ)`. -/
theorem capV_le_of_subset (x : ℝ) (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) {ω : Ω} {ρ : ℝ}
    (hS : jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s ω ⊆ Metric.closedBall 0 ρ) :
    capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω ≤ 2 * ρ ^ 2 := by
  unfold capV
  split_ifs with hadm
  · exact capOf_le_of_subset
      ((prefixImage_subset_jointTarget hκ h12p βA b jumps c₀ h W' s hadm.1 hadm.2 ω).trans hS)
  · positivity

/-- **The relative capacity is at most `2ρ²` when the joint target lies in `B̄(0, ρ)`** (field `hcapB` of
`SchedRule.IsValid`; A.5: "A bounded relative trace range would bound its filled hull in a rectangle, and hence bound
its half-plane capacity"). -/
theorem schedCap_le_of_subset (x : ℝ) (e₀ : ℝ × ℝ≥0) :
    ∀ (xs : List (ℝ × ℝ≥0)) {ω : Ω} {ρ : ℝ},
      jointTarget hκ h12p βA b jumps c₀ h W' Θ Q s ω ⊆ Metric.closedBall 0 ρ →
        schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω ≤ 2 * ρ ^ 2
  | [], _, _, hS => capV_le_of_subset hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ [] hS
  | y :: xs, _, _, hS => max_le (schedCap_le_of_subset x e₀ xs hS)
      (capV_le_of_subset hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ (y :: xs) hS)

/-- The relative capacity of a schedule is at least the capacity of its own prefix image. -/
theorem capV_le_schedCap (x : ℝ) (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) (ω : Ω) :
    capV hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω ≤ schedCap hκ h12p βA b jumps c₀ h W' s Θ Q x e₀ xs ω := by
  cases xs with
  | nil => exact le_rfl
  | cons y xs => exact le_max_right _ _

end Cap

end GW2TipSystem

end Theorem14

end InteractingSLE
