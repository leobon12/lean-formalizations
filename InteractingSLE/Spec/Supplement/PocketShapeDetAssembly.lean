/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeDetChart

/-!
# The pocket-shape reduction after the ordered-contact argument

Packet PROVE-POCKETSHAPE. Non-overlap and the unbounded chart-endpoint assertion are
proved in the preceding files. Two geometric obligations remain explicitly named here:
extracting a shape from the original hypotheses, and excluding the entry as the limit
at zero of a bounded component chart. The conditional results in this file do not
discharge either obligation or claim an unconditional `PocketShapeDetStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.PocketShapeDet

open GW4Reg GW4BarrierSelf

/-- Outstanding deterministic obligation: extract the two wall intervals, with their
finite or infinite terminal parameters, from the hypotheses of `PocketShapeDetStatement`.
This is an input to the conditional reduction, not a proved theorem. -/
def PocketShapeExistenceStatement : Prop :=
  ∀ αR αL : ℝ≥0 → ℂ, GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) →
    (∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL) →
    Disjoint (range αL) (rightSideOf (range αR)) → Disjoint (range αR) (leftSideOf (range αL)) →
    (∀ C ∈ betweenComponents (range αR) (range αL),
      GW3.IsTwoArcJordanComponent (range αR) (range αL) C ∨
      GW3.HasOrientedUniformizer (range αR) (range αL) C) →
    ∀ C ∈ betweenComponents (range αR) (range αL),
      ∃ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v

/-- Outstanding bounded orientation obligation: the entry is not the limit at zero of
a component chart of a shaped pocket. The complementary unbounded assertion is proved by
`chart_zero_eq_exit_of_unbounded`. -/
def BoundedChartEntryExclusionStatement : Prop :=
  ∀ αR αL : ℝ≥0 → ℂ, GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) →
    ∀ C ∈ betweenComponents (range αR) (range αL),
      ∀ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v → u ≠ ⊤ →
        ∀ c : Chart, IsComponentChart (range αR) (range αL) C c →
          ¬ Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR u.toNNReal))

/-- Given existence of shapes, bounded entry exclusion supplies the only remaining
chart-endpoint case. Non-overlap is an unconditional consequence of the shaped geometry. -/
theorem walkPocketShape_of_existence_of_entry_exclusion
    {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    (hS : ∀ C ∈ betweenComponents (range αR) (range αL),
      ∃ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v)
    (hE : BoundedChartEntryExclusionStatement) : WalkPocketShape αR αL := by
  refine ⟨hS, ?_, ?_⟩
  · intro C hC s t u v hs c hc p hp
    rcases chart_zero_eq_endpoint hR hL hord hC hs hc hp with he | ⟨hu, he⟩
    · exact he
    · exact (hE αR αL hR hL hord C hC s t u v hs hu c hc (he ▸ hp)).elim
  · intro C hC D hD hne s t u v s' t' u' v' hs hs'
    exact nonoverlap hR hL hord hC hD hne hs hs'

/-- Conditional reduction of the packet's exact target to the two outstanding geometric
obligations. The original `PocketShapeDetStatement` is unchanged. -/
theorem pocketShapeDetStatement_of_existence_of_entry_exclusion
    (hS : PocketShapeExistenceStatement) (hE : BoundedChartEntryExclusionStatement) :
    GW4Leaf.PocketShapeDetStatement := by
  intro αR αL hR hL hord hno hLR hRL hG
  exact walkPocketShape_of_existence_of_entry_exclusion hR hL hord
    (hS αR αL hR hL hord hno hLR hRL hG) hE

/-- The same explicit deterministic obligations in the existing almost-sure wiring. -/
theorem walkPocketShapeRegStatement_of_existence_of_entry_exclusion
    (hS : PocketShapeExistenceStatement) (hE : BoundedChartEntryExclusionStatement)
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} :=
  GW4Leaf.walkPocketShapeRegStatement_of_det
    (pocketShapeDetStatement_of_existence_of_entry_exclusion hS hE) hCO hNC hSB hA hGeom

end InteractingSLE.Theorem14.PocketShapeDet
