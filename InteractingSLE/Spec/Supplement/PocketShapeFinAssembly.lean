/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeFinOrientation

/-!
# Pocket shapes after the bounded Jordan case

PROVE-POCKETSHAPE continuation. Shape existence is proved for the two-arc Jordan
alternative. The remaining uniformizer alternative and the local positive-boundary order
are the explicit inputs below; the original target is not changed or claimed proved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.PocketShapeFin

open GW4Reg GW4BarrierSelf PocketShapeDet

/-- Outstanding shape-extraction obligation for the uniformizer alternative only.
The bounded two-arc alternative is proved by `exists_isPocketShape_of_twoArcJordan`. -/
def UniformizerShapeStatement : Prop :=
  ∀ αR αL : ℝ≥0 → ℂ, GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) →
    (∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL) →
    Disjoint (range αL) (rightSideOf (range αR)) → Disjoint (range αR) (leftSideOf (range αL)) →
    ∀ C ∈ betweenComponents (range αR) (range αL),
      GW3.HasOrientedUniformizer (range αR) (range αL) C →
        ∃ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v

/-- Shape existence after discharging the entire bounded two-arc Jordan alternative. -/
theorem pocketShapeExistenceStatement_of_uniformizer
    (hU : UniformizerShapeStatement) : PocketShapeExistenceStatement := by
  intro αR αL hR hL hord hno hLR hRL hG C hC
  rcases hG C hC with hG | hG
  · obtain ⟨s, t, u, v, hs⟩ := exists_isPocketShape_of_twoArcJordan hR hL hord hG
    exact ⟨s, t, (u : ℝ≥0∞), (v : ℝ≥0∞), hs⟩
  · exact hU αR αL hR hL hord hno hLR hRL C hC hG

/-- The exact original deterministic target from the two remaining local geometric inputs. -/
theorem pocketShapeDetStatement_of_uniformizer_of_positive_order
    (hU : UniformizerShapeStatement) (hB : BoundedPositiveBoundaryOrderStatement) :
    GW4Leaf.PocketShapeDetStatement :=
  pocketShapeDetStatement_of_existence_of_entry_exclusion
    (pocketShapeExistenceStatement_of_uniformizer hU)
    (boundedChartEntryExclusionStatement_of_positive_order hB)

/-- The existing almost-sure consequence with the same two explicit remaining obligations. -/
theorem walkPocketShapeRegStatement_of_uniformizer_of_positive_order
    (hU : UniformizerShapeStatement) (hB : BoundedPositiveBoundaryOrderStatement)
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} :=
  GW4Leaf.walkPocketShapeRegStatement_of_det
    (pocketShapeDetStatement_of_uniformizer_of_positive_order hU hB) hCO hNC hSB hA hGeom

end InteractingSLE.Theorem14.PocketShapeFin
