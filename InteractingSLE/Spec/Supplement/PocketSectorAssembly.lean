/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketSectorGap

/-!
# The two remaining pocket-shape obligations for strictly interior walls

PROVE-POCKETSHAPE continuation. The sector-map transport removes real connectors
from both remaining obligations. The two propositions below remain unproved
geometric inputs to distinctly named conditional results. The shape input omits
the global side assumptions, so it is explicitly a stronger sufficient input.
No source theorem or frozen declaration is changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Function
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.PocketSector

open GW4Reg GW4BarrierSelf GW3SidedProof

/-- The remaining shape-extraction input for strictly interior proper walls.
The global side assumptions of `PocketShapeFin.UniformizerShapeStatement` are
omitted here: this is a stronger sufficient auxiliary input, not a proved theorem. -/
def InteriorUniformizerShapeStatement : Prop :=
  ∀ αR αL : ℝ≥0 → ℂ, Sec7.Lemma71I.IsSimpleProper αR → Sec7.Lemma71I.IsSimpleProper αL →
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) →
    (∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL) →
    ∀ C ∈ betweenComponents (range αR) (range αL),
      GW3.HasOrientedUniformizer (range αR) (range αL) C →
        ∃ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v

/-- The remaining bounded positive-boundary order input, restricted to walls in
`ℍ` at positive times. This proposition is not discharged here. -/
def InteriorBoundedPositiveBoundaryOrderStatement : Prop :=
  ∀ αR αL : ℝ≥0 → ℂ, Sec7.Lemma71I.IsSimpleProper αR → Sec7.Lemma71I.IsSimpleProper αL →
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) →
    ∀ C ∈ betweenComponents (range αR) (range αL),
      ∀ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v → u ≠ ⊤ →
        ∀ c : Chart, IsComponentChart (range αR) (range αL) C c →
          ∀ (x y : ℝ) (r q : ℝ≥0), 0 < x → x < y →
            Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (αR r)) →
            Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝 (αR q)) → r < q

/-- Shape extraction for interior walls suffices for the original uniformizer alternative. -/
theorem uniformizerShapeStatement_of_interior
    (hU : InteriorUniformizerShapeStatement) : PocketShapeFin.UniformizerShapeStatement := by
  intro αR αL hR hL hord hno _hLR _hRL C hC hG
  have hord' : ∀ s s' t t' : ℝ≥0,
      (sectorMap ∘ αR) s = (sectorMap ∘ αL) t →
      (sectorMap ∘ αR) s' = (sectorMap ∘ αL) t' → (s < s' ↔ t < t') :=
    fun s s' t t' h h' => hord s s' t t' (sectorMap_injective h) (sectorMap_injective h')
  have hno' : ∀ a b : ℝ≥0, a < b →
      ¬ (sectorMap ∘ αR) '' Icc a b ⊆ range (sectorMap ∘ αL) := by
    intro a b hab hsub
    apply hno a b hab
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨t, ht⟩ := hsub ⟨r, hr, rfl⟩
    exact ⟨t, sectorMap_injective ht⟩
  obtain ⟨s, t, u, v, hs⟩ := hU (sectorMap ∘ αR) (sectorMap ∘ αL)
    (isSimpleProper_sector hR) (isSimpleProper_sector hL) hord' hno'
    (sectorMap '' C) (image_mem_between hR hL hC) (hasOrientedUniformizer_sector_image hR hL hC hG)
  exact ⟨s, t, u, v, shape_of_sector_image hR hL hC hs⟩

/-- Bounded positive-boundary order for interior walls suffices also with real connectors. -/
theorem boundedPositiveBoundaryOrderStatement_of_interior
    (hB : InteriorBoundedPositiveBoundaryOrderStatement) :
    PocketShapeFin.BoundedPositiveBoundaryOrderStatement := by
  intro αR αL hR hL hord C hC s t u v hs hu c hc x y r q hx hxy hr hq
  obtain ⟨d, hd, heq⟩ := exists_sector_chart hR hL hC hc
  have hord' : ∀ s s' t t' : ℝ≥0,
      (sectorMap ∘ αR) s = (sectorMap ∘ αL) t →
      (sectorMap ∘ αR) s' = (sectorMap ∘ αL) t' → (s < s' ↔ t < t') :=
    fun s s' t t' h h' => hord s s' t t' (sectorMap_injective h) (sectorMap_injective h')
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  apply hB (sectorMap ∘ αR) (sectorMap ∘ αL) (isSimpleProper_sector hR) (isSimpleProper_sector hL)
    hord' (sectorMap '' C) (image_mem_between hR hL hC) s t u v (shape_sector_image hR hL hC hs)
    hu d hd x y r q hx hxy
  · exact (tendsto_sectorMap_comp hCH hc.2.2.1 hr).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (heq hz).symm)
  · exact (tendsto_sectorMap_comp hCH hc.2.2.1 hq).congr'
      (eventually_nhdsWithin_of_forall fun z hz => (heq hz).symm)

/-- The interior version of bounded boundary order is equivalent to the original version. -/
theorem boundedPositiveBoundaryOrderStatement_iff_interior :
    PocketShapeFin.BoundedPositiveBoundaryOrderStatement ↔
      InteriorBoundedPositiveBoundaryOrderStatement := by
  refine ⟨?_, boundedPositiveBoundaryOrderStatement_of_interior⟩
  intro hB αR αL hR hL
  exact hB αR αL (isCompleteSimpleFlow_of_isSimpleProper hR) (isCompleteSimpleFlow_of_isSimpleProper hL)

/-- The unchanged deterministic target from the two explicitly outstanding interior inputs. -/
theorem pocketShapeDetStatement_of_interior
    (hU : InteriorUniformizerShapeStatement) (hB : InteriorBoundedPositiveBoundaryOrderStatement) :
    GW4Leaf.PocketShapeDetStatement :=
  PocketShapeFin.pocketShapeDetStatement_of_uniformizer_of_positive_order
    (uniformizerShapeStatement_of_interior hU) (boundedPositiveBoundaryOrderStatement_of_interior hB)

/-- The almost-sure consequence of the same outstanding interior inputs. -/
theorem walkPocketShapeRegStatement_of_interior
    (hU : InteriorUniformizerShapeStatement) (hB : InteriorBoundedPositiveBoundaryOrderStatement)
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} :=
  GW4Leaf.walkPocketShapeRegStatement_of_det (pocketShapeDetStatement_of_interior hU hB)
    hCO hNC hSB hA hGeom

end InteractingSLE.Theorem14.PocketSector
