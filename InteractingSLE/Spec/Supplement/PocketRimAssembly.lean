/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketRimChart

/-!
# Pocket shapes from one local disc-side input

PROVE-POCKETSHAPE continuation. Endpoint extraction and the local identification
of components on the same side are proved. The explicit remaining shape input
is now a planar assertion about the side of a single contact-gap pocket.
This is an unproved input to distinctly named conditional results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

universe u

namespace InteractingSLE.Theorem14.PocketRim

open GW4Reg GW4BarrierSelf WangWu Sec7.Lemma71I

/-- Outstanding local planar input: if an open right-wall gap point is below the
other crosscut, its Jordan pocket is above the right crosscut. This is not proved
here. It has no global side-order or uniformizer premise. -/
def DiscGapSideStatement : Prop :=
  ∀ α β : ℝ → ℂ, IsDiscCrosscut α → IsDiscCrosscut β →
    StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β) →
    ∀ a b : ℝ, IsContactGap α β a b → ∀ c ∈ Ioo a b,
      α c ∈ crossSide β (-1) → jordanIn (pocketCurve α β a b) ⊆ crossSide α 1

/-- Outstanding orientation input: whenever a bounded interior shaped pocket has
a component chart, choose one chart with increasing positive boundary order.
The chart comparison theorem then handles every other chart. This input is unproved. -/
def OneInteriorChartBoundaryOrderStatement : Prop :=
  ∀ αR αL : ℝ≥0 → ℂ, IsSimpleProper αR → IsSimpleProper αL →
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) →
    ∀ C ∈ betweenComponents (range αR) (range αL),
      ∀ (s t : ℝ≥0) (u v : ℝ≥0∞), IsPocketShape αR αL C s t u v → u ≠ ⊤ →
        (∃ c : Chart, IsComponentChart (range αR) (range αL) C c) →
          ∃ d : Chart, IsComponentChart (range αR) (range αL) C d ∧
            ∀ (x y : ℝ) (r q : ℝ≥0), 0 < x → x < y →
              Tendsto d.2.1 (𝓝[H] (x : ℂ)) (𝓝 (αR r)) →
              Tendsto d.2.1 (𝓝[H] (y : ℂ)) (𝓝 (αR q)) → r < q

/-- Constructing one ordered chart is equivalent to proving order for every component chart. -/
theorem oneInteriorChartBoundaryOrderStatement_iff :
    OneInteriorChartBoundaryOrderStatement ↔ PocketSector.InteriorBoundedPositiveBoundaryOrderStatement := by
  constructor
  · intro hOne αR αL hR hL hord C hC s t u v hs hu c hc
    obtain ⟨d, hd, horder⟩ := hOne αR αL hR hL hord C hC s t u v hs hu ⟨c, hc⟩
    exact positive_boundary_order_of_bounded_shape_chart
      (PocketSector.isCompleteSimpleFlow_of_isSimpleProper hR)
      (PocketSector.isCompleteSimpleFlow_of_isSimpleProper hL) hord hC hs hu hc hd horder
  · intro hB αR αL hR hL hord C hC s t u v hs hu hcharts
    obtain ⟨c, hc⟩ := hcharts
    exact ⟨c, hc, hB αR αL hR hL hord C hC s t u v hs hu c hc⟩

/-- The local side input identifies an oriented between-component with a contact-gap pocket. -/
theorem exists_cayley_contactGap_of_discGapSide (hSide : DiscGapSideStatement)
    {αR αL : ℝ≥0 → ℂ} (hR : IsSimpleProper αR) (hL : IsSimpleProper αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    (hno : ∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    (hU : GW3.HasOrientedUniformizer (range αR) (range αL) C) :
    ∃ a b : ℝ, IsContactGap (toDisc (realPath αR)) (toDisc (realPath αL)) a b ∧
      cayley '' C = jordanIn (pocketCurve (toDisc (realPath αR)) (toDisc (realPath αL)) a b) := by
  let α := toDisc (realPath αR)
  let β := toDisc (realPath αL)
  have hα : IsDiscCrosscut α := hR.isProperArc.isDiscCrosscut_toDisc
  have hβ : IsDiscCrosscut β := hL.isProperArc.isDiscCrosscut_toDisc
  have hRb := PocketSector.isCompleteSimpleFlow_of_isSimpleProper hR
  have hLb := PocketSector.isCompleteSimpleFlow_of_isSimpleProper hL
  obtain ⟨r, hrfr, hroff⟩ := PocketSector.exists_right_wall_frontier_off_left hRb hLb hno hC hU
  have hrpos : 0 < r := lt_of_le_of_ne (show (0 : ℝ≥0) ≤ r from zero_le) fun he => hroff (by
    rw [← he, hR.2.2.1]
    exact ⟨0, hL.2.2.1⟩)
  let c := discTime (r : ℝ)
  have hcp : α c = cayley (αR r) := by
    exact Sec7.PocketCoord.toDisc_realPath_discTime αR r
  have hpD : α c ∈ ball (0 : ℂ) 1 := by
    rw [hcp]
    exact QuantumZipper.CA.cayley_mem_ball (hR.2.2.2.1 r hrpos)
  have hpβ : α c ∉ crossRange β := by
    rw [hcp]
    intro h
    have hmem := (hL.isProperArc.cayley_mem_crossRange_iff (hRb.2.2.2.1 r)).1 h
    rw [arcRange_realPath] at hmem
    exact hroff hmem
  obtain ⟨a, b, hg, hc⟩ := PocketSector.exists_disc_contactGap_at_right hR hL hroff
  have hinc := PocketSector.strictMonoOn_disc_contactMap hR hL hord
  obtain ⟨hJ, -, -, hPfr, w, -, hwP⟩ := Sec7.PocketCoord.pocket_props_of_strictMono hα hβ hinc hg
  obtain ⟨z, hDz, hDs⟩ := cayley_between_component hR hL hC
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hRb) (isClosed_range_of_isCompleteSimpleFlow hLb) hC
  have hCH : C ⊆ H := fun q hq => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hq).1
  have hpcl : α c ∈ closure (cayley '' C) := by
    rw [hcp]
    exact frontier_subset_closure (Sec7.Lemma71F.cayley_mem_frontier hCo hCH hrfr)
  have hpβside : α c ∈ crossSide β (-1) := mem_crossSide_of_mem_closure hβ (Or.inr rfl) hpD hpβ
    (closure_mono (fun q hq => (hDs hq).2) hpcl)
  have hPside := hSide α β hα hβ hinc a b hg c hc hpβside
  have hpP : α c ∈ closure (jordanIn (pocketCurve α β a b)) := by
    apply frontier_subset_closure
    rw [hPfr]
    exact Or.inl ⟨c, Ioo_subset_Icc_self hc, rfl⟩
  have hcomp : connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) z =
      connectedComponentIn (ball 0 1 \ (crossRange α ∪ crossRange β)) w := by
    apply component_eq_of_same_side_closure hα hβ
    · rw [← hDz]
      exact fun q hq => (hDs hq).1
    · rw [hwP]
      exact hPside
    · rw [← hDz]
      exact hpcl
    · rw [hwP]
      exact hpP
    · exact hpβ
  exact ⟨a, b, hg, hDz.trans (hcomp.trans hwP)⟩

/-- Shape extraction for the uniformizer alternative from the local disc-side input. -/
theorem interiorUniformizerShapeStatement_of_discGapSide (hSide : DiscGapSideStatement) :
    PocketSector.InteriorUniformizerShapeStatement := by
  intro αR αL hR hL hord hno C hC hU
  obtain ⟨a, b, hg, hEq⟩ := exists_cayley_contactGap_of_discGapSide hSide hR hL hord hno hC hU
  exact exists_isPocketShape_of_cayley_contactGap hR hL hord hC hg hEq

/-- The unchanged deterministic target from the explicit local side and bounded-order inputs. -/
theorem pocketShapeDetStatement_of_discGapSide
    (hSide : DiscGapSideStatement) (hB : PocketSector.InteriorBoundedPositiveBoundaryOrderStatement) :
    GW4Leaf.PocketShapeDetStatement :=
  PocketSector.pocketShapeDetStatement_of_interior
    (interiorUniformizerShapeStatement_of_discGapSide hSide) hB

/-- The almost-sure consequence from the same two explicitly unproved geometric inputs. -/
theorem walkPocketShapeRegStatement_of_discGapSide
    (hSide : DiscGapSideStatement) (hB : PocketSector.InteriorBoundedPositiveBoundaryOrderStatement)
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} :=
  GW4Leaf.walkPocketShapeRegStatement_of_det (pocketShapeDetStatement_of_discGapSide hSide hB)
    hCO hNC hSB hA hGeom

/-- The deterministic target from the two remaining local geometric inputs. -/
theorem pocketShapeDetStatement_of_local_inputs
    (hSide : DiscGapSideStatement) (hOne : OneInteriorChartBoundaryOrderStatement) :
    GW4Leaf.PocketShapeDetStatement :=
  pocketShapeDetStatement_of_discGapSide hSide (oneInteriorChartBoundaryOrderStatement_iff.1 hOne)

/-- The almost-sure consequence from the local side input and one ordered chart. -/
theorem walkPocketShapeRegStatement_of_local_inputs
    (hSide : DiscGapSideStatement) (hOne : OneInteriorChartBoundaryOrderStatement)
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} :=
  walkPocketShapeRegStatement_of_discGapSide hSide (oneInteriorChartBoundaryOrderStatement_iff.1 hOne)
    hCO hNC hSB hA hGeom

end InteractingSLE.Theorem14.PocketRim
