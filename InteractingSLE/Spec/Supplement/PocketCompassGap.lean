/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketCompassOrientation

/-!
# The remaining local side reciprocity

PROVE-POCKETSHAPE. The pocket lies below the left crosscut as soon as a point
of its right arc does. Its containment above the right crosscut is equivalent
to the side of one midpoint of the left arc. Only this reciprocity is left as
an explicitly named input; bounded chart orientation has been discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Function
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.PocketCompass

open WangWu Sec7.PocketCoord

/-- A local lower-side point places the entire contact-gap pocket below the left crosscut. -/
theorem pocket_subset_left_lower_of_point {α β : ℝ → ℂ}
    (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β))
    {a b : ℝ} (hg : IsContactGap α β a b) {c : ℝ} (hc : c ∈ Ioo a b)
    (hside : α c ∈ crossSide β (-1)) :
    jordanIn (pocketCurve α β a b) ⊆ crossSide β (-1) := by
  obtain ⟨hJ, hD, hdisj, -, -⟩ := pocket_props_of_strictMono hα hβ hjm hg
  have hcl : α c ∈ closure (jordanIn (pocketCurve α β a b)) :=
    frontier_subset_closure (image_subset_frontier_pocket_left hα hβ hjm hg ⟨c, Ioo_subset_Icc_self hc, rfl⟩)
  exact hβ.subset_crossSide_of_isPreconnected (Or.inr rfl) (isPreconnected_jordanIn hJ)
    (fun z hz => ⟨hD hz, fun h => disjoint_left.1 hdisj hz (Or.inr h)⟩)
    (inter_nonempty_of_mem_closure (hβ.isOpen_crossSide (Or.inr rfl)) hside hcl)

/-- The side of the whole pocket is exactly the side of the midpoint of its left arc. -/
theorem pocket_subset_right_upper_iff_midpoint {α β : ℝ → ℂ}
    (hα : IsDiscCrosscut α) (hβ : IsDiscCrosscut β)
    (hjm : StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β))
    {a b : ℝ} (hg : IsContactGap α β a b) :
    jordanIn (pocketCurve α β a b) ⊆ crossSide α 1 ↔
      β ((contactMap α β a + contactMap α β b) / 2) ∈ crossSide α 1 := by
  let m := (contactMap α β a + contactMap α β b) / 2
  have hjab := hjm hg.1 hg.2.1 hg.2.2.1
  have hm : m ∈ Ioo (contactMap α β a) (contactMap α β b) :=
    ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  obtain ⟨hmD, hmα⟩ := mem_ball_notMem_of_mem_Ioo hα hβ hjm hg hm
  have hcl : β m ∈ closure (jordanIn (pocketCurve α β a b)) :=
    frontier_subset_closure (image_subset_frontier_pocket hα hβ hjm hg ⟨m, Ioo_subset_Icc_self hm, rfl⟩)
  constructor
  · intro hsub
    exact PocketRim.mem_crossSide_of_mem_closure hα (Or.inl rfl) hmD hmα (closure_mono hsub hcl)
  · intro hside
    obtain ⟨hJ, hD, hdisj, -, -⟩ := pocket_props_of_strictMono hα hβ hjm hg
    exact hα.subset_crossSide_of_isPreconnected (Or.inl rfl) (isPreconnected_jordanIn hJ)
      (fun z hz => ⟨hD hz, fun h => disjoint_left.1 hdisj hz (Or.inl h)⟩)
      (inter_nonempty_of_mem_closure (hα.isOpen_crossSide (Or.inl rfl)) hside hcl)

/-- Unproved local planar reciprocity input: a right gap below the other crosscut
has the midpoint of its matching left gap above the right crosscut. This is
equivalent to the previous remaining input, not a source theorem or an axiom. -/
def ContactGapSideReciprocityStatement : Prop :=
  ∀ α β : ℝ → ℂ, IsDiscCrosscut α → IsDiscCrosscut β →
    StrictMonoOn (contactMap α β) (Sec7.pocketContactSet α β) →
    ∀ a b : ℝ, IsContactGap α β a b → ∀ c ∈ Ioo a b,
      α c ∈ crossSide β (-1) →
        β ((contactMap α β a + contactMap α β b) / 2) ∈ crossSide α 1

/-- The sole remaining input can equivalently be stated using one point of each boundary arc. -/
theorem contactGapSideReciprocityStatement_iff :
    ContactGapSideReciprocityStatement ↔ PocketRim.DiscGapSideStatement := by
  constructor
  · intro h α β hα hβ hjm a b hg c hc hside
    exact (pocket_subset_right_upper_iff_midpoint hα hβ hjm hg).2 (h α β hα hβ hjm a b hg c hc hside)
  · intro h α β hα hβ hjm a b hg c hc hside
    exact (pocket_subset_right_upper_iff_midpoint hα hβ hjm hg).1 (h α β hα hβ hjm a b hg c hc hside)

/-- The deterministic target with only the explicitly named local reciprocity input. -/
theorem pocketShapeDetStatement_of_contactGapSideReciprocity (h : ContactGapSideReciprocityStatement) :
    GW4Leaf.PocketShapeDetStatement :=
  pocketShapeDetStatement_of_discGapSide (contactGapSideReciprocityStatement_iff.1 h)

end InteractingSLE.Theorem14.PocketCompass
