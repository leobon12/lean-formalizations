/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketMirrorMarked

/-!
# Contact-gap side reciprocity and the deterministic pocket-shape theorem

PROVE-POCKETSHAPE. If both boundary arcs were below their respective
crosscuts, a two-point uniformizer would map both onto the negative real
half-line, contrary to its boundary injectivity. This discharges the final
local input of the deterministic source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.PocketMirror

open WangWu Sec7.PocketCoord Sec7.PocketJordan GW4Reg GW4BarrierSelf

/-- The candidate pocket is above its right crosscut whenever its right arc is below the left crosscut. -/
theorem discGapSideStatement : PocketRim.DiscGapSideStatement := by
  intro α β hα hβ hjm a b hg c hc hside
  let D := jordanIn (pocketCurve α β a b)
  obtain ⟨hJ, hDb, hd, hfr, -⟩ := pocket_props_of_strictMono hα hβ hjm hg
  have hDo : IsOpen D := isOpen_jordanIn hJ
  have hDpc : IsPreconnected D := isPreconnected_jordanIn hJ
  have hDα : Disjoint D (crossRange α) := hd.mono_right subset_union_left
  have hDβ : Disjoint D (crossRange β) := hd.mono_right subset_union_right
  have hDβlower : D ⊆ crossSide β (-1) := PocketCompass.pocket_subset_left_lower_of_point hα hβ hjm hg hc hside
  have hcover : D ⊆ crossSide α 1 ∪ crossSide α (-1) := fun z hz =>
    hα.subset_crossSide_union ⟨hDb hz, fun h => disjoint_left.1 hDα hz h⟩
  rcases IsPreconnected.subset_or_subset (hα.isOpen_crossSide (Or.inl rfl))
    (hα.isOpen_crossSide (Or.inr rfl)) hα.disjoint_crossSide hcover hDpc with hupper | hlower
  · exact hupper
  · exfalso
    have hIa := right_closure_interval_of_contactGap hα hβ hjm hg
    have hIb := left_closure_interval_of_contactGap hα hβ hjm hg
    have hpa : α a ∈ frontier D := image_subset_frontier_pocket_left hα hβ hjm hg
      ⟨a, left_mem_Icc.2 hg.2.2.1.le, rfl⟩
    have hpb : α b ∈ frontier D := image_subset_frontier_pocket_left hα hβ hjm hg
      ⟨b, right_mem_Icc.2 hg.2.2.1.le, rfl⟩
    have hpq : α a ≠ α b := fun he => hg.2.2.1.ne (hα.inj hg.1.1 hg.2.1.1 he)
    obtain ⟨Ψ, hU⟩ := exists_isBdryUniformizer hDo
      ⟨(JordanSides hJ).2.2.2.1, hDpc⟩ (isBounded_ball.subset hDb) (hfr.symm ▸ hJ) hpa hpb hpq
    have hnegα := re_neg_of_disc_crossSide hα hDo hDpc hDb hDα
      hg.1.1.1 hg.2.2.1 hg.2.1.1.2 hIa hU hlower
    obtain ⟨hja, hjb⟩ := contactMap_mem_Icc hβ hg
    have heqa := (contactMap_mem hβ hg.1).2
    have heqb := (contactMap_mem hβ hg.2.1).2
    have hUβ : IsBdryUniformizer D (β (contactMap α β a)) (β (contactMap α β b)) Ψ := by
      rw [heqa, heqb]
      exact hU
    have hjab := contactMap_lt_contactMap hjm hg
    have hnegβ := re_neg_of_disc_crossSide hβ hDo hDpc hDb hDβ hja.1 hjab hjb.2 hIb hUβ hDβlower
    let m := (a + b) / 2
    have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith [hg.2.2.1], by dsimp [m]; linarith [hg.2.2.1]⟩
    have hm01 : m ∈ Icc (0 : ℝ) 1 := ⟨hg.1.1.1.trans hm.1.le, hm.2.le.trans hg.2.1.1.2⟩
    have hmq : α m ≠ α b := fun he => hm.2.ne (hα.inj hm01 hg.2.1.1 he)
    have hmfr : α m ∈ frontier D := image_subset_frontier_pocket_left hα hβ hjm hg
      ⟨m, Ioo_subset_Icc_self hm, rfl⟩
    have hreal : (Ψ (α m)).im = 0 := hU.im_eq_zero hDo
      (fun h => disjoint_left.1 hDα h ⟨b, hg.2.1.1, rfl⟩) hmfr hmq
    obtain ⟨r, hr, her⟩ := exists_negative_boundary_preimage hβ hDo hDβ hja.1 hjab hjb.2 hIb hUβ hnegβ (hnegα m hm)
    have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hja.1.trans hr.1.le, hr.2.le.trans hjb.2⟩
    have hrcl : β r ∈ closure D := frontier_subset_closure
      (image_subset_frontier_pocket hα hβ hjm hg ⟨r, Ioo_subset_Icc_self hr, rfl⟩)
    have hrq : β r ≠ α b := fun he => hr.2.ne (hβ.inj hr01 hjb (he.trans heqb.symm))
    have he : α m = β r := hU.inj ⟨frontier_subset_closure hmfr, hmq⟩ ⟨hrcl, hrq⟩ (by
      rw [her]
      exact Complex.ext (by simp only [ofReal_re]) (by rw [hreal, ofReal_im]))
    exact hg.2.2.2 m hm ⟨hm01, r, hr01, he.symm⟩

/-- The midpoint form of local contact-gap side reciprocity is discharged. -/
theorem contactGapSideReciprocityStatement : PocketCompass.ContactGapSideReciprocityStatement :=
  PocketCompass.contactGapSideReciprocityStatement_iff.2 discGapSideStatement

/-- The unchanged deterministic pocket-shape target, with no remaining geometric input. -/
theorem pocketShapeDetStatement : GW4Leaf.PocketShapeDetStatement :=
  PocketCompass.pocketShapeDetStatement_of_discGapSide discGapSideStatement

/-- The existing almost-sure pocket-shape consequence, retaining its original regularity inputs. -/
theorem walkPocketShapeRegStatement
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} :=
  PocketCompass.walkPocketShapeRegStatement_of_discGapSide discGapSideStatement hCO hNC hSB hA hGeom

end InteractingSLE.Theorem14.PocketMirror
