/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFiniteLanding

/-!
# The actual transition domain is GB11's current face

PROVE-POCKET-SIDEIN. Write the initial inner pocket in the initial outer
chart, then invert it as in GB11. The common ambient-hull cut and the
actual outer own clock identify its current face exactly. No face-domain
identification is an additional geometric hypothesis.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open Theorem14.GB11Chart
open WangWu (negInv)

/-- The common physical hull gives exactly GB11's current domain for the
initial inner pocket read in the initial outer chart. -/
theorem transition_domain_eq_ownDomain_of_common_cut {base outer inner : Chart}
    (hB : base.IsConformal) (hO : outer.IsConformal) (hI : inner.IsConformal)
    {U F : Set ℂ} (hUC : U ⊆ base.dom)
    (hOuterCut : (outer.dom : Set ℂ) = (base.dom : Set ℂ) ∩ (H \ F))
    (hInnerCut : (inner.dom : Set ℂ) = U ∩ (H \ F))
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hOuterOwn : outer = base.loewner W T) :
    ((pocketTransitionChart outer inner).dom : Set ℂ) =
      ownDomain W (negInv '' (base.1 '' U)) T := by
  have hincl : (inner.dom : Set ℂ) ⊆ outer.dom := by
    rw [hInnerCut, hOuterCut]
    exact inter_subset_inter_left _ hUC
  have hRel : Theorem14.GW4Traverse.relDom (negInv '' (base.1 '' U)) = base.1 '' U := by
    exact Set.preimage_image_eq _ WangWu.negInv_involutive.injective
  have htr : ∀ z ∈ H, YuanSimpleApprox.trMap W 0 T z = QuantumZipper.fwdMapInv W T z := by
    intro z hz
    rw [YuanSimpleApprox.trMap_eq_fwdMapInv hW hT hz,
      YuanSimpleApprox.shiftDrive_zero_eq hW0, sub_zero]
  ext z
  change z ∈ (pocketTransitionChart outer inner).dom ↔ _
  rw [mem_dom_pocketTransitionChart hO hI hincl]
  change _ ↔ z ∈ H ∧ YuanSimpleApprox.trMap W 0 T z ∈ Theorem14.GW4Traverse.relDom _
  rw [hRel]
  constructor
  · rintro ⟨hz, hp⟩
    have hp' : outer.2.1 z ∈ (inner.dom : Set ℂ) := hp
    rw [hInnerCut] at hp'
    refine ⟨hz, outer.2.1 z, hp'.1, ?_⟩
    rw [htr z hz, hOuterOwn]
    change base.1 (base.2.1 (QuantumZipper.fwdMapInv W T z)) = _
    exact hB.2.2 _ (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT hz)
  · rintro ⟨hz, hp⟩
    rw [htr z hz] at hp
    obtain ⟨p, hpU, hpz⟩ := hp
    have hpinv : outer.2.1 z = p := by
      rw [hOuterOwn]
      change base.2.1 (QuantumZipper.fwdMapInv W T z) = p
      rw [← hpz, hB.inv_fwd (hUC hpU)]
    have hnow : outer.2.1 z ∈ (outer.dom : Set ℂ) := hO.inv_mem_dom hz
    rw [hOuterCut] at hnow
    refine ⟨hz, ?_⟩
    change outer.2.1 z ∈ (inner.dom : Set ℂ)
    rw [hInnerCut]
    exact ⟨hpinv ▸ hpU, hnow.2⟩

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketStopField
open Theorem14.GB11Chart
open WangWu (negInv)

variable {Ω : Type} [MeasurableSpace Ω]

/-- Actual original-visit capacities identify the nested transition's face
in the original outer pocket coordinate, with the same original hull. -/
theorem transition_domain_eq_ownDomain_at_original_visit {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hOuterOwn : relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω =
        ((outer.target i d).baseChart ω).loewner W (outer.visitCapacity d ω t).toNNReal) :
    let O := relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω
    let I := relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω
    ((pocketTransitionChart O I).dom : Set ℂ) =
      ownDomain W (negInv '' (((outer.target i d).baseChart ω).1 '' (inner.target i d).domain ω))
        (outer.visitCapacity d ω t).toNNReal := by
  have hb := isDomainChart_baseChart hO hRc hLcO hωO
  have ho := (isDomainChart_relChart_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)).1
  have hi := (isDomainChart_relChart_visitCapacity hI hRc hLcI hωI ht hvisit).1
  apply transition_domain_eq_ownDomain_of_common_cut hb.1 ho hi
    (U := (inner.target i d).domain ω)
    (F := QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t)
  · rwa [hb.coe_dom]
  · rw [hb.coe_dom]
    exact relChart_dom_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)
  · exact relChart_dom_visitCapacity hI hRc hLcI hωI ht hvisit
  · exact hW
  · exact hW0
  · exact (outer.visitCapacity d ω t).toNNReal.coe_nonneg
  · exact hOuterOwn

end InteractingSLE.Wire.Current.SideTest
