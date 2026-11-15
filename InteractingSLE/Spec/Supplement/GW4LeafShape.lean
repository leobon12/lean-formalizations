/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4LeafOrder

/-!
# The pocket shape of the walks: reduction to a deterministic planar statement

Packet PROVE-T14-GW4REG. `GW4BarrierSelf.WalkPocketShapeRegStatement` asks, almost surely, for the pocket shape
(`GW4Reg.WalkPocketShape`) of every parametrization of the two walks by complete simple flows. GW4's proof (p. 637):
"The ordered-contact Jordan argument and GB13a consequently apply to these two proper simple curves". This file
separates the probability from the planar topology:

* `PocketShapeDetStatement` (**named deterministic input**, the ordered-contact Jordan argument): two complete simple
  flows with the same contact order along both, no common open subarc, each off the open outer side of the other, all
  of whose between-components are two-arc Jordan components or have an oriented uniformizer, have the pocket shape;
* **`walkPocketShapeRegStatement_of_det`**: the R51 statement from it and the almost-sure inputs already present in
  Theorem 1.4's wiring — the contact order (`WalkContactOrderRegStatement`, now proved from the wiring's inputs), no
  common continuum (`WalkCont.WalkNoCommonContinuumRegStatement`), SB's frontiers (`SB.SBFrontierRegStatement`),
  GW2a's containment and GW3's geometry (`GW3Sided.GW3GeometryRegStatement`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Leaf

open GW4Traverse GW4Ident GW4Reg GW4BarrierSelf

/-- **Named deterministic input: the ordered-contact Jordan argument** (GW4's proof, p. 637; GB11's barrier input,
p. 555: "Let `C_j` be the Jordan interiors bounded by their two arcs between successive common contacts"). -/
def PocketShapeDetStatement : Prop :=
  ∀ αR αL : ℝ≥0 → ℂ, GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
    (∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')) →
    (∀ a b : ℝ≥0, a < b → ¬ αR '' Icc a b ⊆ range αL) →
    Disjoint (range αL) (rightSideOf (range αR)) → Disjoint (range αR) (leftSideOf (range αL)) →
    (∀ C ∈ betweenComponents (range αR) (range αL),
      GW3.IsTwoArcJordanComponent (range αR) (range αL) C ∨ GW3.HasOrientedUniformizer (range αR) (range αL) C) →
    WalkPocketShape αR αL

/-- **The pocket shape of the walks** from the deterministic ordered-contact Jordan argument and the almost-sure
inputs of Theorem 1.4's wiring. -/
theorem walkPocketShapeRegStatement_of_det (hdet : PocketShapeDetStatement)
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg
  have hpi := Real.pi_pos
  filter_upwards [hCO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hNC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true),
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false),
    hGeom κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω hC hN hS hAR hAL hG
  intro αR αL hrR hrL hfR hfL
  refine hdet αR αL hfR hfL (hC αR αL hrR hrL hfR hfL) (fun a b' hab hsub => ?_) ?_ ?_ ?_
  · have hS' : αR '' Icc a b' ⊆ range αR ∩ range αL := fun z hz => ⟨image_subset_range _ _ hz, hsub hz⟩
    rw [hrR, hrL] at hS'
    have hsing := hN (αR '' Icc a b') hS' (isPreconnected_Icc.image _ hfR.1.continuousOn)
    have he := hsing ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩ ⟨b', ⟨hab.le, le_rfl⟩, rfl⟩
    exact absurd (hfR.2.1 he) hab.ne
  · rw [hrR, hrL, Set.disjoint_left]
    intro z hzL hzR
    exact eq_empty_iff_forall_notMem.1 hS.1 z ⟨hAL hzL, hzR⟩
  · rw [hrR, hrL, Set.disjoint_left]
    intro z hzR hzL
    exact eq_empty_iff_forall_notMem.1 hS.2 z ⟨hAR hzR, hzL⟩
  · rw [hrR, hrL]
    exact hG

end GW4Leaf

end Theorem14

end InteractingSLE
