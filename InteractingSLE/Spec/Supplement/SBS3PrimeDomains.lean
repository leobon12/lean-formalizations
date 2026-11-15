/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinCompP38

/-!
# S3: the open domains of the protected component comparison

The component form of Proposition 3.8 uses `FinRel.freeNear`. Such a set is
open whenever the single-history complement is open: a whole component of
the open patch has the same avoidance property. This permits restriction of
both union-mean representatives to their common protected domain.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- The components of the open single-history patch that miss the other
history form an open set. No closedness hypothesis on the other history is
needed for this deterministic topological fact. -/
theorem isOpen_freeNear {A B : Set ℂ} (hB : IsOpen (H \ B)) (p : ℂ) (r : ℝ) :
    IsOpen (FinRel.freeNear A B p r) := by
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  have hU : IsOpen ((H \ B) ∩ ball p r) := hB.inter isOpen_ball
  refine ⟨connectedComponentIn ((H \ B) ∩ ball p r) z, ?_,
    hU.connectedComponentIn, mem_connectedComponentIn hz.1⟩
  intro w hw
  refine ⟨connectedComponentIn_subset _ _ hw, ?_⟩
  rw [← connectedComponentIn_eq hw]
  exact hz.2

/-- The common protected domain is contained in the joint complement,
including at contacts of the two histories. -/
theorem inter_freeNear_subset_joint {A B : Set ℂ} {p : ℂ} {r₁ r₂ : ℝ} :
    FinRel.freeNear B A p r₁ ∩ FinRel.freeNear A B p r₂ ⊆ H \ (A ∪ B) :=
  fun _ hz => FinRel.freeNear_subset hz.2

end InteractingSLE.Theorem14.SB.S3
