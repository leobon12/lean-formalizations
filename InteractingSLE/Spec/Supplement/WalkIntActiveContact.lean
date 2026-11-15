/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntExtendFamily
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# A free boundary contact places a component in the active domain

The existing half-plane separation results already include real contacts
and the inward-push argument. A free point in the closure of a connected
component supplies a point outside the filling; saturation supplies the
whole component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntActive

/-- A free contact of the closure of a preconnected component suffices
for active containment, including when the contact itself is real. -/
theorem active_of_free_contact {F C : Set ℂ} (hF : IsClosed F)
    (hC : IsPreconnected C) (hCF : C ⊆ H \ F) {q : ℂ}
    (hqC : q ∈ closure C) (hq : HalfPlaneSep.IsFreeAt F q) :
    C ⊆ H \ fillH F := by
  obtain ⟨r, hr, hball⟩ := hq
  obtain ⟨p, hpC, hpq⟩ := Metric.mem_closure_iff.1 hqC r hr
  have hpF : p ∈ H \ fillH F :=
    hball ⟨by rw [mem_ball, dist_comm]; exact hpq, (hCF hpC).1⟩
  apply WalkIntGerm.subset_H_diff_fillH_of_mem hC _ hpC hpF
  simpa only [hF.closure_eq] using hCF

/-- A continuation in Hbar that is connected, unbounded and disjoint
from a compact retained set makes any incident component active. The
continuation may contain arbitrarily many original-real contacts. -/
theorem active_of_unbounded_continuation {F C X : Set ℂ} (hF : IsCompact F)
    (hC : IsPreconnected C) (hCF : C ⊆ H \ F)
    (hX : IsPreconnected X) (hXu : ¬ Bornology.IsBounded X)
    (hXF : X ⊆ Hbar \ F) {q : ℂ} (hqX : q ∈ X) (hqC : q ∈ closure C) :
    C ⊆ H \ fillH F :=
  active_of_free_contact hF.isClosed hC hCF hqC
    (HalfPlaneSep.isFreeAt_of_not_isBounded hF.isClosed hF.isBounded hX hXu hXF q hqX)

end InteractingSLE.Theorem14.WalkIntActive
