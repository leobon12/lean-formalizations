/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillFamily
import InteractingSLE.Spec.Supplement.WalkIntFiberWord

/-!
# Physical matches persist in larger retained reference hulls

Ordinary matches change only their hull inclusion. Real collars can be
referenced to any actual retained pair, using its physical filling identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntPromote

open WalkBdry WalkIntFill WalkIntFiber WalkIntCanon

/-- Raw inclusion of actual retained pairs implies reference-hull inclusion. -/
theorem retained_hull_subset {sR sL : ExplState} {J K : RetainedPair sR sL}
    (h : J.raw ⊆ K.raw) : J.model.hull ⊆ K.model.hull := by
  rw [J.filled, K.filled]
  exact fillH_mono h

/-- Enlarging the reference hull preserves every chosen physical witness. -/
theorem isPiecePhysicalMatch_of_hull_subset {s s' : ExplState} {left : Bool}
    {c d e : Chart} {B : HullModel d} {D : HullModel e} {x : ℝ}
    (hBD : B.hull ⊆ D.hull) (h : IsPiecePhysicalMatch s s' left c B x) :
    IsPiecePhysicalMatch s s' left c D x := by
  obtain ⟨pre, post, pc, τ, y, p, r, δ, A, hs, hτ, hside, hland, hp, hr,
    hown, hother, hAB, hδ, hdom, hlim⟩ := h
  exact ⟨pre, post, pc, τ, y, p, r, δ, A, hs, hτ, hside, hland, hp, hr,
    hown, hother, hAB.trans hBD, hδ, hdom, hlim⟩

/-- The same untouched real collar works for any actual retained pair.
Its new raw support and filling identity come from that pair. -/
theorem isRealIncidentMatch_retained {sR sL : ExplState} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {c d : Chart} {B : HullModel d} {x bx : ℝ}
    (K : RetainedPair sR sL)
    (h : WalkIntGerm.IsRealIncidentMatch sR sL b jumps c B x bx) :
    WalkIntGerm.IsRealIncidentMatch sR sL b jumps c K.model x bx := by
  obtain ⟨a, r, Γ, ha, hr, hland, hgap, _, _, hbx⟩ := h
  exact K.isRealIncidentMatch ha hr hland hgap hbx

end InteractingSLE.Theorem14.WalkIntPromote
