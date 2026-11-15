/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntGermFill
import InteractingSLE.Spec.Supplement.WalkIntBridgeMatch

/-!
# Geometric matches without inherited-lift assumptions

Ordinary matches supply a real incident interval; real matches supply a
raw trace gap and its physical filling. Their inherited zero limits follow
from the preceding modules.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntGerm

open WalkBdry WalkIntCanon

/-- Physical prefix matching plus a real incident transition interval.
There is no lift comparison or transition-hull gap in these data. -/
def IsPieceIncidentMatch (s s' : ExplState) (left : Bool) (c : Chart)
    {d : Chart} (B : HullModel d) (x : ℝ) : Prop :=
  ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0) (y : ℝ) (p : ℂ) (r δ : ℝ)
    (A : HullModel (prefixChart pc τ)),
    s.1 = pre ++ pc :: post ∧ (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
    (if left then IsLeftSidePt pc τ y else IsRightSidePt pc τ y) ∧
    Tendsto (prefixChart pc τ).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) ∧
    p ∈ wsetOf s ∪ {z : ℂ | z.im = 0} ∧ 0 < r ∧
    wsetOf s ∩ ball p r ⊆ prefixSet pre pc τ ∧
    wsetOf s' ∩ ball p r ⊆ wsetOf s ∧ IsNormalized (prefixChart pc τ) ∧
    A.hull ⊆ B.hull ∧ 0 < δ ∧
    (∀ w ∈ H ∩ ball (x : ℂ) δ, c.2.1 w ∈ (prefixChart pc τ).dom) ∧
    Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w))
      (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) ∧
    ∀ z ∈ ball (x : ℂ) δ, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
      Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w)) (𝓝[H] z) (𝓝 v)

theorem isPieceMatchRef_of_incident {s s' : ExplState} {left : Bool}
    {c d : Chart} {B : HullModel d} {x : ℝ} (hc : c.IsConformal)
    (hd : IsNormalized d) (hC : (c.dom : Set ℂ) ⊆ d.dom)
    (h : IsPieceIncidentMatch s s' left c B x) :
    WalkIntBridge.IsPieceMatchRef s s' left c d x := by
  obtain ⟨pre, post, pc, τ, y, p, r, δ, A, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, h13, h14⟩ := h
  refine ⟨pre, post, pc, τ, y, p, r, δ, h1, h2, h3, h4, h5, h6, h7, h8,
    h9.conformal, h11, h12, h13, ?_⟩
  exact tendsto_piece_lift_sub_of_realLimits hc A B h9 hd h10 hC h11 h12 h14 h13

/-- A surviving real collar, with its retained physical raw set. No
reference-lift boundary limit is included. -/
def IsRealIncidentMatch (sR sL : ExplState) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (c : Chart) {d : Chart} (B : HullModel d) (x bx : ℝ) : Prop :=
  ∃ (a r : ℝ) (Γ : Set ℂ), a ∉ (jumps : Set ℝ) ∧ 0 < r ∧
    Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ)) ∧
    Disjoint (ball (a : ℂ) r) (wsetOf sR ∪ wsetOf sL) ∧
    Γ ⊆ wsetOf sR ∪ wsetOf sL ∧ B.hull = fillH Γ ∧ bx = b a

theorem isRealMatchRef_of_incident {sR sL : ExplState} {b : ℝ → ℝ}
    {jumps : Finset ℝ} {c d : Chart} {B : HullModel d} {x bx : ℝ}
    (hc : c.IsConformal) (hd : IsNormalized d) (hC : (c.dom : Set ℂ) ⊆ d.dom)
    (h : IsRealIncidentMatch sR sL b jumps c B x bx) :
    WalkIntBridge.IsRealMatchRef sR sL b jumps c d x bx := by
  obtain ⟨a, r, Γ, ha, hr, hland, hgap, hΓ, hB, hbx⟩ := h
  refine ⟨a, r, ha, hr, hland, hgap, ?_, hbx⟩
  exact tendsto_lift_zero_comp_of_raw_gap hc B hd hB hC hr
    (hgap.mono_right hΓ) hland

end InteractingSLE.Theorem14.WalkIntGerm
