/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBridgeLift
import InteractingSLE.Spec.Supplement.WalkNormChart

/-!
# Matching every component flank with one integer

The geometric data compare each piece or untouched real collar with one of
the retained-prefix references. No integer is supplied in these data. The
shared-anchor theorem constructs one integer for all reference indices and
both incoming sides, then the existing normalization lemma applies.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntBridge

open WalkBdry WalkNorm WalkMean GW3Between

/-- A prefix match whose inherited lift agrees with a retained-prefix
reference. The component chart's lift is not normalized here. -/
def IsPieceMatchRef (s s' : ExplState) (left : Bool) (c d : Chart) (x : ℝ) : Prop :=
  ∃ (pre post : List Piece) (pc : Piece) (τ : ℚ≥0) (y : ℝ) (p : ℂ) (r δ : ℝ),
    s.1 = pre ++ pc :: post ∧ (((τ : ℝ≥0)) : ℝ≥0∞) < pc.2.2 ∧
    (if left then IsLeftSidePt pc τ y else IsRightSidePt pc τ y) ∧
    Tendsto (prefixChart pc τ).2.1 (𝓝[H] (y : ℂ)) (𝓝 p) ∧
    p ∈ wsetOf s ∪ {z : ℂ | z.im = 0} ∧ 0 < r ∧
    wsetOf s ∩ ball p r ⊆ prefixSet pre pc τ ∧
    wsetOf s' ∩ ball p r ⊆ wsetOf s ∧ (prefixChart pc τ).IsConformal ∧
    0 < δ ∧ (∀ w ∈ H ∩ ball (x : ℂ) δ, c.2.1 w ∈ (prefixChart pc τ).dom) ∧
    Tendsto (fun w => (prefixChart pc τ).1 (c.2.1 w))
      (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) ∧
    Tendsto (fun w => (prefixChart pc τ).2.2 (c.2.1 w) - d.2.2 (c.2.1 w))
      (𝓝[H] (x : ℂ)) (𝓝 0)

/-- An untouched real collar on which the retained reference has zero lift. -/
def IsRealMatchRef (sR sL : ExplState) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (c d : Chart) (x bx : ℝ) : Prop :=
  ∃ a r : ℝ, a ∉ (jumps : Set ℝ) ∧ 0 < r ∧
    Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ)) ∧
    Disjoint (ball (a : ℂ) r) (wsetOf sR ∪ wsetOf sL) ∧
    Tendsto (fun w => d.2.2 (c.2.1 w)) (𝓝[H] (x : ℂ)) (𝓝 0) ∧ bx = b a

/-- Add the reference-to-component difference to the piece-to-reference
difference. -/
theorem isPieceMatchLoc_of_ref {s s' : ExplState} {left : Bool}
    {c d : Chart} {x : ℝ} {n : ℤ} (h : IsPieceMatchRef s s' left c d x)
    (hn : Tendsto (fun w => d.2.2 (c.2.1 w) - c.2.2 (c.2.1 w))
      (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n))) : IsPieceMatchLoc s s' left c x n := by
  obtain ⟨pre, post, pc, τ, y, p, r, δ, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, h13⟩ := h
  refine ⟨pre, post, pc, τ, y, p, r, δ, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, ?_⟩
  have hs := h13.add hn
  rw [zero_add] at hs
  refine hs.congr fun w => ?_
  ring

/-- Subtract the reference-to-component difference from the zero real lift. -/
theorem isRealMatchLoc_of_ref {sR sL : ExplState} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {c d : Chart} {x bx : ℝ} {n : ℤ} (h : IsRealMatchRef sR sL b jumps c d x bx)
    (hn : Tendsto (fun w => d.2.2 (c.2.1 w) - c.2.2 (c.2.1 w))
      (𝓝[H] (x : ℂ)) (𝓝 (2 * π * n))) :
    IsRealMatchLoc sR sL b jumps c x bx n := by
  obtain ⟨a, r, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨a, r, h1, h2, h3, h4, ?_, h6⟩
  have hs := h5.sub hn
  rw [zero_sub] at hs
  refine hs.congr fun w => ?_
  ring

/-- The component word and all geometric matches through a retained-prefix
reference family. A match may use a different reference index at each point;
the common integer will be constructed, rather than assumed. -/
def IsNormChartRef (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (r : ExplState × ExplState) (C : Set ℂ) (t : Chart × (ℝ → ℝ) × Finset ℝ)
    (F : ReferenceFamily t.1) : Prop :=
  IsComponentChart (physOf (boundaryWalkSpec b jumps (-(π / 2)) true) r.1)
      (physOf (boundaryWalkSpec b jumps (π / 2) false) r.2) C t.1 ∧
    IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
    IsComponentBoundaryData κ b (ordOf r.1) (ordOf r.2) t.1.2.1 t.2.1 t.2.2 ∧
    ∃ Eℝ : Set ℝ, Eℝ.Finite ∧ ∀ x : ℝ, x ∉ Eℝ →
      (0 < x → ∃ i, x ∈ F.interval i ∧
        ((IsPieceMatchRef r.1 r.2 true t.1 (F.chart i) x ∧
          t.2.1 x = -bigLambda κ) ∨
          IsRealMatchRef r.1 r.2 b jumps t.1 (F.chart i) x (t.2.1 x))) ∧
      (x < 0 → ∃ i, x ∈ F.interval i ∧
        ((IsPieceMatchRef r.2 r.1 false t.1 (F.chart i) x ∧
          t.2.1 x = bigLambda κ) ∨
          IsRealMatchRef r.1 r.2 b jumps t.1 (F.chart i) x (t.2.1 x)))

/-- The continuous argument carried by a component chart has an analytic
derivative logarithm. -/
theorem hasDerivLift_of_isComponentChart {R L C : Set ℂ} {c : Chart}
    (hc : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H) :
    c.IsConformal ∧ c.HasDerivLift := by
  have hconf := GW3Law.isConformal_of_isComponentChart hc hCo hCH
  have hdom : (c.dom : Set ℂ) = C :=
    hconf.coe_dom.trans (GW3Joint.image_inv_eq_of_isComponentChart hc)
  refine ⟨hconf, hasDerivLift_of_continuous_arg hconf ?_ ?_⟩
  · rw [hdom]
    exact hc.2.2.2.2.2.1
  · rw [hdom]
    exact hc.2.2.2.2.2.2

/-- Reference-family geometry gives one integer for every match of the
component, including both flanks and untouched real collars. -/
theorem exists_isNormChartLoc_of_ref {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {r : ExplState × ExplState} {C : Set ℂ} {t : Chart × (ℝ → ℝ) × Finset ℝ}
    {F : ReferenceFamily t.1} (hCo : IsOpen C) (hCH : C ⊆ H)
    (h : IsNormChartRef κ b jumps r C t F) :
    ∃ n : ℤ, IsNormChartLoc κ b jumps r C t n := by
  obtain ⟨hchart, hb, hword, Eℝ, hE, hm⟩ := h
  obtain ⟨hc, hL⟩ := hasDerivLift_of_isComponentChart hchart hCo hCH
  obtain ⟨n, hn⟩ := F.exists_int hc hL
  refine ⟨n, hchart, hb, hword, Eℝ, hE, fun x hx => ⟨fun hx0 => ?_, fun hx0 => ?_⟩⟩
  · obtain ⟨i, hxi, hi⟩ := (hm x hx).1 hx0
    rcases hi with ⟨hp, hv⟩ | hr
    · exact Or.inl ⟨isPieceMatchLoc_of_ref hp (hn i x hxi), hv⟩
    · exact Or.inr (isRealMatchLoc_of_ref hr (hn i x hxi))
  · obtain ⟨i, hxi, hi⟩ := (hm x hx).2 hx0
    rcases hi with ⟨hp, hv⟩ | hr
    · exact Or.inl ⟨isPieceMatchLoc_of_ref hp (hn i x hxi), hv⟩
    · exact Or.inr (isRealMatchLoc_of_ref hr (hn i x hxi))

end InteractingSLE.Theorem14.WalkIntBridge
