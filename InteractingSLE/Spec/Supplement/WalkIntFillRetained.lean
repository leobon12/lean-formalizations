/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillChart

/-!
# Actual prefix pairs give normalized retained hull models

Select two live recorded prefixes. Regularity constructs each raw filling;
the filled union has a normalized chart, includes both individual hulls,
and has raw support inside the two complete ordinary walk sets.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFill

open WalkBdry WalkIntCanon Exist.StagedLaw

/-- A selected live recorded prefix with its proved analytic and physical
model facts. The constructor below needs only the existing run regularity. -/
structure WalkPrefix (s : ExplState) where
  pre : List Piece
  post : List Piece
  piece : Piece
  time : ℝ≥0
  split : s.1 = pre ++ piece :: post
  alive : (time : ℝ≥0∞) < piece.2.2
  model : HullModel (prefixChart piece time)
  normalized : IsNormalized (prefixChart piece time)
  proper : GW1P.HasProperBdryExt (prefixChart piece time)
  filled : model.hull = fillH (prefixSet pre piece time)

def WalkPrefix.raw {s : ExplState} (R : WalkPrefix s) : Set ℂ :=
  prefixSet R.pre R.piece R.time

theorem WalkPrefix.raw_subset {s : ExplState} (R : WalkPrefix s) :
    R.raw ⊆ wsetOf s := prefixSet_subset_wsetOf R.split R.alive.le

theorem WalkPrefix.raw_subset_H {s : ExplState} (R : WalkPrefix s) : R.raw ⊆ H :=
  fun _ hz => hz.2

/-- Every selected live recorded boundary-walk prefix has these facts.
Its physical filling identity is a conclusion, not a new input. -/
theorem exists_walkPrefix {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1
        (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) :
    ∃ R : WalkPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length),
      R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ := by
  obtain ⟨M⟩ := exists_hullModel_prefixChart _ D _
    (fun j _ c θ' hl => hreg j c θ' hl) hD hs hτ
  exact ⟨⟨pre, post, pc, τ, hs, hτ, M,
    isNormalized_prefixChart _ D _ (fun j _ c θ' hl => hreg j c θ' hl) hD hs hτ,
    WalkIntFiber.hasProperBdryExt_prefixChart θ right D hreg hD hs hτ,
    hull_eq_fillH_prefixSet θ right D hreg hD hs hτ M⟩, rfl, rfl, rfl, rfl⟩

/-- A normalized chart of two retained raw prefixes, with both physical
prefix hulls inside its hull. Incident-component geometry is not a field. -/
structure RetainedPair (sR sL : ExplState) where
  right : WalkPrefix sR
  left : WalkPrefix sL
  chart : Chart
  model : HullModel chart
  normalized : IsNormalized chart
  filled : model.hull = fillH (right.raw ∪ left.raw)
  right_subset : right.model.hull ⊆ model.hull
  left_subset : left.model.hull ⊆ model.hull

/-- Two selected prefixes always admit a normalized joint hull model.
No inclusion of a particular between component is assumed or concluded. -/
theorem exists_retainedPair {sR sL : ExplState} (R : WalkPrefix sR) (L : WalkPrefix sL) :
    ∃ J : RetainedPair sR sL, J.right = R ∧ J.left = L := by
  have hR : IsHPHull (fillH R.raw) := by
    rw [WalkPrefix.raw, ← R.filled]
    exact R.model.isHull
  have hL : IsHPHull (fillH L.raw) := by
    rw [WalkPrefix.raw, ← L.filled]
    exact L.model.isHull
  have hK := isHPHull_fillH_raw_union R.raw_subset_H L.raw_subset_H hR hL
  obtain ⟨c, M, hn, hM⟩ := exists_normalized_hullChart hK
  refine ⟨⟨R, L, c, M, hn, hM, ?_, ?_⟩, rfl, rfl⟩
  · rw [R.filled, hM]
    exact fillH_mono subset_union_left
  · rw [L.filled, hM]
    exact fillH_mono subset_union_right

def RetainedPair.raw {sR sL : ExplState} (J : RetainedPair sR sL) : Set ℂ :=
  J.right.raw ∪ J.left.raw

theorem RetainedPair.raw_subset {sR sL : ExplState} (J : RetainedPair sR sL) :
    J.raw ⊆ wsetOf sR ∪ wsetOf sL :=
  union_subset_union J.right.raw_subset J.left.raw_subset

/-- A real match through this constructed joint chart requires only the
original real collar data. Its raw filling identity has already been proved. -/
theorem RetainedPair.isRealIncidentMatch {sR sL : ExplState} (J : RetainedPair sR sL)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {c : Chart} {x bx a r : ℝ}
    (ha : a ∉ (jumps : Set ℝ)) (hr : 0 < r)
    (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ)))
    (hgap : Disjoint (ball (a : ℂ) r) (wsetOf sR ∪ wsetOf sL)) (hbx : bx = b a) :
    WalkIntGerm.IsRealIncidentMatch sR sL b jumps c J.model x bx :=
  ⟨a, r, J.raw, ha, hr, hland, hgap, J.raw_subset, J.filled, hbx⟩

/-- An untouched real collar has zero actual lift in the constructed
joint chart whenever the component lies in its active complement. -/
theorem RetainedPair.tendsto_lift_zero {sR sL : ExplState} (J : RetainedPair sR sL)
    {c : Chart} (hc : c.IsConformal) (hC : (c.dom : Set ℂ) ⊆ J.chart.dom)
    {x a r : ℝ} (hr : 0 < r)
    (hgap : Disjoint (ball (a : ℂ) r) (wsetOf sR ∪ wsetOf sL))
    (hland : Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (a : ℂ))) :
    Tendsto (fun z => J.chart.2.2 (c.2.1 z)) (𝓝[H] (x : ℂ)) (𝓝 0) :=
  WalkIntGerm.tendsto_lift_zero_comp_of_raw_gap hc J.model J.normalized J.filled hC hr
    (hgap.mono_right J.raw_subset) hland

end InteractingSLE.Theorem14.WalkIntFill
