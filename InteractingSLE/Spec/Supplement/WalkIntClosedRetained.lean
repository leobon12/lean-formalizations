/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedPiece

/-!
# Retained prefixes allowing a completed finite ordinary piece

These are separate internal objects. The existing live WalkPrefix and
RetainedPair declarations and all their consumers remain unchanged.
Every closed-time prefix has the same literal recorded raw support and
a proved normalized model of its physical filling.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkBdry WalkIntCanon Exist.StagedLaw

/-- A finite own-time truncation of an actual recorded piece, allowing
equality at a finite lifetime, with its actual chart and filling model. -/
structure ClosedPrefix (s : ExplState) where
  pre : List Piece
  post : List Piece
  piece : Piece
  time : ℝ≥0
  split : s.1 = pre ++ piece :: post
  time_le : (time : ℝ≥0∞) ≤ piece.2.2
  model : HullModel (prefixChart piece time)
  normalized : IsNormalized (prefixChart piece time)
  proper : GW1P.HasProperBdryExt (prefixChart piece time)
  filled : model.hull = fillH (prefixSet pre piece time)

/-- The literal ordinary support of the recorded truncation. -/
def ClosedPrefix.raw {s : ExplState} (R : ClosedPrefix s) : Set ℂ :=
  prefixSet R.pre R.piece R.time

/-- A previously constructed live prefix is also a closed-time prefix. -/
def ClosedPrefix.ofWalkPrefix {s : ExplState} (R : WalkIntFill.WalkPrefix s) : ClosedPrefix s :=
  ⟨R.pre, R.post, R.piece, R.time, R.split, R.alive.le,
    R.model, R.normalized, R.proper, R.filled⟩

theorem ClosedPrefix.raw_ofWalkPrefix {s : ExplState} (R : WalkIntFill.WalkPrefix s) :
    (ClosedPrefix.ofWalkPrefix R).raw = R.raw := rfl

theorem ClosedPrefix.raw_subset {s : ExplState} (R : ClosedPrefix s) :
    R.raw ⊆ wsetOf s := prefixSet_subset_wsetOf R.split R.time_le

theorem ClosedPrefix.raw_subset_H {s : ExplState} (R : ClosedPrefix s) : R.raw ⊆ H :=
  fun _ hz => hz.2

/-- Closed-time prefix models exist for every regular actual boundary run.
The equality case uses the completed-launch theorem, not a live-time limit. -/
theorem exists_closedPrefix {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (k + 1)).2.2.2.1 k = some (c, θ') → GW1P.PieceRegular (D k).1
        (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) ≤ pc.2.2) :
    ∃ R : ClosedPrefix (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length),
      R.pre = pre ∧ R.post = post ∧ R.piece = pc ∧ R.time = τ := by
  rcases hτ.lt_or_eq with hlt | heq
  · obtain ⟨R, hpre, hpost, hpc, htime⟩ := WalkIntFill.exists_walkPrefix
      θ right D hreg hD hs hlt
    exact ⟨ClosedPrefix.ofWalkPrefix R, hpre, hpost, hpc, htime⟩
  · have hfin : pc.2.2 ≠ ⊤ := heq ▸ ENNReal.coe_ne_top
    have htime : τ = pc.2.2.toNNReal := by rw [← heq, ENNReal.toNNReal_coe]
    obtain ⟨M, hn, hp, hf⟩ := exists_completed_prefix_model _ D hreg hs hfin
    subst τ
    exact ⟨⟨pre, post, pc, pc.2.2.toNNReal, hs, ENNReal.coe_toNNReal_le_self,
      M, hn, hp, hf⟩, rfl, rfl, rfl, rfl⟩

/-- A joint normalized hull of two actual closed-time prefixes. -/
structure ClosedPair (sR sL : ExplState) where
  right : ClosedPrefix sR
  left : ClosedPrefix sL
  chart : Chart
  model : HullModel chart
  normalized : IsNormalized chart
  filled : model.hull = fillH (right.raw ∪ left.raw)
  right_subset : right.model.hull ⊆ model.hull
  left_subset : left.model.hull ⊆ model.hull

def ClosedPair.raw {sR sL : ExplState} (J : ClosedPair sR sL) : Set ℂ :=
  J.right.raw ∪ J.left.raw

/-- Existing live references embed with exactly the same chart, model,
raw support and filling. Thus whole-pool cofinality also covers old witnesses. -/
def ClosedPair.ofRetainedPair {sR sL : ExplState}
    (J : WalkIntFill.RetainedPair sR sL) : ClosedPair sR sL :=
  ⟨ClosedPrefix.ofWalkPrefix J.right, ClosedPrefix.ofWalkPrefix J.left,
    J.chart, J.model, J.normalized, J.filled, J.right_subset, J.left_subset⟩

theorem ClosedPair.raw_ofRetainedPair {sR sL : ExplState}
    (J : WalkIntFill.RetainedPair sR sL) : (ClosedPair.ofRetainedPair J).raw = J.raw := rfl

theorem ClosedPair.raw_subset {sR sL : ExplState} (J : ClosedPair sR sL) :
    J.raw ⊆ wsetOf sR ∪ wsetOf sL :=
  union_subset_union J.right.raw_subset J.left.raw_subset

/-- The joint model is constructed from the proved physical fillings. -/
theorem exists_closedPair {sR sL : ExplState} (R : ClosedPrefix sR) (L : ClosedPrefix sL) :
    ∃ J : ClosedPair sR sL, J.right = R ∧ J.left = L := by
  have hR : IsHPHull (fillH R.raw) := by
    rw [ClosedPrefix.raw, ← R.filled]
    exact R.model.isHull
  have hL : IsHPHull (fillH L.raw) := by
    rw [ClosedPrefix.raw, ← L.filled]
    exact L.model.isHull
  obtain ⟨c, M, hn, hM⟩ := WalkIntFill.exists_normalized_hullChart
    (WalkIntFill.isHPHull_fillH_raw_union R.raw_subset_H L.raw_subset_H hR hL)
  refine ⟨⟨R, L, c, M, hn, hM, ?_, ?_⟩, rfl, rfl⟩
  · rw [R.filled, hM]
    exact fillH_mono subset_union_left
  · rw [L.filled, hM]
    exact fillH_mono subset_union_right

end InteractingSLE.Theorem14.WalkIntClosed
