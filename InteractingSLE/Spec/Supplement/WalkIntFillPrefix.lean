/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFillBoundary

/-!
# The physical hull of a live walk prefix is its actual filling

The capped program's frontier lies on its recorded ordinary set in H.
Prefix avoidance and the boundary-support theorem identify the physical
hull with the filling of the raw prefix set, without a new filling input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFill

open WalkBdry WalkIntCanon Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- All finite frontier points in H of an actual live prefix belong to
the raw prefix set. This is the capped run's existing frontier theorem. -/
theorem frontier_prefixChart_subset_prefixSet
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
    frontier ((prefixChart pc τ).dom : Set ℂ) ∩ H ⊆ prefixSet pre pc τ := by
  let w := boundaryWalkSpec b jumps θ right
  obtain ⟨ℓ, hℓ, θ', hl, hpre, hpc⟩ :=
    WalkSide.exists_launch_of_pieces_eq (κ := κ) (b := b) (jumps := jumps)
      w D w.2.2.length hs
  have hins := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) w D hl).1
  obtain ⟨hθ, ht⟩ := WalkLeaf.boundaryWalkSpec_inl hins
  have hins' : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤)) := by
    simpa only [hθ, ht] using hins
  rw [ht] at hpc
  have hτ' : (τ : ℝ≥0∞) < min ⊤ (D ℓ).2 := by
    rw [hpc] at hτ
    exact hτ
  let E : ℕ → Unit → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun k _ => D k
  have hset := WalkSide.prefixSet_eq_stageSet (κ := κ) (b := b) (jumps := jumps)
    E () hℓ.le hins' hl (hD ℓ) hτ'
  have hchart := WalkSide.prefixChart_eq_chart (κ := κ) (b := b) (jumps := jumps)
    E () hℓ.le hins' hl (hD ℓ) hτ'
  rw [hpc, ← hpre, hset, hchart]
  rintro z ⟨hzfr, hzH⟩
  have hO := (ExplState.run κ b jumps (WalkSide.capSpec w ℓ θ τ) D
    (ℓ + 1)).2.2.2.2.1.dom.isOpen
  rw [hO.frontier_eq] at hzfr
  exact WalkLeaf.mem_stageSet_of_frontier (WalkSide.capSpec w ℓ θ τ) E ()
    (WalkSide.pieceRegular_capSpec D hℓ.le hins' hreg τ) (ℓ + 1) z hzH hzfr.1 hzfr.2

/-- Any physical model of an actual live prefix is the filling of its
raw prefix set. No physical filling identity is assumed. -/
theorem hull_eq_fillH_prefixSet
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1
        (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) (M : HullModel (prefixChart pc τ)) :
    M.hull = fillH (prefixSet pre pc τ) := by
  symm
  have havoid := WalkIntBridge.prefixChart_disjoint_prefixSet θ right D hreg hD hs hτ
  apply fillH_eq_of_frontier_subset M.isHull
  · intro z hz
    by_contra hzK
    have hzdom : z ∈ (prefixChart pc τ).dom := by
      change z ∈ ((prefixChart pc τ).dom : Set ℂ)
      rw [M.dom_eq]
      exact ⟨hz.2, hzK⟩
    exact Set.disjoint_left.1 havoid hzdom hz
  · rw [← M.dom_eq]
    exact (frontier_prefixChart_subset_prefixSet θ right D hreg hD hs hτ).trans
      subset_closure

end InteractingSLE.Theorem14.WalkIntFill
