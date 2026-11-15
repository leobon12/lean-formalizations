/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntClosedFinite

/-!
# Joint physical family selection allowing finite-piece endings

Combine the two actual closed-prefix sequences at a common natural index.
Taking the maximum of two selected indices gives whole-pool cofinality
and local coverage for both ordinary walks. No terminal-infinite lifetime
condition or pointwise physical selection hypothesis is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntClosed

open WalkBdry Exist.StagedLaw

/-- Two nested cofinal physical prefix sequences give a single joint
family, cofinal in every actual closed-time retained pair. -/
theorem exists_closedPair_family_of_prefix_families {sR sL : ExplState}
    (R : ℕ → ClosedPrefix sR) (L : ℕ → ClosedPrefix sL)
    (hmR : Monotone (fun n => (R n).raw)) (hmL : Monotone (fun n => (L n).raw))
    (hdR : ∀ Q : ClosedPrefix sR, ∃ n, Q.raw ⊆ (R n).raw)
    (hdL : ∀ Q : ClosedPrefix sL, ∃ n, Q.raw ⊆ (L n).raw)
    (hlR : ∀ p : ℂ, ∃ n, wsetOf sR ∩ ball p 1 ⊆ (R n).raw)
    (hlL : ∀ p : ℂ, ∃ n, wsetOf sL ∩ ball p 1 ⊆ (L n).raw) :
    ∃ pair : ℕ → ClosedPair sR sL, Monotone (fun n => (pair n).raw) ∧
      (∀ J : ClosedPair sR sL, ∃ n, J.raw ⊆ (pair n).raw) ∧
      ∀ p : ℂ, ∃ n, (wsetOf sR ∪ wsetOf sL) ∩ ball p 1 ⊆ (pair n).raw := by
  choose pair hR hL using fun n => exists_closedPair (R n) (L n)
  have hraw (n : ℕ) : (pair n).raw = (R n).raw ∪ (L n).raw := by
    rw [ClosedPair.raw, hR n, hL n]
  refine ⟨pair, ?_, ?_, ?_⟩
  · intro m n hmn
    change (pair m).raw ⊆ (pair n).raw
    rw [hraw m, hraw n]
    exact union_subset_union (hmR hmn) (hmL hmn)
  · intro J
    obtain ⟨r, hr⟩ := hdR J.right
    obtain ⟨l, hl⟩ := hdL J.left
    refine ⟨max r l, ?_⟩
    rw [hraw]
    exact union_subset_union (hr.trans (hmR (le_max_left r l)))
      (hl.trans (hmL (le_max_right r l)))
  · intro p
    obtain ⟨r, hr⟩ := hlR p
    obtain ⟨l, hl⟩ := hlL p
    refine ⟨max r l, ?_⟩
    rw [hraw]
    rintro z ⟨hz | hz, hball⟩
    · exact Or.inl (hmR (le_max_left r l) (hr ⟨hz, hball⟩))
    · exact Or.inr (hmL (le_max_right r l) (hl ⟨hz, hball⟩))

/-- Actual regular boundary runs with nonempty recorded piece lists
admit a nested cofinal physical family, allowing finite last lifetimes. -/
theorem exists_closedPair_family_of_last_pieces {κ : ℝ} {b : ℝ → ℝ}
    {jumps : Finset ℝ} (θR θL : ℝ) (rightR rightL : Bool)
    (DR DL : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hregR : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θR rightR)
      DR (k + 1)).2.2.2.1 k = some (c, θ') → GW1P.PieceRegular (DR k).1
        (min (instrTime (boundaryWalkSpec b jumps θR rightR) k) (DR k).2))
    (hregL : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θL rightL)
      DL (k + 1)).2.2.2.1 k = some (c, θ') → GW1P.PieceRegular (DL k).1
        (min (instrTime (boundaryWalkSpec b jumps θL rightL) k) (DL k).2))
    (hDR : ∀ k, Exist.Staged.IsRegularDriver (DR k))
    (hDL : ∀ k, Exist.Staged.IsRegularDriver (DL k))
    {preR preL : List Piece} {pcR pcL : Piece}
    (hsR : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θR rightR) DR
      (boundaryWalkSpec b jumps θR rightR).2.2.length).1 = preR ++ [pcR])
    (hsL : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θL rightL) DL
      (boundaryWalkSpec b jumps θL rightL).2.2.length).1 = preL ++ [pcL]) :
    let sR := ExplState.run κ b jumps (boundaryWalkSpec b jumps θR rightR) DR
      (boundaryWalkSpec b jumps θR rightR).2.2.length
    let sL := ExplState.run κ b jumps (boundaryWalkSpec b jumps θL rightL) DL
      (boundaryWalkSpec b jumps θL rightL).2.2.length
    ∃ pair : ℕ → ClosedPair sR sL, Monotone (fun n => (pair n).raw) ∧
      (∀ J : ClosedPair sR sL, ∃ n, J.raw ⊆ (pair n).raw) ∧
      ∀ p : ℂ, ∃ n, (wsetOf sR ∪ wsetOf sL) ∩ ball p 1 ⊆ (pair n).raw := by
  obtain ⟨R, hmR, hdR, hlR⟩ := exists_closedPrefix_family_of_last_piece
    θR rightR DR hregR hDR hsR
  obtain ⟨L, hmL, hdL, hlL⟩ := exists_closedPrefix_family_of_last_piece
    θL rightL DL hregL hDL hsL
  exact exists_closedPair_family_of_prefix_families R L hmR hmL hdR hdL hlR hlL

end InteractingSLE.Theorem14.WalkIntClosed
