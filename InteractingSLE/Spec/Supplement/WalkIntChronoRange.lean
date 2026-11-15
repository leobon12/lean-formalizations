/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntChronoHistory
import InteractingSLE.Spec.Supplement.GW2aContArc

/-!
# A capped physical prefix lies in the complete physical walk

The ordinary prefix inclusion already follows from the stopped-piece API.
The connector case reuses the existing fact that a step preserves or
appends the connector list. Real points and connectors are retained here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntChrono

open WalkSide Exist.StagedLaw

/-- Existing connector records remain present at all later instructions. -/
theorem mem_arcs_run_mono {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (w : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n m : ℕ} {A : Set ℝ}
    (hA : A ∈ (ExplState.run κ b jumps w D n).2.1) (hnm : n ≤ m) :
    A ∈ (ExplState.run κ b jumps w D m).2.1 := by
  induction m, hnm using Nat.le_induction with
  | base => exact hA
  | succ m _ ih =>
    rcases GW2aCont.arcs_run_succ (κ := κ) (b := b) (jumps := jumps) w D m with h | ⟨A', h⟩
    · rwa [h]
    · rw [h]
      exact List.mem_append_left _ ih

/-- Inclusion of the full physical capped carrier, including every real
ordinary point and connector, in the complete program's physical set. -/
theorem capped_physical_subset_walk {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {w : ExplSpec} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} {θ θ' : ℝ} {c : Chart}
    (hk : k < w.2.2.length) (hins : w.2.2[k]? = some (Sum.inl (θ, ⊤)))
    (hl : (ExplState.run κ b jumps w D (k + 1)).2.2.2.1 k = some (c, θ'))
    (hD : Exist.Staged.IsRegularDriver (D k)) {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < (D k).2) :
    SB.prefixPhysSet κ b jumps (WalkSide.capSpec w k θ τ) D (k + 1) ⊆
      ExplState.physSet κ b jumps w D := by
  have hτ' : (τ : ℝ≥0∞) < min ⊤ (D k).2 := by simpa only [min_top_left] using hτ
  have hpiece := WalkSide.pieces_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps)
    hk.le hins D hl (τ : ℝ≥0∞)
  have harcs : (ExplState.run κ b jumps (WalkSide.capSpec w k θ τ) D (k + 1)).2.1 =
      (ExplState.run κ b jumps w D k).2.1 := by
    rw [WalkSide.run_capSpec_succ hk.le D, GW2aCont.arcs_flowStep]
  have hfull : recPiece (ExplState.run κ b jumps w D k) (D k) ⊤ ∈
      (ExplState.run κ b jumps w D w.2.2.length).1 := by
    apply WalkSide.mem_pieces_run_mono w D (n := k + 1) _ _ hk
    obtain ⟨-, he, -⟩ := eq_launch_of_launches w D hl
    have htime : instrTime w k = ⊤ := by simp only [instrTime, hins]
    rw [he, CounterflowRange.pieces_launch, htime]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  intro z hz
  change z ∈ {(w.1 : ℂ)} ∪
    (⋃ p ∈ (ExplState.run κ b jumps (WalkSide.capSpec w k θ τ) D (k + 1)).1,
      p.1.tipSet p.2.1 p.2.2) ∪
    ⋃ A ∈ (ExplState.run κ b jumps (WalkSide.capSpec w k θ τ) D (k + 1)).2.1,
      ((↑) : ℝ → ℂ) '' A at hz
  change z ∈ {(w.1 : ℂ)} ∪
    (⋃ p ∈ (ExplState.run κ b jumps w D w.2.2.length).1, p.1.tipSet p.2.1 p.2.2) ∪
    ⋃ A ∈ (ExplState.run κ b jumps w D w.2.2.length).2.1, ((↑) : ℝ → ℂ) '' A
  rcases hz with (hz | hz) | hz
  · exact Or.inl (Or.inl hz)
  · apply Or.inl ∘ Or.inr
    obtain ⟨p, hp, hz⟩ := mem_iUnion₂.1 hz
    rw [hpiece] at hp
    rcases List.mem_append.1 hp with hp | hp
    · exact mem_iUnion₂.2 ⟨p, WalkSide.mem_pieces_run_mono w D hp _ hk.le, hz⟩
    · rw [List.mem_singleton] at hp
      subst p
      rw [← WalkSide.tipSet_recPiece _ hD hτ'] at hz
      obtain ⟨t, ht, hlim⟩ := hz
      exact mem_iUnion₂.2 ⟨_, hfull, t, ht.trans hτ'.le, hlim⟩
  · obtain ⟨A, hA, hz⟩ := mem_iUnion₂.1 hz
    rw [harcs] at hA
    exact Or.inr (mem_iUnion₂.2 ⟨A, mem_arcs_run_mono w D hA hk.le, hz⟩)

end InteractingSLE.Theorem14.WalkIntChrono
