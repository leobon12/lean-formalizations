/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1Bookkeep

/-!
# GW1: chronological arcs and the terminal chain

The finite arcs are appended in chronological order. A new arc meets the old history only at its
initial point. The induction below turns these forward intersection conditions into `ChainOK`,
whose conditions compare each arc with the entire subsequent history. Both orientations use
the same construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW1WalkChain

open GW1X GW1Bookkeep

/-- A finite chronological history, starting at `x`, with retained range `A` and endpoint `q`.
Zero-length pieces contribute no arc. -/
inductive ArcHistory (x : ℂ) : Set ℂ → ℂ → Prop
  | root : ArcHistory x {x} x
  | append {A : Set ℂ} {q : ℂ} (past : ArcHistory x A q) (α : ℝ≥0 → ℂ)
      (arc : IsArc α) (upper : ∀ t ∈ Iic (1 : ℝ≥0), 0 ≤ (α t).im)
      (start : α 0 = q) (meet : ∀ t ∈ Iic (1 : ℝ≥0), α t ∈ A → t = 0) :
      ArcHistory x (A ∪ α '' Iic 1) (α 1)

theorem chainStart_mem (L : List (ℝ≥0 → ℂ)) (ρ : ℝ≥0 → ℂ) :
    chainStart L ρ ∈ chainSet L ρ := by
  cases L with
  | nil => exact Or.inr ⟨0, rfl⟩
  | cons α L =>
    rw [chainSet_cons]
    exact Or.inl ⟨0, by simp only [mem_Iic, zero_le], rfl⟩

theorem ArcHistory.endpoint_mem {x q : ℂ} {A : Set ℂ} (h : ArcHistory x A q) : q ∈ A := by
  cases h with
  | root => exact mem_singleton _
  | append _ α _ _ _ _ => exact Or.inr ⟨1, mem_Iic.2 le_rfl, rfl⟩

/-- A terminal chain meeting the finite history only at its current endpoint can be prepended
by every arc of the history. This changes chronological intersection order to `ChainOK`. -/
theorem ArcHistory.prepend {x q : ℂ} {A : Set ℂ} (h : ArcHistory x A q)
    (L : List (ℝ≥0 → ℂ)) (ρ : ℝ≥0 → ℂ) (hL : ChainOK L ρ)
    (hstart : chainStart L ρ = q)
    (hmeet : ∀ z ∈ chainSet L ρ, z ∈ A → z = q) :
    ∃ L' : List (ℝ≥0 → ℂ), ChainOK L' ρ ∧ chainStart L' ρ = x ∧
      chainSet L' ρ = A ∪ chainSet L ρ := by
  induction h generalizing L with
  | root =>
    refine ⟨L, hL, hstart, ?_⟩
    symm
    apply union_eq_right.2
    intro z hz
    rw [mem_singleton_iff] at hz
    rw [hz, ← hstart]
    exact chainStart_mem L ρ
  | @append A q past α hα hupper hα0 hαmeet ih =>
    have hC : ChainOK (α :: L) ρ := by
      refine ⟨hα, hupper, hstart.symm, ?_, hL⟩
      intro t ht hmem
      apply hα.2 ht (mem_Iic.2 le_rfl)
      exact hmeet _ hmem (Or.inr ⟨t, ht, rfl⟩)
    have hM : ∀ z ∈ chainSet (α :: L) ρ, z ∈ A → z = q := by
      intro z hz hA
      rw [chainSet_cons] at hz
      rcases hz with ⟨t, ht, rfl⟩ | hz
      · rw [hαmeet t ht hA, hα0]
      · have heq := hmeet z hz (Or.inl hA)
        have hbad : α 1 ∈ A := heq ▸ hA
        have := hαmeet 1 (mem_Iic.2 le_rfl) hbad
        exact False.elim (one_ne_zero this)
    obtain ⟨L', hL', hs, hset⟩ := ih (α :: L) hC hα0 hM
    refine ⟨L', hL', hs, ?_⟩
    rw [hset, chainSet_cons, union_assoc]

/-- Closing a finite chronological history with a proper terminal curve gives exactly the
terminal-state representation required by GW1Y. -/
theorem ArcHistory.complete {x q : ℂ} {A : Set ℂ} (h : ArcHistory x A q)
    {ρ : ℝ≥0 → ℂ} (hρ0 : ρ 0 = q)
    (hmeet : ∀ t, ρ t ∈ A → t = 0) :
    ∃ L : List (ℝ≥0 → ℂ), ChainOK L ρ ∧ chainStart L ρ = x ∧
      chainSet L ρ = A ∪ range ρ := by
  obtain ⟨L, hL, hs, hset⟩ := h.prepend [] ρ trivial hρ0 (by
    intro z hz hA
    have hz' : z ∈ range ρ := by
      simpa only [chainSet, List.not_mem_nil, iUnion_of_empty, iUnion_empty, empty_union] using hz
    obtain ⟨t, rfl⟩ := hz'
    rw [hmeet t hA, hρ0])
  refine ⟨L, hL, hs, ?_⟩
  simpa only [chainSet, List.not_mem_nil, iUnion_of_empty, iUnion_empty, empty_union] using hset

theorem ArcHistory.walkChainRepresentation {x : ℝ} {q : ℂ} {A : Set ℂ}
    (h : ArcHistory (x : ℂ) A q) {s : ExplState} {ρ : ℝ≥0 → ℂ}
    (hρ : Supp9B.IsProperCurve ρ) (hρ0 : ρ 0 = q)
    (hmeet : ∀ t, ρ t ∈ A → t = 0) (hset : statePhysicalSet x s = A ∪ range ρ) :
    WalkChainRepresentation x s := by
  obtain ⟨L, hL, hs, hS⟩ := h.complete hρ0 hmeet
  exact ⟨L, ρ, hρ, hL, hs, hS.trans hset.symm⟩

end InteractingSLE.Theorem14.GW1WalkChain
