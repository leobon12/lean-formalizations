/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsPiece
import InteractingSLE.Spec.Supplement.WalkSideSpec
import InteractingSLE.Spec.Supplement.GW2aContStepAux
import InteractingSLE.Spec.Supplement.SB2Remainder

/-!
# The recorded pieces of a boundary walk near a simple point

Packet PROVE-WALK-WORDS. Along a boundary walk whose launched pieces are regular (`GW1P.PieceRegular`) and simple
(`GW1Z.IsSimplePiece`, the content of `WalkPiecesSimple`):

* `exists_pieceData`: every recorded piece `pc` (in a decomposition `pre ++ pc :: post` of the final pieces) carries
  `PieceData` with old set the union of the earlier pieces;
* `isClosed_tipSet_of_mem`: every recorded piece is closed;
* `tipAt_zero_of_mem_post`: a point of an earlier piece lying on a later piece is that later piece's start;
* **`exists_ball_walk_window`**: near a point `g(t₀)` of a piece (`0 < t₀`) that is no later piece's start, the walk is
  the piece's own window `g((lo, hi))` around `t₀`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry Exist.StagedLaw

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Every recorded piece carries `PieceData`.** -/
theorem exists_pieceData (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2))
    (hsimple : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1Z.IsSimplePiece c (D k).1 (min (instrTime spec k) (D k).2) (SB.prefixPhysSet κ b jumps spec D k))
    {n : ℕ} {pre post : List Piece} {pc : Piece} (hs : (ExplState.run κ b jumps spec D n).1 = pre ++ pc :: post) :
    ∃ (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) f W α := by
  obtain ⟨ℓ, -, θ', hl, hpre, hpc⟩ := WalkSide.exists_launch_of_pieces_eq (κ := κ) (b := b) (jumps := jumps) spec D n hs
  subst hpc hpre
  obtain ⟨f, α, C, hf, hC, hW0, hW, hα, htr, hinj, havoid⟩ := hsimple ℓ _ θ' hl
  have hconf := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec D ℓ
    fun j _ c θ hlj => hreg j c θ hlj).1
  refine ⟨f, (D ℓ).1, α, ⟨hconf, hf, ⟨C, hC⟩, hW0, hW, hα, htr, hinj, fun t ht htS hA => ?_, rfl⟩⟩
  refine havoid t ht htS ?_
  simp only [SB.prefixPhysSet, mem_union, mem_iUnion, exists_prop] at hA ⊢
  exact Or.inl (Or.inr hA)

end Run

section Walk

variable {L : List Piece}

/-- A recorded piece with `PieceData` is closed. -/
theorem PieceData.isClosed_tipSet {pc : Piece} {A : Set ℂ} {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {α : ℝ≥0 → ℂ}
    (h : PieceData pc A f W α) : IsClosed (pc.1.tipSet pc.2.1 pc.2.2) := by
  rw [h.tipSet_eq]
  exact h.isClosed_image (isClosed_le (ENNReal.continuous_coe) continuous_const) subset_rfl

/-- **A point of an earlier piece lying on a later piece is the later piece's start.** -/
theorem PieceData.tipAt_zero_of_mem {pc pc' : Piece} {A' : Set ℂ} {f' : ℂ → ℂ} {W' : ℝ≥0 → ℝ} {α' : ℝ≥0 → ℂ}
    (h' : PieceData pc' A' f' W' α') (hA : pc.1.tipSet pc.2.1 pc.2.2 ⊆ A') {z : ℂ}
    (hz : z ∈ pc'.1.tipSet pc'.2.1 pc'.2.2) (hzpc : z ∈ pc.1.tipSet pc.2.1 pc.2.2) :
    pc'.1.tipAt pc'.2.1 0 z := by
  rw [h'.tipSet_eq] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | h0
  · rw [← h0]; exact h'.tipAt (by simp)
  · exact absurd (hA hzpc) (h'.avoid t h0 ht)

/-- **Near a simple point of a piece, the walk is the piece's own window.** -/
theorem exists_ball_walk_window {pre post : List Piece} {pc : Piece} (hL : L = pre ++ pc :: post)
    {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {α : ℝ≥0 → ℂ} (hd : PieceData pc (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) f W α)
    (hclosed : ∀ p' ∈ L, IsClosed (p'.1.tipSet p'.2.1 p'.2.2))
    (hpost : ∀ p' ∈ post, ∀ z ∈ p'.1.tipSet p'.2.1 p'.2.2, z ∈ pc.1.tipSet pc.2.1 pc.2.2 → p'.1.tipAt p'.2.1 0 z)
    {t₀ : ℝ≥0} (ht₀ : 0 < t₀) (ht₀S : (t₀ : ℝ≥0∞) ≤ pc.2.2)
    (hnostart : ∀ p' ∈ post, ¬ p'.1.tipAt p'.2.1 0 (f (α t₀))) {lo hi : ℝ} (hlo : lo < t₀) (hhi : (t₀ : ℝ) < hi) :
    ∃ ρ > 0, ∀ z ∈ (⋃ p ∈ L, p.1.tipSet p.2.1 p.2.2) ∩ ball (f (α t₀)) ρ,
      ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ pc.2.2 ∧ lo < t ∧ (t : ℝ) < hi ∧ z = f (α t) := by
  set g : ℝ≥0 → ℂ := fun t => f (α t) with hgdef
  set D : Set ℝ≥0 := {t | (t : ℝ≥0∞) ≤ pc.2.2} with hDdef
  have hDc : IsClosed D := isClosed_le ENNReal.continuous_coe continuous_const
  set F : Set ℝ≥0 := D ∩ {t | (t : ℝ) ≤ lo ∨ hi ≤ t} with hFdef
  have hFc : IsClosed F := hDc.inter ((isClosed_le NNReal.continuous_coe continuous_const).union
    (isClosed_le continuous_const NNReal.continuous_coe))
  set K : Set ℂ := (⋃ p' ∈ {x | x ∈ pre ++ post}, p'.1.tipSet p'.2.1 p'.2.2) ∪ g '' F with hKdef
  have hKc : IsClosed K := by
    refine IsClosed.union ?_ (hd.isClosed_image hFc inter_subset_left)
    refine (List.finite_toSet (pre ++ post)).isClosed_biUnion fun p' hp' => hclosed p' ?_
    rw [hL]
    rcases List.mem_append.1 hp' with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  have hpK : g t₀ ∉ K := by
    rintro (hK | ⟨t, ⟨htD, ht⟩, he⟩)
    · obtain ⟨p', hp', hz⟩ := mem_iUnion₂.1 hK
      rcases List.mem_append.1 hp' with h | h
      · refine hd.avoid t₀ ht₀ ht₀S ?_
        simp only [mem_iUnion, exists_prop]
        exact ⟨p', h, hz⟩
      · refine hnostart p' h (hpost p' h _ hz ?_)
        rw [hd.tipSet_eq]
        exact ⟨t₀, ht₀S, rfl⟩
    · have := hd.inj htD ht₀S he
      subst this
      rcases ht with ht | ht <;> linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl _ hpK
  refine ⟨ρ, hρ, fun z ⟨hz, hzb⟩ => ?_⟩
  have hzK : z ∉ K := hball hzb
  simp only [mem_iUnion, exists_prop] at hz
  obtain ⟨p', hp', hzp⟩ := hz
  rw [hL] at hp'
  have hKpre : ∀ p' ∈ pre ++ post, z ∈ p'.1.tipSet p'.2.1 p'.2.2 → z ∈ K := fun p' hp' hz' =>
    Or.inl (mem_biUnion (x := p') hp' hz')
  rcases List.mem_append.1 hp' with h | h
  · exact absurd (hKpre p' (List.mem_append_left _ h) hzp) hzK
  · rcases List.mem_cons.1 h with rfl | h
    · rw [hd.tipSet_eq] at hzp
      obtain ⟨t, htD, rfl⟩ := hzp
      by_cases hwin : lo < t ∧ (t : ℝ) < hi
      · exact ⟨t, htD, hwin.1, hwin.2, rfl⟩
      · refine absurd (Or.inr ⟨t, ⟨htD, ?_⟩, rfl⟩) hzK
        rw [not_and_or, not_lt, not_lt] at hwin
        exact hwin
    · exact absurd (hKpre p' (List.mem_append_right _ h) hzp) hzK

end Walk

end InteractingSLE.Theorem14.WalkWords
