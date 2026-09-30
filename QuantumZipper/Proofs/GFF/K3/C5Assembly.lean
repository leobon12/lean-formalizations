import QuantumZipper.Proofs.GFF.K3.C5KernelMeas
import QuantumZipper.Proofs.GFF.K3.C5prime

/-!
# GFF-K3, node C5 (via C5′): the pieces of `ℍ \ η[0,T]`

Blueprint `blueprint/EXT_PP_BLUEPRINT.md` §B (C5′).  For a curve-generated chain (`GenTrace`),
`U_T = ℍ \ η[0,T]` is the disjoint union of `D_T = ℍ \ K_T` and the countably many bubble sets
`Ω_τ` (`C5Interface.lean`).  Here they are enumerated as an `ℕ`-indexed family `c5Piece` (as
needed by C3, `dualNormSq_iUnion_of_pairwise_disjoint`), with: openness, pairwise
disjointness, union `= U_T`, and item 5 across pieces (`VTe_eq_zero_of_mem_c5Piece`).
-/

noncomputable section

open Set Filter Topology MeasureTheory Function
open scoped ENNReal

namespace QuantumZipper.K3

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {T : ℝ}

/-- The pieces of `ℍ \ η[0,T]`: `D_T` at index `0`, then the bubble set of the time encoded by
`m` at index `m + 1` (`∅` if `m` encodes no time). -/
def c5Piece (W : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ) (hS : (bubbleIdx W η T).Countable) : ℕ → Set ℂ
  | 0 => H \ fwdHull W T
  | m + 1 => (@Encodable.decode₂ _ hS.toEncodable m).elim ∅ fun τ => bubbleSet W η T τ.1

theorem c5Piece_succ (hS : (bubbleIdx W η T).Countable) (m : ℕ) :
    c5Piece W η T hS (m + 1) = ∅ ∨ ∃ τ : bubbleIdx W η T,
      @Encodable.encode _ hS.toEncodable τ = m ∧ c5Piece W η T hS (m + 1) = bubbleSet W η T τ.1 := by
  letI := hS.toEncodable
  simp only [c5Piece]
  cases h : Encodable.decode₂ (bubbleIdx W η T) m with
  | none => exact Or.inl rfl
  | some τ => exact Or.inr ⟨τ, Encodable.mem_decode₂.1 h, rfl⟩

/-- Label of a point of a piece: `D_T`, or a bubble time with its code. -/
theorem c5Piece_label (hS : (bubbleIdx W η T).Countable) {n : ℕ} {z : ℂ}
    (hz : z ∈ c5Piece W η T hS n) :
    (n = 0 ∧ z ∈ H \ fwdHull W T) ∨ ∃ τ : bubbleIdx W η T,
      n = @Encodable.encode _ hS.toEncodable τ + 1 ∧ z ∈ bubbleSet W η T τ.1 := by
  cases n with
  | zero => exact Or.inl ⟨rfl, hz⟩
  | succ m =>
    rcases c5Piece_succ hS m with h | ⟨τ, hτ, h⟩
    · rw [h] at hz; exact absurd hz (notMem_empty z)
    · rw [h] at hz; exact Or.inr ⟨τ, by rw [hτ], hz⟩

theorem c5Piece_subset (hg : GenTrace W η) (hT : 0 ≤ T) (hS : (bubbleIdx W η T).Countable)
    (n : ℕ) : c5Piece W η T hS n ⊆ H \ η '' Icc 0 T := fun z hz => by
  rcases c5Piece_label hS hz with ⟨-, h⟩ | ⟨τ, -, h⟩
  · exact hg.compl_fwdHull_subset hT h
  · exact h.1

theorem isOpen_c5Piece (hg : GenTrace W η) (hT : 0 ≤ T) (hS : (bubbleIdx W η T).Countable)
    (n : ℕ) : IsOpen (c5Piece W η T hS n) := by
  cases n with
  | zero => exact FwdHolo.isOpen_compl_fwdHull hg.contW hT
  | succ m =>
    rcases c5Piece_succ hS m with h | ⟨τ, -, h⟩
    · rw [h]; exact isOpen_empty
    · rw [h]; exact hg.isOpen_bubbleSet τ.2.1.2

/-- Two pieces sharing a point, or carrying points with equal swallowing times, coincide. -/
theorem c5Piece_eq_of_swallowTime_eq (hS : (bubbleIdx W η T).Countable) {n m : ℕ} {a b : ℂ}
    (ha : a ∈ c5Piece W η T hS n) (hb : b ∈ c5Piece W η T hS m)
    (hab : swallowTime W a = swallowTime W b) : n = m := by
  rcases c5Piece_label hS ha with ⟨rfl, haD⟩ | ⟨τ, rfl, haΩ⟩ <;>
    rcases c5Piece_label hS hb with ⟨rfl, hbD⟩ | ⟨τ', rfl, hbΩ⟩
  · rfl
  · exact absurd ⟨haD.1, hab ▸ hbΩ.2 ▸ ENNReal.ofReal_le_ofReal τ'.2.1.2⟩ haD.2
  · exact absurd ⟨hbD.1, hab ▸ haΩ.2 ▸ ENNReal.ofReal_le_ofReal τ.2.1.2⟩ hbD.2
  · have h := haΩ.2.symm.trans (hab.trans hbΩ.2)
    rw [ENNReal.ofReal_eq_ofReal_iff τ.2.1.1 τ'.2.1.1] at h
    rw [Subtype.ext h]

theorem pairwise_disjoint_c5Piece (hS : (bubbleIdx W η T).Countable) :
    Pairwise (Disjoint on c5Piece W η T hS) := fun n m hnm =>
  Set.disjoint_left.2 fun z hn hm => hnm (c5Piece_eq_of_swallowTime_eq hS hn hm rfl)

theorem iUnion_c5Piece (hg : GenTrace W η) (hT : 0 ≤ T) (hS : (bubbleIdx W η T).Countable) :
    ⋃ n, c5Piece W η T hS n = H \ η '' Icc 0 T := by
  letI := hS.toEncodable
  refine Subset.antisymm (iUnion_subset (c5Piece_subset hg hT hS)) ?_
  rw [hg.compl_image_eq_union hT]
  rintro z (hz | hz)
  · exact mem_iUnion.2 ⟨0, hz⟩
  · obtain ⟨τ, hτ, hz⟩ := mem_iUnion₂.1 hz
    refine mem_iUnion.2 ⟨Encodable.encode (⟨τ, hτ⟩ : bubbleIdx W η T) + 1, ?_⟩
    simp only [c5Piece, Encodable.encodek₂, Option.elim]
    exact hz

/-- **Item 5 across pieces.** Points of different pieces have `V_T = 0`. -/
theorem VTe_eq_zero_of_mem_c5Piece (hg : GenTrace W η) (hS : (bubbleIdx W η T).Countable)
    {n m : ℕ} (hnm : n ≠ m) {a b : ℂ} (ha : a ∈ c5Piece W η T hS n)
    (hb : b ∈ c5Piece W η T hS m) : VTe W T a b = 0 := by
  have hne : swallowTime W a ≠ swallowTime W b := fun h =>
    hnm (c5Piece_eq_of_swallowTime_eq hS ha hb h)
  have hle : min (swallowTime W a) (swallowTime W b) ≤ ENNReal.ofReal T := by
    rcases c5Piece_label hS ha with ⟨-, -⟩ | ⟨τ, -, haΩ⟩
    · rcases c5Piece_label hS hb with ⟨rfl, -⟩ | ⟨τ', -, hbΩ⟩
      · rcases c5Piece_label hS ha with ⟨rfl, -⟩ | ⟨τ, -, haΩ⟩
        · exact absurd rfl hnm
        · exact (min_le_left _ _).trans (haΩ.2 ▸ ENNReal.ofReal_le_ofReal τ.2.1.2)
      · exact (min_le_right _ _).trans (hbΩ.2 ▸ ENNReal.ofReal_le_ofReal τ'.2.1.2)
    · exact (min_le_left _ _).trans (haΩ.2 ▸ ENNReal.ofReal_le_ofReal τ.2.1.2)
  have hmem : ∀ {k z}, z ∈ c5Piece W η T hS k → z ∈ H := fun hz => by
    rcases c5Piece_label hS hz with ⟨-, h⟩ | ⟨τ, -, h⟩
    · exact h.1
    · exact h.1.1
  exact VTe_eq_zero_of_swallowTime_ne hg.contW (hmem ha) (hmem hb) hne hle

end QuantumZipper.K3
