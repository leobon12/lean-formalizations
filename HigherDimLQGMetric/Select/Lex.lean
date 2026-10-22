import HigherDimLQGMetric.Select.GeodProper

/-!
# Lexicographic minima of compact subsets

Packet M3a, MA1 A10. A countable separating family of continuous real functions
picks a unique point from each nonempty compact set. The explicit characterization
by finite prefixes is used to prove that the resulting partial graph is Borel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology

namespace HigherDimLQGMetric

variable {E : Type*} [TopologicalSpace E] [T2Space E]

/-- The set surviving the first `m` lexicographic minimizations. -/
def lexPrefixSet (K : Set E) (φ : ℕ → E → ℝ) : ℕ → Set E
  | 0 => K
  | m + 1 => {z | z ∈ lexPrefixSet K φ m ∧
      ∀ w ∈ lexPrefixSet K φ m, φ m z ≤ φ m w}

/-- `z` has no competitor whose first differing coordinate is smaller. -/
def IsLexMin (K : Set E) (φ : ℕ → E → ℝ) (z : E) : Prop :=
  z ∈ K ∧ ∀ m, ∀ w ∈ K,
    (∀ i < m, φ i w = φ i z) → φ m z ≤ φ m w

omit [TopologicalSpace E] [T2Space E] in
theorem lexPrefixSet_succ_subset (K : Set E) (φ : ℕ → E → ℝ) (m : ℕ) :
    lexPrefixSet K φ (m + 1) ⊆ lexPrefixSet K φ m := fun _ hz => hz.1

omit [T2Space E] in
theorem isClosed_lexPrefixSet (K : Set E) (hK : IsClosed K)
    (φ : ℕ → E → ℝ) (hφ : ∀ m, Continuous (φ m)) :
    ∀ m, IsClosed (lexPrefixSet K φ m) := by
  intro m
  induction m with
  | zero => exact hK
  | succ m ih =>
    have hmin : IsClosed {z : E | ∀ w ∈ lexPrefixSet K φ m, φ m z ≤ φ m w} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun w => isClosed_iInter fun _ =>
        isClosed_le (hφ m) continuous_const
    change IsClosed (lexPrefixSet K φ m ∩
      {z : E | ∀ w ∈ lexPrefixSet K φ m, φ m z ≤ φ m w})
    exact ih.inter hmin

theorem nonempty_lexPrefixSet (K : Set E) (hK : IsCompact K) (hKn : K.Nonempty)
    (φ : ℕ → E → ℝ) (hφ : ∀ m, Continuous (φ m)) :
    ∀ m, (lexPrefixSet K φ m).Nonempty := by
  have hclosed := isClosed_lexPrefixSet K hK.isClosed φ hφ
  have hsub : ∀ m, lexPrefixSet K φ m ⊆ K := by
    intro m
    induction m with
    | zero => exact Subset.rfl
    | succ m ih => exact (lexPrefixSet_succ_subset K φ m).trans ih
  intro m
  induction m with
  | zero => exact hKn
  | succ m ih =>
    have hcompact : IsCompact (lexPrefixSet K φ m) :=
      hK.of_isClosed_subset (hclosed m) (hsub m)
    obtain ⟨z, hz, hmin⟩ := hcompact.exists_isMinOn ih (hφ m).continuousOn
    exact ⟨z, hz, fun w hw => hmin hw⟩

/-- The nested compact prefix sets have a common point. -/
theorem exists_mem_all_lexPrefixSet (K : Set E) (hK : IsCompact K) (hKn : K.Nonempty)
    (φ : ℕ → E → ℝ) (hφ : ∀ m, Continuous (φ m)) :
    ∃ z : E, ∀ m, z ∈ lexPrefixSet K φ m := by
  have hn := nonempty_lexPrefixSet K hK hKn φ hφ
  have hclosed := isClosed_lexPrefixSet K hK.isClosed φ hφ
  have h := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (lexPrefixSet K φ) (lexPrefixSet_succ_subset K φ) hn hK hclosed
  obtain ⟨z, hz⟩ := h
  exact ⟨z, fun m => mem_iInter.mp hz m⟩

omit [TopologicalSpace E] [T2Space E] in
theorem isLexMin_of_mem_all_lexPrefixSet (K : Set E) (φ : ℕ → E → ℝ)
    {z : E} (hz : ∀ m, z ∈ lexPrefixSet K φ m) : IsLexMin K φ z := by
  refine ⟨hz 0, ?_⟩
  intro m w hw heq
  have hwm : ∀ k ≤ m, w ∈ lexPrefixSet K φ k := by
    intro k hk
    induction k with
    | zero => exact hw
    | succ k ih =>
      have hwi := ih (by omega)
      have hzi := hz (k + 1)
      exact ⟨hwi, fun u hu => by
        rw [heq k (by omega)]
        exact hzi.2 u hu⟩
  exact (hz (m + 1)).2 w (hwm m le_rfl)

/-- A compact nonempty set has a unique lexicographic minimum when `φ` separates points. -/
theorem existsUnique_isLexMin (K : Set E) (hK : IsCompact K) (hKn : K.Nonempty)
    (φ : ℕ → E → ℝ) (hφ : ∀ m, Continuous (φ m))
    (hsep : ∀ z w : E, (∀ m, φ m z = φ m w) → z = w) :
    ∃! z : E, IsLexMin K φ z := by
  obtain ⟨z, hz⟩ := exists_mem_all_lexPrefixSet K hK hKn φ hφ
  refine ⟨z, isLexMin_of_mem_all_lexPrefixSet K φ hz, ?_⟩
  intro w hw
  apply hsep w z
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hzw : ∀ i < m, φ i w = φ i z := fun i hi => ih i hi
    have hwz : ∀ i < m, φ i z = φ i w := fun i hi => (ih i hi).symm
    exact le_antisymm (hw.2 m z (isLexMin_of_mem_all_lexPrefixSet K φ hz).1 hwz)
      ((isLexMin_of_mem_all_lexPrefixSet K φ hz).2 m w hw.1 hzw)

end HigherDimLQGMetric
