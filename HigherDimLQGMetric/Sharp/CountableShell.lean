import HigherDimLQGMetric.Shell.Across

/-!
# Countable forms of shell functionals

The internal metric is continuous on an open domain for a length metric. Thus
the sphere supremum and set-distance infimum can be read on dense sequences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem exists_denseSeq_rd {S : Set (Rd d)} (hS : S.Nonempty) :
    ∃ q : ℕ → Rd d, (∀ n, q n ∈ S) ∧ S ⊆ closure (range q) := by
  have : Nonempty S := hS.to_subtype
  refine ⟨fun n => (TopologicalSpace.denseSeq S n : Rd d),
    fun n => (TopologicalSpace.denseSeq S n).2, ?_⟩
  intro x hx
  rw [_root_.mem_closure_iff]
  intro o ho hxo
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq S).exists_mem_open
    (ho.preimage continuous_subtype_val) ⟨⟨x, hx⟩, hxo⟩
  exact ⟨_, hn, n, rfl⟩

theorem mem_of_dense_rd {f : Rd d × Rd d → ℝ≥0∞} {V A B : Set (Rd d)}
    (hf : ContinuousOn f (V ×ˢ V))
    {a b : ℕ → Rd d} (ha : ∀ n, a n ∈ V) (hb : ∀ n, b n ∈ V)
    (hA : A ⊆ closure (range a)) (hB : B ⊆ closure (range b))
    {Z : Set ℝ≥0∞} (hZ : IsClosed Z)
    (hT : ∀ i j, f (a i, b j) ∈ Z) {x y : Rd d}
    (hx : x ∈ A) (hy : y ∈ B) (hxV : x ∈ V) (hyV : y ∈ V) :
    f (x, y) ∈ Z := by
  have hs : range (Prod.map a b) ⊆ V ×ˢ V := by
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨ha i, hb j⟩
  have hmem : (x, y) ∈ closure (range (Prod.map a b)) := by
    rw [range_prodMap, closure_prod_eq]
    exact ⟨hA hx, hB hy⟩
  have := ContinuousWithinAt.mem_closure_image
    ((hf (x, y) ⟨hxV, hyV⟩).mono hs) hmem
  refine closure_minimal ?_ hZ this
  rintro _ ⟨_, ⟨⟨i, j⟩, rfl⟩, rfl⟩
  exact hT i j

theorem sphereDiam_eq_iSup_dense (D : ContMetric d) (hD : D.IsLength)
    {V A : Set (Rd d)} (hV : IsOpen V) (hAV : A ⊆ V)
    {a : ℕ → Rd d} (haA : ∀ n, a n ∈ A)
    (hA : A ⊆ closure (range a)) :
    (⨆ u ∈ A, ⨆ v ∈ A, D.internal V u v) =
      ⨆ p : ℕ × ℕ, D.internal V (a p.1) (a p.2) := by
  refine le_antisymm (iSup₂_le fun u hu => iSup₂_le fun v hv => ?_) (iSup_le fun p => ?_)
  · exact mem_of_dense_rd (f := fun p : Rd d × Rd d => D.internal V p.1 p.2)
      (D.continuousOn_internal hD hV) (fun n => hAV (haA n))
      (fun n => hAV (haA n)) hA hA isClosed_Iic
      (fun i j => le_iSup (fun p : ℕ × ℕ => D.internal V (a p.1) (a p.2)) (i, j))
      hu hv (hAV hu) (hAV hv)
  · exact le_iSup₂_of_le (a p.1) (haA p.1)
      (le_iSup₂_of_le (a p.2) (haA p.2) le_rfl)

theorem setDistIn_eq_iInf_dense (D : ContMetric d) (hD : D.IsLength)
    {V A B : Set (Rd d)} (hV : IsOpen V) (hAV : A ⊆ V) (hBV : B ⊆ V)
    {a b : ℕ → Rd d} (ha : ∀ n, a n ∈ A) (hb : ∀ n, b n ∈ B)
    (hA : A ⊆ closure (range a)) (hB : B ⊆ closure (range b)) :
    setDistIn D V A B = ⨅ p : ℕ × ℕ, D.internal V (a p.1) (b p.2) := by
  unfold setDistIn
  refine le_antisymm
    (le_iInf fun p => iInf₂_le_of_le (a p.1) (ha p.1)
      (iInf₂_le_of_le (b p.2) (hb p.2) le_rfl))
    (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  exact mem_of_dense_rd (f := fun p : Rd d × Rd d => D.internal V p.1 p.2)
    (D.continuousOn_internal hD hV) (fun n => hAV (ha n))
    (fun n => hBV (hb n)) hA hB isClosed_Ici
    (fun i j => iInf_le (fun p : ℕ × ℕ => D.internal V (a p.1) (b p.2)) (i, j))
    hx hy (hAV hx) (hBV hy)

end HigherDimLQGMetric
