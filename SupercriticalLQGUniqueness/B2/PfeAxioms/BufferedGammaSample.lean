import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaUnitSpeed

 









set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open PfeWeyl

theorem sampled_buffered_skeleton
    (D : LSCMetric) {V K : Set ℂ} {Q : ℝ → ℂ} {L : ℝ}
    (hQ : D.IsCurve Q 0 L)
    (hQV : ∀ u ∈ Icc 0 L, Q u ∈ V)
    (hQK : ∀ u ∈ Icc 0 L, Q u ∈ interior K)
    (hfinite : D.len Q 0 L < ∞)
    {ε r : ℝ≥0∞}
    (hnear : D.len Q 0 L <
      D.internal V
        (⟨Q 0, hQV 0 ⟨le_rfl, hQ.1⟩⟩,
          ⟨Q L, hQV L ⟨hQ.1, le_rfl⟩⟩) + ε)
    (hrfin : r < ∞)
    (N : ℕ) (t : Fin (N + 2) → ℝ)
    (htmem : ∀ j, t j ∈ Icc 0 L)
    (htinc : ∀ j : Fin (N + 1),
      t (Fin.castSucc j) ≤ t j.succ)
    (hwidth : ∀ j : Fin (N + 1),
      ε ≤ D.len Q (t (Fin.castSucc j)) (t j.succ) ∧
        D.len Q (t (Fin.castSucc j)) (t j.succ) < r) :
    ∃ a b : Fin (N + 1) → V,
      (∀ i : Fin N, b (Fin.castSucc i) = a i.succ) ∧
      (∀ i, (a i : ℂ) ∈ interior K) ∧
      (∀ i, D ((a i : ℂ), (b i : ℂ)) < r) ∧
      (∀ i, a i ≠ b i) ∧
      (∀ i : Fin N, IsNonsingular D (b (Fin.castSucc i))) := by
  let a : Fin (N + 1) → V :=
    fun j => ⟨Q (t (Fin.castSucc j)), hQV _ (htmem _)⟩
  let b : Fin (N + 1) → V :=
    fun j => ⟨Q (t j.succ), hQV _ (htmem _)⟩
  have hnonzero : ∀ j : Fin (N + 1), a j ≠ b j := by
    intro j heq
    have hloop : Q (t (Fin.castSucc j)) = Q (t j.succ) :=
      congrArg Subtype.val heq
    have hshortLoop := near_minimal_buffered_loop_short D hQ hQV
      (htmem (Fin.castSucc j)) (htmem j.succ) (htinc j) hloop hnear hfinite
    exact (not_lt_of_ge (hwidth j).1) hshortLoop
  have hshort : ∀ j : Fin (N + 1), D ((a j : ℂ), (b j : ℂ)) < r := by
    intro j
    exact (LSCMetric.apply_le_len D Q (htinc j)).trans_lt (hwidth j).2
  refine ⟨a, b, ?_, ?_, hshort, hnonzero, ?_⟩
  · intro i
    apply Subtype.ext
    change Q (t (Fin.castSucc i).succ) = Q (t (Fin.castSucc i.succ))
    congr 1
  · intro j
    exact hQK _ (htmem (Fin.castSucc j))
  · intro i
    unfold PfeWeyl.IsNonsingular
    refine ⟨(a (Fin.castSucc i) : ℂ), ?_, ?_⟩
    · intro heq
      exact hnonzero (Fin.castSucc i) (Subtype.ext heq)
    · have hdist := hshort (Fin.castSucc i)
      have hsym : D ((b (Fin.castSucc i) : ℂ), (a (Fin.castSucc i) : ℂ)) =
          D ((a (Fin.castSucc i) : ℂ), (b (Fin.castSucc i) : ℂ)) :=
        D.isExtMetric.2.2.1 _ _
      rw [hsym]
      exact hdist.trans hrfin

end SupercriticalLQGUniqueness.B2.PfeAxioms
