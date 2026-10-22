import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Caps.FullScales
import HigherDimLQGMetric.Sec8.Colors
import HigherDimLQGMetric.Sec8b.BinIndex

/-!
# Scale, colour, and unit-bin classification of supplied sites

This is the finite pigeonhole part of Step 2. It reuses the Section 8
palette and dyadic bin API from the sealed metric library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- The finite catalogue class set for the supplied sites. -/
def q11ClassSet (d : ℕ) (V Δ K0 : ℝ) : Finset (ℕ × (Fin d → ℤ) × ℤ) :=
  (p4_fullScales V).product
    ((sec8Colors d).product (s7b_binIndices (Δ ^ K0) (Δ ^ (-K0))))

/-- Many sites among finitely many scale, colour and unit classes force a
large single class. The conclusion includes the actual unit-bin bounds. -/
theorem q11_class_pigeonhole {d m n : ℕ} (hd : 1 ≤ d)
    {V Δ K0 : ℝ} (hΔ : 0 < Δ)
    (hm : 0 < m)
    (k : Fin m → ℕ) (j : Fin m → Fin d → ℤ) (S : Fin m → ℝ)
    (hk : ∀ i, k i ∈ p4_fullScales V)
    (hS : ∀ i, Δ ^ K0 ≤ S i ∧ S i ≤ Δ ^ (-K0))
    (hcount : (q11ClassSet d V Δ K0).card * n ≤ m) :
    ∃ c ∈ q11ClassSet d V Δ K0, ∃ I : Finset (Fin m),
      n ≤ I.card ∧ ∀ i ∈ I,
        k i = c.1 ∧ sec8Color d (j i) = c.2.1 ∧
          (2 : ℝ) ^ c.2.2 ≤ S i ∧ S i ≤ 2 * (2 : ℝ) ^ c.2.2 := by
  classical
  have hlo : 0 < Δ ^ K0 := Real.rpow_pos_of_pos hΔ _
  have hhi : 0 < Δ ^ (-K0) := Real.rpow_pos_of_pos hΔ _
  let bin : Fin m → ℤ := fun i =>
    Classical.choose (s7b_exists_bin hlo hhi (hS i))
  have hbin (i : Fin m) :
      bin i ∈ s7b_binIndices (Δ ^ K0) (Δ ^ (-K0)) ∧
      0 < (2 : ℝ) ^ bin i ∧ (2 : ℝ) ^ bin i ≤ S i ∧
        S i ≤ 2 * (2 : ℝ) ^ bin i := by
    exact Classical.choose_spec (s7b_exists_bin hlo hhi (hS i))
  let f : Fin m → ℕ × (Fin d → ℤ) × ℤ :=
    fun i => (k i, sec8Color d (j i), bin i)
  have hf (i : Fin m) : f i ∈ q11ClassSet d V Δ K0 := by
    change (k i, (sec8Color d (j i), bin i)) ∈
      (p4_fullScales V).product
        ((sec8Colors d).product (s7b_binIndices (Δ ^ K0) (Δ ^ (-K0))))
    exact Finset.mk_mem_product (hk i)
      (Finset.mk_mem_product (sec8Color_mem_colors hd (j i)) (hbin i).1)
  have hnonempty : (q11ClassSet d V Δ K0).Nonempty :=
    ⟨f ⟨0, hm⟩, hf ⟨0, hm⟩⟩
  obtain ⟨c, hc, hfiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := Finset.univ) (t := q11ClassSet d V Δ K0)
      (f := f) (n := n) (fun i _ => hf i) hnonempty (by
        simpa only [Finset.card_univ, Fintype.card_fin] using hcount)
  let I : Finset (Fin m) := Finset.univ.filter (fun i => f i = c)
  refine ⟨c, hc, I, hfiber, ?_⟩
  intro i hi
  have hfi : f i = c := (Finset.mem_filter.mp hi).2
  have hcomponents : k i = c.1 ∧ sec8Color d (j i) = c.2.1 ∧ bin i = c.2.2 := by
    change (k i, (sec8Color d (j i), bin i)) = c at hfi
    exact ⟨congrArg Prod.fst hfi,
      congrArg (fun p : ℕ × (Fin d → ℤ) × ℤ => p.2.1) hfi,
      congrArg (fun p : ℕ × (Fin d → ℤ) × ℤ => p.2.2) hfi⟩
  refine ⟨hcomponents.1, hcomponents.2.1, ?_, ?_⟩
  · rw [← hcomponents.2.2]
    exact (hbin i).2.2.1
  · rw [← hcomponents.2.2]
    exact (hbin i).2.2.2

end HigherDimLQGContinuity
