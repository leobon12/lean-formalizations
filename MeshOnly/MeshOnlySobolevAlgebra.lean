import BouRabeeGwynne.DiscretePDEAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Finite weighted algebra for the mesh-only BV--Sobolev argument.

The geometric pyramid and Sobolev inputs are proved in subsequent modules;
these lemmas isolate only finite sums and real inequalities.
-/

open scoped BigOperators

namespace BouRabeeGwynne.MeshOnlySobolev

variable {V : Type*} [Fintype V]

lemma sum_transpose_weighted (p : V → V → ℝ) (u : V → ℝ) :
    (∑ v, ∑ w, p w v * u w ^ 2) = ∑ v, ∑ w, p v w * u v ^ 2 := by
  rw [Finset.sum_comm]

lemma sum_transpose_difference_sq (p : V → V → ℝ) (u : V → ℝ) :
    (∑ v, ∑ w, p w v * (u w - u v) ^ 2) =
      ∑ v, ∑ w, p v w * (u w - u v) ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- The two oriented pyramid contributions are controlled by three primal
volumes plus their symmetric jump cost. The row bound is only needed at
vertices where the function is nonzero. -/
theorem dual_mass_le_primal_and_jumps (p : V → V → ℝ) (m u : V → ℝ)
    (hp : ∀ v w, 0 ≤ p v w)
    (hrow : ∀ v, u v ≠ 0 → ∑ w, p v w ≤ m v) :
    (∑ v, ∑ w, (p v w + p w v) * u v ^ 2) ≤
      3 * (∑ v, m v * u v ^ 2) +
        ∑ v, ∑ w, (p v w + p w v) * (u w - u v) ^ 2 := by
  have hpoint (v w : V) : p w v * u v ^ 2 ≤
      2 * (p w v * u w ^ 2) + 2 * (p w v * (u w - u v) ^ 2) := by
    have hs : u v ^ 2 ≤ 2 * u w ^ 2 + 2 * (u w - u v) ^ 2 := by
      nlinarith [sq_nonneg (u v - 2 * u w)]
    nlinarith [mul_le_mul_of_nonneg_left hs (hp w v)]
  have hsum : (∑ v, ∑ w, p w v * u v ^ 2) ≤
      2 * (∑ v, ∑ w, p v w * u v ^ 2) +
      2 * (∑ v, ∑ w, p v w * (u w - u v) ^ 2) := by
    calc
      _ ≤ ∑ v, ∑ w,
          (2 * (p w v * u w ^ 2) + 2 * (p w v * (u w - u v) ^ 2)) :=
        Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hpoint v w
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [sum_transpose_weighted p u, sum_transpose_difference_sq p u]
  have hprimal : (∑ v, ∑ w, p v w * u v ^ 2) ≤ ∑ v, m v * u v ^ 2 := by
    apply Finset.sum_le_sum
    intro v _
    rw [← Finset.sum_mul]
    by_cases hu : u v = 0
    · simp [hu]
    · exact mul_le_mul_of_nonneg_right (hrow v hu) (sq_nonneg _)
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [sum_transpose_difference_sq p u]
  linarith

/-- Solving the defective support quadratic does not divide by the energy,
so the zero-energy case is included. -/
theorem support_bound_of_quadratic {X E K ε : ℝ}
    (hX : 0 ≤ X) (hE : 0 ≤ E) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hquad : X ^ 2 ≤ K ^ 2 * E * (X + ε ^ 2 * E)) :
    X ≤ (K ^ 2 + K * ε) * E := by
  by_contra h
  have hgt : (K ^ 2 + K * ε) * E < X := lt_of_not_ge h
  have hKE : 0 ≤ K * ε * E := mul_nonneg (mul_nonneg hK hε) hE
  have hbound : K * ε * E < X - K ^ 2 * E := by nlinarith
  have hprod : (K * ε * E) ^ 2 < X * (X - K ^ 2 * E) := by
    have hx : K * ε * E < X := by nlinarith [mul_nonneg (sq_nonneg K) hE]
    calc
      _ = (K * ε * E) * (K * ε * E) := pow_two _
      _ ≤ X * (K * ε * E) := mul_le_mul_of_nonneg_right hx.le hKE
      _ < _ := mul_lt_mul_of_pos_left hbound (hKE.trans_lt hx)
  nlinarith

end BouRabeeGwynne.MeshOnlySobolev
