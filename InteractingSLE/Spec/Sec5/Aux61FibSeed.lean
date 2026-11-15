/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61FibAssembly

/-!
# The reference seed of a fibre is not a threshold state

Packet PROVE-AUX61-FIB, a deterministic input of `Aux61Fib.FibData` (its field `seed`). At the seed `0` of the
flow-line word of boundary data `b` (angle `0`), the only marks at the driver value `0` are the two seed marks `0⁻`,
`0⁺` (every other mark is a genuine jump `y ≠ 0`, placed at `y`), with weights `−b(0⁻)/λ − 1` and `b(0⁺)/λ − 1`.
Hence the continuation-threshold condition fails as soon as `b(0⁻) < λ` and `b(0⁺) > −λ` — in particular for the
reference words of Aux. lemmas 64–65 (`−λ` on the negative side next to the seed, `λ` or a height `≥ λ − πχ` on the
positive side).

* `sum_filter_cons_eq`: the sum over the vanishing marks is the seed weight;
* **`not_threshold_seed`**.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param` result.
-/

set_option autoImplicit false

noncomputable section

open Set Finset

namespace InteractingSLE.Sec5.Aux61Fib

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

variable {b : ℝ → ℝ} {J : Finset ℝ}

/-- A sum over the marks equal to `0` of a word whose first mark is `0` and whose other marks are nonzero is the
first weight. -/
theorem sum_filter_cons_eq {n : ℕ} (g : Fin n → ℝ) (hg : ∀ j, g j ≠ 0) (ρ0 : ℝ) (ρ : Fin n → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => (Fin.cons 0 g : Fin (n + 1) → ℝ) i = 0),
      (Fin.cons ρ0 ρ : Fin (n + 1) → ℝ) i = ρ0 := by
  rw [Finset.sum_filter, Fin.sum_univ_succ]
  simp [hg]

/-- **The reference seed is not a threshold state** when `b(0⁻) < λ` and `b(0⁺) > −λ`: at seed `0` the only marks
at the driver value `0` are the seed marks (every other mark is a genuine jump `y ≠ 0`), with weights
`−b(0⁻)/λ − 1 > −2` and `b(0⁺)/λ − 1 > −2`. -/
theorem not_threshold_seed {κ : ℝ} (hκ : 0 < κ) (hL : leftLim b 0 < sleLambda κ)
    (hR : -sleLambda κ < rightLim b 0) :
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0) 0
      (flowLineXL b J 0) (flowLineXR b J 0) := by
  have hlam := Sec4.sleLambda_pos hκ
  have hgL : ∀ j, ((jumpSet b J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev j) - 0 ≠ 0 := fun j => by
    rw [sub_zero]
    exact (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem ((jumpSet b J).filter (· < 0)) rfl (Fin.rev j))).2.ne
  have hgR : ∀ j, ((jumpSet b J).filter (0 < ·)).orderEmbOfFin rfl j - 0 ≠ 0 := fun j => by
    rw [sub_zero]
    exact (Finset.mem_filter.1 (Finset.orderEmbOfFin_mem ((jumpSet b J).filter (0 < ·)) rfl j)).2.ne'
  unfold ForceWord.ThresholdCondition flowLineRhoL flowLineRhoR flowLineXL flowLineXR flowLineNL flowLineNR
  rw [sum_filter_cons_eq _ hgL, sum_filter_cons_eq _ hgR]
  simp only [zero_mul, add_zero]
  rintro (h | h)
  · have : leftLim b 0 / sleLambda κ < 1 := (div_lt_one hlam).2 hL
    have e : -leftLim b 0 / sleLambda κ = -(leftLim b 0 / sleLambda κ) := neg_div _ _
    linarith
  · have : -1 < rightLim b 0 / sleLambda κ := by
      rw [lt_div_iff₀ hlam]
      linarith
    linarith

end InteractingSLE.Sec5.Aux61Fib
