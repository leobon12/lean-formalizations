/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Supplement.GW2JointKernelProofC

/-!
# The stage word's totals from its far heights (GB9, p. 525; follow-up note A.3)

Packet PROVE-T14-TIP11. GB9 (`source/spec/p481-528.md` L1062–L1066, p. 525): "With the angle absorbed into that field,
the far heights for a current angle `θ` are `−λ′ + (θ + π)χ`, `λ′ + (θ − π)χ` … At `θ = π/2` the total weights are
`(κ − 4, c_κ)`; at `θ = −π/2` they are reflected." The totals of the angle-`θ` flow-line word of a boundary datum depend
only on its outermost heights: the side weights telescope (the left partial sum through a mark is the cumulative weight
`−b(y)/λ − 1` just beyond it, `Sec5.Aux22ChartE.exists_sum_flowLineRhoL_eq`, and the angle enters only the seed weight,
`GW1Conn.flowLineRhoL_theta`). This file proves

* **`sum_flowLineRhoL_eq_of_far`**, **`sum_flowLineRhoR_eq_of_far`**: if the datum equals `h_L` beyond the
  outermost left mark (resp. `h_R` beyond the outermost right mark), the left (right) total of the angle-`θ` word
  is the cumulative weight `−(h_L + θχ)/λ − 1` (resp. `(h_R + θχ)/λ − 1`);
* **`totals_far_half_pi`**, **`totals_far_neg_half_pi`**: with the specification's far heights `−λ′ + πχ`, `λ′ − πχ`
  (TIP10's corrected joint chart, `GW2JointKernel.totals_specHeights`), the totals are `(κ − 4, κ/2 − 2)` at `π/2` and
  `(κ/2 − 2, κ − 4)` at `−π/2` — the totals of the leftward and rightward stages of `GW2TipStageCross`.
-/

set_option autoImplicit false

noncomputable section

open Finset
open QuantumZipper (chiC)

namespace InteractingSLE

namespace Theorem14

namespace GW2TipStage

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}

/-- The outermost left mark of the flow-line word from `0`. -/
def lastL (b : ℝ → ℝ) (J : Finset ℝ) : Fin (flowLineNL b J 0) :=
  ⟨flowLineNL b J 0 - 1, Nat.sub_lt (by unfold flowLineNL; omega) one_pos⟩

/-- The outermost right mark of the flow-line word from `0`. -/
def lastR (b : ℝ → ℝ) (J : Finset ℝ) : Fin (flowLineNR b J 0) :=
  ⟨flowLineNR b J 0 - 1, Nat.sub_lt (by unfold flowLineNR; omega) one_pos⟩

theorem filter_le_lastL : univ.filter (fun l => l ≤ lastL b J) = univ := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact Fin.le_def.2 (by simp only [lastL]; have := l.isLt; omega)

theorem filter_le_lastR : univ.filter (fun l => l ≤ lastR b J) = univ := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact Fin.le_def.2 (by simp only [lastR]; have := l.isLt; omega)

/-- **The left total from the far-left height**: if the datum equals `h_L` left of the outermost left mark (off the
jumps), the left total of the angle-`θ` flow-line word from `0` is `−(h_L + θχ)/λ − 1`. -/
theorem sum_flowLineRhoL_eq_of_far (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ) {hL : ℝ}
    (hfar : ∀ y, y < flowLineXL b J 0 (lastL b J) → y ∉ J → b y = hL) :
    ∑ i, flowLineRhoL κ b J 0 θ i = Sec4.cumWeightLeft κ (hL + θ * chiC κ) := by
  have hsum : ∑ l ∈ univ.filter (fun l => l ≤ lastL b J), flowLineRhoL κ b J 0 θ l =
      ∑ l ∈ univ.filter (fun l => l ≤ lastL b J), flowLineRhoL κ b J 0 0 l - θ * chiC κ / sleLambda κ := by
    rw [Finset.sum_congr rfl (fun l _ => GW1Conn.flowLineRhoL_theta κ b J θ l), Finset.sum_add_distrib,
      GW1Conn.sum_filter_le_ite_val_eq_zero _ (lastL b J) ⟨0, by unfold flowLineNL; omega⟩ rfl]
    ring
  rw [← filter_le_lastL (b := b) (J := J), hsum, GW3Word.filter_le_eq_filter_le_flowLineXL]
  obtain ⟨y, -, hy, hyJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoL_eq hκ hb
    (lo := flowLineXL b J 0 (lastL b J) - 1) (by linarith) (GW3Word.flowLineXL_nonpos b J (lastL b J))
  rw [hS, hfar y hy hyJ]
  unfold Sec4.cumWeightLeft
  ring

/-- **The right total from the far-right height**: if the datum equals `h_R` right of the outermost right mark (off the
jumps), the right total of the angle-`θ` flow-line word from `0` is `(h_R + θχ)/λ − 1`. -/
theorem sum_flowLineRhoR_eq_of_far (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J) (θ : ℝ) {hR : ℝ}
    (hfar : ∀ y, flowLineXR b J 0 (lastR b J) < y → y ∉ J → b y = hR) :
    ∑ j, flowLineRhoR κ b J 0 θ j = Sec4.cumWeightRight κ (hR + θ * chiC κ) := by
  have hsum : ∑ l ∈ univ.filter (fun l => l ≤ lastR b J), flowLineRhoR κ b J 0 θ l =
      ∑ l ∈ univ.filter (fun l => l ≤ lastR b J), flowLineRhoR κ b J 0 0 l + θ * chiC κ / sleLambda κ := by
    rw [Finset.sum_congr rfl (fun l _ => GW1Conn.flowLineRhoR_theta κ b J θ l), Finset.sum_add_distrib,
      GW1Conn.sum_filter_le_ite_val_eq_zero _ (lastR b J) ⟨0, by unfold flowLineNR; omega⟩ rfl]
  rw [← filter_le_lastR (b := b) (J := J), hsum, GW3Word.filter_le_eq_filter_flowLineXR_le]
  obtain ⟨y, hy, hyJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoR_eq hκ hb
    (GW3Word.flowLineXR_nonneg b J (lastR b J))
  rw [hS, hfar y hy hyJ]
  unfold Sec4.cumWeightRight
  ring

/-- **GB9's totals at `θ = π/2`** from the specification's far heights `−λ′ + πχ` (left) and `λ′ − πχ` (right): the
leftward stage's totals `(κ − 4, κ/2 − 2)`. -/
theorem totals_far_half_pi (hκ : 0 < κ) :
    Sec4.cumWeightLeft κ ((-sleLambda (16 / κ) + Real.pi * chiC κ) + Real.pi / 2 * chiC κ) = κ - 4 ∧
      Sec4.cumWeightRight κ ((sleLambda (16 / κ) - Real.pi * chiC κ) + Real.pi / 2 * chiC κ) = κ / 2 - 2 := by
  have h := GW2JointKernel.totals_specHeights hκ
  unfold Sec4.cumWeightLeft Sec4.cumWeightRight
  exact h

/-- **GB9's totals at `θ = −π/2`** ("at `θ = −π/2` they are reflected"): the rightward stage's totals
`(κ/2 − 2, κ − 4)`. -/
theorem totals_far_neg_half_pi (hκ : 0 < κ) :
    Sec4.cumWeightLeft κ ((-sleLambda (16 / κ) + Real.pi * chiC κ) + -(Real.pi / 2) * chiC κ) = κ / 2 - 2 ∧
      Sec4.cumWeightRight κ ((sleLambda (16 / κ) - Real.pi * chiC κ) + -(Real.pi / 2) * chiC κ) = κ - 4 := by
  unfold Sec4.cumWeightLeft Sec4.cumWeightRight sleLambda QuantumZipper.chiC
  rw [GW2JointKernel.sqrt_sixteen_div hκ]
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ κ = r ^ 2 := ⟨Real.sqrt κ, Real.sqrt_pos.2 hκ, (Real.sq_sqrt hκ.le).symm⟩
  rw [Real.sqrt_sq hr.le]
  have hπ : 0 < Real.pi := Real.pi_pos
  constructor
  · field_simp
    ring
  · field_simp
    ring

end GW2TipStage

end Theorem14

end InteractingSLE
