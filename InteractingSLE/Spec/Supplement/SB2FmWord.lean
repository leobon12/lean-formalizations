/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LwInv
import InteractingSLE.Spec.Supplement.SB2FlTail

/-!
# D34's second clause, part (b): left admissibility through the step word (deterministic)

Worker PROVE-SB2-F3LAW (round 2, target 3). The induction's word at stage `ℓ + 2` is `Qw.stepWord κ (−π/2) x₀ β e`
(`Fl.mvLaw_succ_succ`): the stop word of B's piece `ℓ` (angle `−π/2`) from the offset-`x₀` word `β`, recentred by
`x₀ + W_T`. Left of the piece's tip the stop word's heights are the piece's new left side `−λ + (π/2)χ` or heights of
`β` left of the seed (`Lh.stopWord_fn_neg_mem`); both are admissible for the lower flow (`height − (π/2)χ < λ`, i.e.
left weight `> −2`) when `β`'s are:

* `LeftAdm`, `leftAdm_stopWord`, **`leftAdm_stepWord`**, `cumWeightLeft_gt_of_lt`.

The equivalence with the clause's form `−2 < cumWeightLeft κ (height − (π/2)χ)` is `cumWeightLeft_gt_of_lt`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.Fm

open Exist Exist.StagedLaw Exist.Staged Restart

/-- **Admissible heights left of a point** for the lower flow (angle `−π/2`): every height of `β` left of `a` off its
jumps satisfies `height − (π/2)χ < λ`. -/
def LeftAdm (κ : ℝ) (β : BoundaryWord) (a : ℝ) : Prop :=
  ∀ y, y < a → y ∉ β.jumps → β.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ

/-- **The stop word of a piece of angle `−π/2` keeps the left admissibility** (left of its tip `0`). -/
theorem leftAdm_stopWord {κ : ℝ} (hκ : 0 < κ) {β : BoundaryWord} (hL : LeftAdm κ β 0) (r : RecData) :
    LeftAdm κ (stopWord κ (β, -(Real.pi / 2), r)) 0 := by
  intro y hy _
  rcases Lh.stopWord_fn_neg_mem hκ β (-(Real.pi / 2)) r hy with h | ⟨x, hx, hxJ, h⟩
  · rw [h]
    have hl := Sec4.sleLambda_pos hκ
    linarith
  · rw [h]
    exact hL x hx hxJ

/-- **Left admissibility is moved by a shift.** -/
theorem leftAdm_shiftW {κ : ℝ} {β : BoundaryWord} {a : ℝ} (hL : LeftAdm κ β a) (s : ℝ) :
    LeftAdm κ (BoundaryWord.shiftW s β) (a - s) := by
  intro y hy hyJ
  rw [BoundaryWord.fn_shiftW]
  refine hL _ (by linarith) fun hmem => hyJ ?_
  rw [BoundaryWord.jumps_shiftW]
  exact Finset.mem_image.2 ⟨y + s, hmem, by ring⟩

/-- **The step word keeps the left admissibility left of the new tip `x₀ + W_T`.** -/
theorem leftAdm_stepWord {κ : ℝ} (hκ : 0 < κ) {Ω : Type*} (x₀ : Ω → ℝ) {β : Ω → BoundaryWord}
    (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {ω : Ω} (hL : LeftAdm κ (β ω) 0) :
    LeftAdm κ (Qw.stepWord κ (-(Real.pi / 2)) x₀ β e ω) (x₀ ω + Qw.endV (recOf ⊤ (e ω))) := by
  have h := leftAdm_shiftW (leftAdm_stopWord hκ hL (recOf ⊤ (e ω))) (-(x₀ ω + Qw.endV (recOf ⊤ (e ω))))
  rw [zero_sub, neg_neg] at h
  exact h

/-- The clause's form: a height `v` with `v − (π/2)χ < λ` has left cumulative weight `> −2` for the lower flow. -/
theorem cumWeightLeft_gt_of_lt {κ : ℝ} (hκ : 0 < κ) {v : ℝ} (hv : v + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    -2 < Sec4.cumWeightLeft κ (v + -(Real.pi / 2) * chiC κ) := by
  have hl := Sec4.sleLambda_pos hκ
  unfold Sec4.cumWeightLeft
  have := (div_lt_one hl).2 hv
  rw [neg_div]
  linarith

end InteractingSLE.Theorem14.SB.Fm
