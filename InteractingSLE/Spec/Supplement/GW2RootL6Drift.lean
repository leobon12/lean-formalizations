/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Drift
import InteractingSLE.Spec.Sec5.Prop59StageDrift

/-!
# The remaining drift of finite varying-angle words

Continuation of PROVE-T14-GW2ROOT2. The new marks carry the actual
telescoping differences of arbitrary angles, followed by a fixed finite
initial word. This is distinct from `stageρL/stageρR`, which use alternating
extreme angles. Abel summation and the finite inherited-mark estimate are
reused from `Sec5.Drift`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootL6

open Sec5

/-- Left angle-change marks in outward order, followed by inherited marks. -/
def angleWordL (κ : ℝ) (φ : ℕ → ℝ) (m : ℕ) {n : ℕ} (ρ₀ : Fin n → ℝ) :
    Fin (m + n) → ℝ :=
  Fin.append (fun i : Fin m => -angleChangeWeight κ φ i) ρ₀

/-- The new first right seed, the remaining angle-change marks in outward
order, and the inherited right marks. -/
def angleWordR (κ : ℝ) (φ : ℕ → ℝ) (m : ℕ) {n : ℕ} (ρ₀ : Fin n → ℝ) :
    Fin (m + n + 1) → ℝ :=
  Fin.cons (angleChangeWeight κ φ 0)
    (Fin.append (fun i : Fin m => angleChangeWeight κ φ (i + 1)) ρ₀)

/-- A finite block of consecutive angle changes has a depth-independent
drift bound for ordered gaps. This only adapts the existing Abel estimate
from natural-number indexing to `Fin`. -/
theorem abs_angleBlock_div_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {φ : ℕ → ℝ} (hφ : ∀ i, φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (k : ℕ) {n : ℕ} {g : Fin n → ℝ}
    (hg : ∀ i, 3 / 4 ≤ g i) (hmono : Monotone g) :
    |∑ i : Fin n, angleChangeWeight κ (fun j => φ (k + j)) i / g i| ≤
      4 * angleWeightBound κ / 3 := by
  let gN : ℕ → ℝ := fun i => if hi : i < n then g ⟨i, hi⟩ else 0
  have hgN : ∀ i < n, 3 / 4 ≤ gN i := by
    intro i hi
    simpa only [gN, hi, ↓reduceDIte] using hg ⟨i, hi⟩
  have hmonoN : ∀ i j, i ≤ j → j < n → gN i ≤ gN j := by
    intro i j hij hj
    have hi : i < n := hij.trans_lt hj
    simp only [gN, hi, hj, ↓reduceDIte]
    exact hmono hij
  have h := abs_sum_div_le_of_gap_mono (by norm_num : (0 : ℝ) < 3 / 4)
    hgN hmonoN (fun l _ => abs_sum_angleChangeWeight_le hκ hκ4 hφ k l)
  have heq :
      (∑ i : Fin n, angleChangeWeight κ (fun j => φ (k + j)) i / g i) =
        ∑ i ∈ range n, angleChangeWeight κ (fun j => φ (k + j)) i / gN i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun i _ => by simp only [gN, i.isLt, ↓reduceDIte]
  rw [heq]
  exact h.trans_eq (by ring)

/-- Exact decomposition into the two new-angle blocks and the two inherited
blocks, omitting precisely the new first right seed from `otherDrift`. -/
theorem otherDrift_angleWord_eq (κ : ℝ) (φ : ℕ → ℝ) {nL₀ nR₀ : ℕ}
    (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) (mL mR : ℕ) (w : ℝ)
    (vL : Fin (mL + nL₀) → ℝ) (vR : Fin (mR + nR₀ + 1) → ℝ) :
    otherDrift (angleWordL κ φ mL ρL₀) (angleWordR κ φ mR ρR₀) w vL vR =
      ((∑ i : Fin mL, -angleChangeWeight κ φ i /
          (w - vL (Fin.castAdd nL₀ i))) +
        (∑ i : Fin mR, angleChangeWeight κ φ (i + 1) /
          (w - vR (Fin.castAdd nR₀ i).succ))) +
      ((∑ i : Fin nL₀, ρL₀ i / (w - vL (Fin.natAdd mL i))) +
        (∑ i : Fin nR₀, ρR₀ i / (w - vR (Fin.natAdd mR i).succ))) := by
  simp only [otherDrift, angleWordL, angleWordR, Fin.cons_succ]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  ring

/-- The actual varying-angle word has the same uniform remaining-drift
bound as the extreme alternating word. The constant depends only on `κ`
and the fixed inherited weights, not on the number or values of the angles. -/
theorem otherDrift_angleWord_le {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {φ : ℕ → ℝ} (hφ : ∀ i, φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {nL₀ nR₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ)
    (mL mR : ℕ) {w : ℝ} {vL : Fin (mL + nL₀) → ℝ}
    {vR : Fin (mR + nR₀ + 1) → ℝ} (hvL : Antitone vL) (hvR : Monotone vR)
    (hgL : ∀ i, 3 / 4 ≤ w - vL i)
    (hgR : ∀ i : Fin (mR + nR₀), 3 / 4 ≤ vR i.succ - w) :
    |otherDrift (angleWordL κ φ mL ρL₀) (angleWordR κ φ mR ρR₀) w vL vR| ≤
      Prop59Stage.stageDriftBound κ ρL₀ ρR₀ := by
  have hL := abs_angleBlock_div_le hκ hκ4 hφ 0
    (g := fun i : Fin mL => w - vL (Fin.castAdd nL₀ i))
    (fun i => hgL _) (fun i j hij => sub_le_sub_left
      (hvL (show Fin.castAdd nL₀ i ≤ Fin.castAdd nL₀ j from hij)) w)
  simp only [Nat.zero_add] at hL
  have hL' : |∑ i : Fin mL, -angleChangeWeight κ φ i /
      (w - vL (Fin.castAdd nL₀ i))| ≤ 4 * angleWeightBound κ / 3 := by
    simpa only [neg_div, sum_neg_distrib, abs_neg] using hL
  have hR := abs_angleBlock_div_le hκ hκ4 hφ 1
    (g := fun i : Fin mR => vR (Fin.castAdd nR₀ i).succ - w)
    (fun i => hgR _) (fun i j hij => sub_le_sub_right
      (hvR (Fin.succ_le_succ_iff.2
        (show Fin.castAdd nR₀ i ≤ Fin.castAdd nR₀ j from hij))) w)
  have he : ∀ i, angleChangeWeight κ (fun j => φ (1 + j)) i =
      angleChangeWeight κ φ (i + 1) := by
    intro i
    simp only [angleChangeWeight]
    ring_nf
  simp only [he] at hR
  have hR' : |∑ i : Fin mR, angleChangeWeight κ φ (i + 1) /
      (w - vR (Fin.castAdd nR₀ i).succ)| ≤ 4 * angleWeightBound κ / 3 := by
    have heq :
        (∑ i : Fin mR, angleChangeWeight κ φ (i + 1) /
          (w - vR (Fin.castAdd nR₀ i).succ)) =
        -(∑ i : Fin mR, angleChangeWeight κ φ (i + 1) /
          (vR (Fin.castAdd nR₀ i).succ - w)) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun i _ => by rw [← div_neg, neg_sub]
    rw [heq, abs_neg]
    exact hR
  have hIL := abs_sum_div_le_of_gap (univ : Finset (Fin nL₀))
    (ρ := ρL₀) (V := fun i => vL (Fin.natAdd mL i)) (W := w)
    (by norm_num : (0 : ℝ) < 3 / 4) (fun i _ => by
      rw [abs_of_nonneg (by linarith only [hgL (Fin.natAdd mL i)])]
      exact hgL _)
  have hIR := abs_sum_div_le_of_gap (univ : Finset (Fin nR₀))
    (ρ := ρR₀) (V := fun i => vR (Fin.natAdd mR i).succ) (W := w)
    (by norm_num : (0 : ℝ) < 3 / 4) (fun i _ => by
      rw [abs_sub_comm, abs_of_nonneg
        (by linarith only [hgR (Fin.natAdd mR i)])]
      exact hgR _)
  rw [otherDrift_angleWord_eq]
  refine (abs_add_le _ _).trans ((add_le_add
    (Supp8.gb9_two_sides_le hL' hR')
    ((abs_add_le _ _).trans (add_le_add hIL hIR))).trans_eq ?_)
  rw [Prop59Stage.stageDriftBound]
  ring

end InteractingSLE.Theorem14.GW2TipSystem.RootL6
