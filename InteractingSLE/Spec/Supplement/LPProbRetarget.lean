/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Sec7.ContinuityTargetChange

/-!
# Retargeting a right mark: the transformed word of Lemma LP9

Packet PROVE-R17. Supplement §6.5, Lemma LP9 (`source/spec/p481-528.md` L117–L132, pp. 485–486):
for a configuration with right positions `x_1 < ⋯ < x_n` (source indexing; `x_1 = 0⁺` allowed) and an
index `j ≥ 2`, target the actual mark `x_j` by `ψ(z) = z/(x_j − z)`. "The target mark is removed from
the finite list and the old target becomes the finite mark `−1`, of weight `k − 6` minus the original
total weight. […] The right transformed marks are exactly the original right marks preceding `x_j`.
The left list consists, in order away from the seed, of all original left marks, the old target `−1`,
and the original right marks after `x_j` in reversed order. Adding their weights proves (LP9.1)."

Lean indexing: the right list has length `j + 1 + m` and the target has Lean index `j` (source index
`j + 1`), so the source condition `j ≥ 2` reads `1 ≤ j`. The real Möbius map `ψ` is
`Sec7.targetChangeReal` (PROVE-SEC7-C, reused with its monotonicity lemmas).

* `retargetXL`, `retargetXR`, `retargetρL`, `retargetρR`: the transformed word;
* `isDistinctForceWord_retarget`: it is an ordered word with distinct positions on each side,
  `ψ(x^L_1) > ⋯ > ψ(x^L_ℓ) > −1 > ψ(x_n) > ⋯ > ψ(x_{j+1})` and `0 ≤ ψ(x_1) < ⋯ < ψ(x_{j−1})`;
* its count `(nL + (m + 1)) + j = nL + (j + 1 + m)` (exactly `N` marks: the old target is retained);
* `sum_retargetρR` (right total `S_{j−1}`) and `sum_retargetρL` (**(LP9.1)**: left total
  `k − 6 − S_j`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.LP

/-- An appended tuple is strictly decreasing if both pieces are and every entry of the second
piece is below every entry of the first. -/
theorem strictAnti_fin_append {a b : ℕ} {f : Fin a → ℝ} {g : Fin b → ℝ} (hf : StrictAnti f)
    (hg : StrictAnti g) (hfg : ∀ i k, g k < f i) : StrictAnti (Fin.append f g) := by
  intro i i' h
  induction i using Fin.addCases with
  | left i =>
    induction i' using Fin.addCases with
    | left i' =>
      simp only [Fin.append_left]
      refine hf ?_
      rw [Fin.lt_def] at h ⊢; simpa only [Fin.val_castAdd] using h
    | right k => simp only [Fin.append_left, Fin.append_right]; exact hfg i k
  | right k =>
    induction i' using Fin.addCases with
    | left i' =>
      exfalso; rw [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at h; omega
    | right k' =>
      simp only [Fin.append_right]
      refine hg ?_
      rw [Fin.lt_def] at h ⊢; rw [Fin.val_natAdd, Fin.val_natAdd] at h; omega

/-- `Fin.cons a g` is strictly decreasing if `g` is and every entry of `g` is below `a`. -/
theorem strictAnti_fin_cons {b : ℕ} {a : ℝ} {g : Fin b → ℝ} (hg : StrictAnti g)
    (h : ∀ k, g k < a) : StrictAnti (Fin.cons a g : Fin (b + 1) → ℝ) := by
  intro i i' hii
  induction i using Fin.cases with
  | zero =>
    induction i' using Fin.cases with
    | zero => exact absurd hii (lt_irrefl _)
    | succ k => simp only [Fin.cons_zero, Fin.cons_succ]; exact h k
  | succ k =>
    induction i' using Fin.cases with
    | zero => exact absurd hii (Fin.not_lt_zero _)
    | succ k' =>
      simp only [Fin.cons_succ]
      exact hg (Fin.succ_lt_succ_iff.1 hii)

section Retarget

variable {nL j m : ℕ}

/-- The Lean index `j` of the retargeted right mark in a right list of length `j + 1 + m`
(source index `j + 1`). -/
def retargetIdx (j m : ℕ) : Fin (j + 1 + m) := Fin.castAdd m (Fin.last j)

/-- The retargeted mark's position `x_j`. -/
def retargetPos (xR : Fin (j + 1 + m) → ℝ) : ℝ := xR (retargetIdx j m)

/-- **LP9's transformed left list**: the original left marks `ψ(x^L_i)`, the old target `−1`, and
the original right marks after the target in reversed order, `ψ(x_n), …, ψ(x_{j+1})`. -/
def retargetXL (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) : Fin (nL + (m + 1)) → ℝ :=
  Fin.append (fun i => Sec7.targetChangeReal (retargetPos xR) (xL i))
    (Fin.cons (-1) fun l : Fin m =>
      Sec7.targetChangeReal (retargetPos xR) (xR (Fin.natAdd (j + 1) l.rev)))

/-- **LP9's transformed right list**: the original right marks before the target, `ψ(x_1), …,
ψ(x_{j−1})`. -/
def retargetXR (xR : Fin (j + 1 + m) → ℝ) : Fin j → ℝ :=
  fun i => Sec7.targetChangeReal (retargetPos xR) (xR (Fin.castAdd m i.castSucc))

/-- LP9's transformed left weights: the original left weights, `k − 6` minus the original total
weight at the old target, and the weights of the later right marks in reversed order. -/
def retargetρL (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ) : Fin (nL + (m + 1)) → ℝ :=
  Fin.append ρL (Fin.cons (κ - 6 - ((∑ i, ρL i) + ∑ i, ρR i)) fun l : Fin m =>
    ρR (Fin.natAdd (j + 1) l.rev))

/-- LP9's transformed right weights: the weights of the original right marks before the target. -/
def retargetρR (ρR : Fin (j + 1 + m) → ℝ) : Fin j → ℝ := fun i => ρR (Fin.castAdd m i.castSucc)

/-- The right total of the transformed word is `S_{j−1}` (source indexing), the sum of the weights
before the target. -/
theorem sum_retargetρR (ρR : Fin (j + 1 + m) → ℝ) :
    ∑ i, retargetρR ρR i = ∑ i : Fin j, ρR (Fin.castAdd m i.castSucc) := rfl

/-- Splitting the right weights at the target. -/
theorem sum_right_split (ρR : Fin (j + 1 + m) → ℝ) :
    ∑ i, ρR i = (∑ i : Fin j, ρR (Fin.castAdd m i.castSucc)) + ρR (retargetIdx j m) +
      ∑ l : Fin m, ρR (Fin.natAdd (j + 1) l) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  rfl

/-- Reversal does not change a sum over `Fin m`. -/
theorem sum_rev_eq {m : ℕ} (f : Fin m → ℝ) : ∑ l : Fin m, f l.rev = ∑ l, f l :=
  Fintype.sum_equiv Fin.revPerm _ _ (fun _ => rfl)

/-- **(LP9.1)**: the left total of the transformed word is `k − 6 − S_j`. -/
theorem sum_retargetρL (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ) :
    ∑ i, retargetρL κ ρL ρR i =
      κ - 6 - ((∑ i : Fin j, ρR (Fin.castAdd m i.castSucc)) + ρR (retargetIdx j m)) := by
  rw [retargetρL, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.sum_cons]
  rw [sum_rev_eq (fun l => ρR (Fin.natAdd (j + 1) l)), sum_right_split]
  ring


/-- The target position is positive when `j ≥ 2` (source indexing). -/
theorem retargetPos_pos {xR : Fin (j + 1 + m) → ℝ} (hmono : StrictMono xR) (h0 : ∀ i, 0 ≤ xR i)
    (hj : 1 ≤ j) : 0 < retargetPos xR :=
  lt_of_le_of_lt (h0 ⟨0, by omega⟩) (hmono (by rw [Fin.lt_def]; simp [retargetIdx]; omega))

/-- The marks before the target are to its left. -/
theorem xR_castAdd_castSucc_lt {xR : Fin (j + 1 + m) → ℝ} (hmono : StrictMono xR) (i : Fin j) :
    xR (Fin.castAdd m i.castSucc) < retargetPos xR :=
  hmono (by rw [Fin.lt_def]; simp [retargetIdx])

/-- The marks after the target are to its right. -/
theorem retargetPos_lt_xR_natAdd {xR : Fin (j + 1 + m) → ℝ} (hmono : StrictMono xR) (l : Fin m) :
    retargetPos xR < xR (Fin.natAdd (j + 1) l) :=
  hmono (by rw [Fin.lt_def]; simp [retargetIdx]; omega)

/-- **The transformed word of LP9 has distinct positions on each side** (and is ordered): the
left list is `ψ(x^L_1) > ⋯ > ψ(x^L_ℓ) > −1 > ψ(x_n) > ⋯ > ψ(x_{j+1})`, the right list is
`0 ≤ ψ(x_1) < ⋯ < ψ(x_{j−1})`. -/
theorem isDistinctForceWord_retarget {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
    (hD : IsDistinctForceWord xL xR) (hj : 1 ≤ j) :
    IsDistinctForceWord (retargetXL xL xR) (retargetXR xR) := by
  obtain ⟨⟨-, hL0, -, hR0⟩, hanti, hmono⟩ := hD
  have hp := retargetPos_pos hmono hR0 hj
  have hψL : ∀ i, -1 < Sec7.targetChangeReal (retargetPos xR) (xL i) := fun i =>
    Sec7.neg_one_lt_targetChangeReal hp (lt_of_le_of_lt (hL0 i) hp)
  have hlater : ∀ l : Fin m, Sec7.targetChangeReal (retargetPos xR)
      (xR (Fin.natAdd (j + 1) l.rev)) < -1 := fun l =>
    Sec7.targetChangeReal_lt_neg_one hp (retargetPos_lt_xR_natAdd hmono _)
  have hgle : ∀ k, (Fin.cons (-1) fun l : Fin m => Sec7.targetChangeReal (retargetPos xR)
      (xR (Fin.natAdd (j + 1) l.rev)) : Fin (m + 1) → ℝ) k ≤ -1 := by
    intro k
    induction k using Fin.cases with
    | zero => simp
    | succ l => simp only [Fin.cons_succ]; exact (hlater l).le
  have hXL : StrictAnti (retargetXL xL xR) := by
    refine strictAnti_fin_append ?_ (strictAnti_fin_cons ?_ hlater) ?_
    · intro i i' h
      exact Sec7.strictMonoOn_targetChangeReal_Iio hp (lt_of_le_of_lt (hL0 i') hp)
        (lt_of_le_of_lt (hL0 i) hp) (hanti h)
    · intro l l' h
      refine Sec7.strictMonoOn_targetChangeReal_Ioi hp (retargetPos_lt_xR_natAdd hmono _)
        (retargetPos_lt_xR_natAdd hmono _) (hmono ?_)
      rw [Fin.lt_def, Fin.val_natAdd, Fin.val_natAdd, Fin.val_rev, Fin.val_rev]
      have := Fin.lt_def.1 h; omega
    · intro i k; exact lt_of_le_of_lt (hgle k) (hψL i)
  have hXR : StrictMono (retargetXR xR) := by
    intro i i' h
    refine Sec7.strictMonoOn_targetChangeReal_Iio hp (xR_castAdd_castSucc_lt hmono i)
      (xR_castAdd_castSucc_lt hmono i') (hmono ?_)
    rw [Fin.lt_def]; simpa using Fin.lt_def.1 h
  refine ⟨⟨hXL.antitone, ?_, hXR.monotone, ?_⟩, hXL, hXR⟩
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simp only [retargetXL, Fin.append_left]
      exact div_nonpos_of_nonpos_of_nonneg (hL0 i) (sub_nonneg.2 (le_trans (hL0 i) hp.le))
    | right k =>
      simp only [retargetXL, Fin.append_right]
      linarith [hgle k]
  · intro i
    exact Sec7.targetChangeReal_nonneg (hR0 _) (xR_castAdd_castSucc_lt hmono i)

/-- The transformed word has exactly as many marks as the original one. -/
theorem retarget_card (nL j m : ℕ) : nL + (m + 1) + j = nL + (j + 1 + m) := by omega

end Retarget

end InteractingSLE.LP
