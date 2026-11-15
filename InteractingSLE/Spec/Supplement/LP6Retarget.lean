/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPProbInduction

/-!
# Proposition LP6: the same-side two-mark reduction, as Lemma LP9 with two groups

Packet PROVE-LP14. Supplement §6.4, Proposition LP6 (`source/spec/p481-528.md` L77–L107, pp. 483–484):
"Fix `k > 0`. Assume that every canonical two-seed law with both weights greater than `−2` has a continuous trace on
every finite interval and is transient. Assume the integrated target-change identity, used only before the old and
new targets separate. Then every law with two same-side force groups has a continuous trace up to and including its
finite continuation threshold and is transient on infinite lifetime."

LP6's proof retargets the second mark by `ψ(z) = z/(x₂ − z)`. The transformed word has the old target `−1` (weight
`k − 6 − S`) on the left and `ψ(x₁) ≥ 0` (weight `r₁`) on the right, "exactly two groups, one on each side", and
"By Aux. lemma 106, whose hypotheses are precisely the two-seed theorem assumed here and the independent one-force
first-swallow input, this transformed evolution has a continuous trace through every finite continuation endpoint
and is transient". The rest of the proof (target change until separation, the pullback of the transformed prefix,
the merger of the two original groups and the one-seed continuation) is exactly Lemma LP9's argument for `N = 2`
groups and the target index `j = 2` ("The transformed word has at most `N` finite groups … If the complete theorem is
available for that transformed word and for all words with at most `N − 1` groups, then it holds for the original
word", p. 485).

This file proves that identification in Lean:

* `distinctCompleteBelow_two`: the smaller-count hypothesis of LP9 for `N = 2` (words with at most one group) is the
  zero-force base and the one-force theorem;
* `isDistinctForceWord_of_two`: the LP6 word `0 ≤ x₁ < x₂` is a distinct-position word;
* **`lp6Statement_of_lp9`**: the named input `LP6Statement κ` of LP10 (`LPProbInduction.lean`) from LP9, Aux. lemma 106
  and the zero- and one-force bases; LP9's transformed word for `j = 2`, `N = 2` is LP6's (1,1) word
  (`retargetXL`, `retargetXR`, LP9.1);
* **`lp10Statement_of_reductions_noLP6`**: Theorem LP10 from the remaining reductions, without `LP6Statement`.

Every input is one of LP10's own named inputs, so LP6 is no longer an open input of Theorem LP10. The integrated
target-change identity enters only through LP9 (its prefix part `Sec7.LP9PrefixStatement`, `ContinuityProb3Steps`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.LP

variable {κ : ℝ}

/-- **The smaller-count hypothesis for two groups**: every distinct-position word with at most one mark is complete,
by ordinary SLE (zero marks) and the one-force theorem (one mark, either side). -/
theorem distinctCompleteBelow_two (h0 : ZeroForceStatement.{u} κ) (h1 : OneForceStatement.{u} κ) :
    DistinctCompleteBelow.{u} κ 2 := by
  intro nL nR xL xR ρL ρR hD hc
  rcases (by omega : nL + nR = 0 ∨ nL + nR = 1) with h | h
  · exact @complete_of_card_eq_zero κ h0 nL nR xL xR ρL ρR h
  · exact @complete_of_card_eq_one κ h1 nL nR xL xR ρL ρR hD h

/-- LP6's word, after its reflection step: no left mark and two right marks `0 ≤ x₁ < x₂`, is a distinct-position
force word. -/
theorem isDistinctForceWord_of_two (xL : Fin 0 → ℝ) (xR : Fin 2 → ℝ) (hx0 : 0 ≤ xR 0)
    (hx : xR 0 < xR 1) : IsDistinctForceWord xL xR := by
  have hmono : StrictMono xR := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    rw [Fin.fin_one_eq_zero i]
    exact hx
  refine ⟨⟨fun i => i.elim0, fun i => i.elim0, hmono.monotone, fun i => ?_⟩, fun i => i.elim0, hmono⟩
  rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with h | h <;> rw [h]
  · exact hx0
  · exact hx0.trans hx.le

/-- **Proposition LP6 from Lemma LP9** (supplement p. 483; conditional helper with LP10's own inputs). For a word with
two right marks `0 ≤ x₁ < x₂` (LP6 after its reflection step), LP9 with `N = 2` groups and the target `x₂` (source
index `j = 2`, Lean index `1`) reduces completeness to the transformed word, which has the old target `−1` with weight
`k − 6 − S` on the left and `ψ(x₁)` with weight `r₁` on the right (LP6's proof, p. 484). That word is complete by Aux.
lemma 106 under the two-seed premise, and the words with at most one group are complete by the zero- and one-force
bases. -/
theorem lp6Statement_of_lp9 (h0 : ZeroForceStatement.{u} κ) (h1 : OneForceStatement.{u} κ)
    (h106 : Aux106Statement.{u} κ) (h9 : LP9Statement.{u} κ) : LP6Statement.{u} κ := by
  intro h2 xL ρL xR ρR hx0 hx
  have hD : IsDistinctForceWord xL xR := isDistinctForceWord_of_two xL xR hx0 hx
  have hT : IsDistinctForceWord (retargetXL (j := 1) (m := 0) xL xR) (retargetXR (j := 1) (m := 0) xR) :=
    isDistinctForceWord_retarget hD le_rfl
  have hW : IsCompleteForceWord.{u} κ (retargetXL (j := 1) (m := 0) xL xR) (retargetXR (j := 1) (m := 0) xR)
      (retargetρL (j := 1) (m := 0) κ ρL ρR) (retargetρR (j := 1) (m := 0) ρR) :=
    Aux106Statement.complete h106 h2 _ _ _ _ hT.1
  exact @LP9Statement.complete κ h9 2 (distinctCompleteBelow_two h0 h1) 0 1 0 xL xR ρL ρR hD rfl le_rfl hW

/-- **Theorem LP10 at one parameter without Proposition LP6**: the induction of `isCompleteForceWord_of_reductions`
with LP6 supplied by `lp6Statement_of_lp9`. -/
theorem isCompleteForceWord_of_reductions_noLP6 (h0 : ZeroForceStatement.{u} κ)
    (h1 : OneForceStatement.{u} κ) (h106 : Aux106Statement.{u} κ) (h113 : Aux113Statement.{u} κ)
    (h8 : LP8Statement.{u} κ) (h9 : LP9Statement.{u} κ) (h2 : TwoSeedComplete.{u} κ) {nL nR : ℕ}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hF : IsOrderedForceWord xL xR) : IsCompleteForceWord.{u} κ xL xR ρL ρR :=
  isCompleteForceWord_of_reductions h0 h1 h106 (lp6Statement_of_lp9 h0 h1 h106 h9) h113 h8 h9 h2 xL xR ρL ρR hF

/-- **The named input `LP10Statement` without Proposition LP6** (LP11's assembly, `LPAssembly.lean`): for every
`k > 4`, the zero- and one-force bases, Aux. lemmas 106 and 113, and Lemmas LP8 and LP9 give Theorem LP10. -/
theorem lp10Statement_of_reductions_noLP6 (h0 : ∀ κ : ℝ, 4 < κ → ZeroForceStatement.{u} κ)
    (h1 : ∀ κ : ℝ, 4 < κ → OneForceStatement.{u} κ) (h106 : ∀ κ : ℝ, 4 < κ → Aux106Statement.{u} κ)
    (h113 : ∀ κ : ℝ, 4 < κ → Aux113Statement.{u} κ) (h8 : ∀ κ : ℝ, 4 < κ → LP8Statement.{u} κ)
    (h9 : ∀ κ : ℝ, 4 < κ → LP9Statement.{u} κ) : LP10Statement.{u} :=
  lp10Statement_of_reductions h0 h1 h106
    (fun κ hκ => lp6Statement_of_lp9 (h0 κ hκ) (h1 κ hκ) (h106 κ hκ) (h9 κ hκ)) h113 h8 h9

end InteractingSLE.LP
