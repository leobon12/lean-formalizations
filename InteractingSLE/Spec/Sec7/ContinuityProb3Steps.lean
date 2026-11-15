/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb3Cont
import InteractingSLE.Spec.Supplement.LPProbInduction

/-!
# §7.3: Aux. lemma 113, the one-sided step and LP9 from their prefix parts

Packet PROVE-RANDRESTART2. Each of these results stops the evolution at a time `τ` at which (if `τ < ζ`) two force
groups have merged, restarts with the smaller group count, and joins the future trace to the prefix:

* Aux. lemma 113 (pp. 369–372): "Stop at the continuation threshold or when two distinct groups on the same side
  have been swallowed and merge, whichever comes first. Call this time `τ`. If `τ < ∞` and continuation is allowed,
  at most `N − 1` active groups remain. The induction hypothesis in the remaining component, and its continuously
  extended inverse hydrodynamic map, then give the required continuation and transience. It remains to treat
  `τ = ∞`."
* The one-sided step (pp. 378–380): the target change `ψ(z) = z/(x₂ − z)` is used until the old and new targets
  separate; at the separation (or at the new target) "the first two original groups merge" and "the original
  process continues with at most `N − 1` active groups"; "In every continuation case the smaller-count hypothesis
  gives a continuous future trace in the original remaining component" and the inverse map joins it.
* Lemma LP9 (supplement p. 485) is the same retargeting with a strict group-count decrease.

The restart and the join are proved (`isCompleteForceWord_of_hasCountPrefix`: `randomRestartTraceStatement`, the
join `IsGeneratingTraceIcc.join`, amalgamation). What remains of each result is its *prefix part*, stated exactly
as a named input:

* `Aux113PrefixStatement`: finite-time continuity through `τ` (Aux. lemma 103) and transience on `τ = ∞` (the
  finite angular clock/band argument for a nonpositive endpoint parameter, the moving-midpoint trials with the local
  GFF comparison of Aux. lemmas 108–111 and Lévy's upward theorem (TI15.1) for two positive ones);
* `OneSidedPrefixStatement`: the integrated target-change identity (C1)–(C2), the transformed word's completeness
  (Aux. lemmas 106/113, a premise), the pullback of the transformed prefix through `ψ⁻¹` with finite original
  capacity, and Aux. lemma 3 for the case `q = −1`;
* `LP9PrefixStatement`: the same for LP9's retargeting.

Aux. lemma 106 has no restart step; `aux106Statement_of_separated` proves its seed case and names the case with a
positive cross-gap (`Aux106SeparatedStatement`).

These are conditional helpers. They replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-! ### Aux. lemma 113 (κ < 4) -/

/-- **Named input: the prefix part of Aux. lemma 113** (Specification pp. 369–372, `source/spec/p337-384.md`
L688–L740). For `0 < κ < 4`, `N ≥ 3`, under the smaller-count hypothesis, every evolution of a distinct-position
word with `N` marks, at least one on each side, has a stopping time `τ ≤ ζ` (the first merger of two same-side
groups, or the continuation threshold) with a continuous generating trace through `τ` (closed at `τ` when `τ < ζ`;
transient when `τ = ∞`), and fewer than `N` distinct positions at `τ < ζ`. -/
def Aux113PrefixStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ N : ℕ, 3 ≤ N →
    (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR ≤ N - 1 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 1 ≤ nL → 1 ≤ nR →
      HasCountPrefix.{u} κ xL xR ρL ρR N

/-- The smaller-count hypothesis `nL + nR ≤ N − 1` of §7.3 is `LP.DistinctCompleteBelow κ N` (`N ≥ 1`). -/
theorem distinctCompleteBelow_of_le {κ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (h : ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR ≤ N - 1 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) :
    LP.DistinctCompleteBelow.{u} κ N := fun xL xR ρL ρR hd hlt => h xL xR ρL ρR hd (by omega)

/-- **`Sec7.Aux113Statement` (the input of the κ < 4 induction) from its prefix part.** -/
theorem aux113Statement_of_prefix (h : Aux113PrefixStatement.{u}) : Aux113Statement.{u} := by
  intro κ hκ hκ4 N hN hbelow nL nR xL xR ρL ρR hd hsum hL hR
  have hD : LP.DistinctCompleteBelow.{u} κ N := distinctCompleteBelow_of_le (by omega) hbelow
  intro Ω mΩ
  exact isCompleteForceWord_of_hasCountPrefix hκ hD (h κ hκ hκ4 N hN hbelow xL xR ρL ρR hd hsum hL hR)

/-! ### The one-sided step (κ < 4) -/

/-- **Named input: the prefix part of the one-sided step of the revised induction** (Specification pp. 378–380,
`source/spec/p337-384.md` L847–L875). For `0 < κ < 4`, `N ≥ 2`, under the smaller-count hypothesis and the
two-sided `N`-group hypothesis (the transformed word (C2) is two-sided with `N` groups), every evolution of a
distinct-position word with `N` marks all on one side has a stopping time `τ ≤ ζ` (the separation of the old and new
targets, the arrival at the new target `x₂`, or the original threshold) with a continuous generating trace through
`τ` (closed at `τ` when `τ < ζ`; transient when `τ = ∞`, the case `q = −1`), and fewer than `N` distinct positions
at `τ < ζ` (the first two groups have merged). -/
def OneSidedPrefixStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ N : ℕ, 2 ≤ N →
    (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR ≤ N - 1 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 1 ≤ nL → 1 ≤ nR →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → (nL = 0 ∨ nR = 0) →
      HasCountPrefix.{u} κ xL xR ρL ρR N

/-- **`Sec7.OneSidedStepStatement` (the input of the κ < 4 induction) from its prefix part.** -/
theorem oneSidedStepStatement_of_prefix (h : OneSidedPrefixStatement.{u}) : OneSidedStepStatement.{u} := by
  intro κ hκ hκ4 N hN hbelow htwo nL nR xL xR ρL ρR hd hsum hside
  have hD : LP.DistinctCompleteBelow.{u} κ N := distinctCompleteBelow_of_le (by omega) hbelow
  intro Ω mΩ
  exact isCompleteForceWord_of_hasCountPrefix hκ hD
    (h κ hκ hκ4 N hN hbelow htwo xL xR ρL ρR hd hsum hside)

/-! ### The supplement's forms (every κ > 0) -/

/-- **Named input: the prefix part of Aux. lemma 113 in LP10's form** (`LP.Aux113Statement`, every `κ`, with the
alternatives (TI13.1)). -/
def LPAux113PrefixStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → LP.DistinctCompleteBelow.{u} κ N → LP.TwoSeedComplete.{u} κ →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 0 < nL → 0 < nR →
      ((∑ i, ρL i) ≤ -2 ∨ (∑ i, ρR i) ≤ -2 ∨
        (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i)) →
        HasCountPrefix.{u} κ xL xR ρL ρR N

/-- **`LP.Aux113Statement κ` from its prefix part**, `κ > 0`. -/
theorem lpAux113Statement_of_prefix {κ : ℝ} (hκ : 0 < κ) (h : LPAux113PrefixStatement.{u} κ) :
    LP.Aux113Statement.{u} κ := by
  intro N hN hD h2 nL nR xL xR ρL ρR hd hsum hL hR hTI Ω mΩ
  exact isCompleteForceWord_of_hasCountPrefix hκ hD (h N hN hD h2 xL xR ρL ρR hd hsum hL hR hTI)

/-- **Named input: the prefix part of Lemma LP9** (supplement p. 485, retargeting the actual mark `x_j`, `j ≥ 2`,
by `ψ(z) = z/(x_j − z)`; the transformed word is complete by hypothesis). -/
def LP9PrefixStatement (κ : ℝ) : Prop :=
  ∀ N : ℕ, LP.DistinctCompleteBelow.{u} κ N →
    ∀ {nL j m : ℕ} (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) (ρL : Fin nL → ℝ)
      (ρR : Fin (j + 1 + m) → ℝ), LP.IsDistinctForceWord xL xR → nL + (j + 1 + m) = N → 1 ≤ j →
      LP.IsCompleteForceWord.{u} κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
        (LP.retargetρR ρR) →
        HasCountPrefix.{u} κ xL xR ρL ρR N

/-- **`LP.LP9Statement κ` from its prefix part**, `κ > 0`. -/
theorem lp9Statement_of_prefix {κ : ℝ} (hκ : 0 < κ) (h : LP9PrefixStatement.{u} κ) :
    LP.LP9Statement.{u} κ := by
  intro N hD nL j m xL xR ρL ρR hd hsum hj hT Ω mΩ
  exact isCompleteForceWord_of_hasCountPrefix hκ hD (h N hD xL xR ρL ρR hd hsum hj hT)

/-! ### Aux. lemma 106 (κ < 4): the seed case -/

/-- **Named input: Aux. lemma 106 with a positive cross-gap** (Specification p. 354, `source/spec/p337-384.md`
L382–L416, from "Otherwise the cross-gap `D_0` is positive": finite-time continuity by Aux. lemma 103 with `N = 2`,
transience by the finite angular clock (Aux. lemma 102) and the band comparison when `a ≤ 0` or `b ≤ 0`, and by the
clock change (J12), Aux. lemma 100 and the stationary two-sided Jacobi path-law transfer (J14) with [Yua22]
Corollary 1.3 when `a, b > 0`). For `0 < κ < 4`, under the two-seed premise, a word with one mark on each side, not
both at the seed, is complete. -/
def Aux106SeparatedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
    (∀ (xL xR ρL ρR : Fin 1 → ℝ), (∀ i, xL i = 0) → (∀ i, xR i = 0) → (∀ i, -2 < ρL i) →
      (∀ i, -2 < ρR i) → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ (xL xR ρL ρR : Fin 1 → ℝ), IsOrderedForceWord xL xR → (xL 0 < 0 ∨ 0 < xR 0) →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **`Sec7.Aux106Statement` from its positive-cross-gap case.** Both marks at the seed: the premise if both weights
exceed `−2` (p. 354: "If both marks are at the seed, the stated base case applies unless a group is initially
inadmissible, in which case the lifetime is zero"), and an immediate continuation threshold otherwise. -/
theorem aux106Statement_of_separated (h : Aux106SeparatedStatement.{u}) : Aux106Statement.{u} := by
  intro κ hκ hκ4 h2 xL xR ρL ρR hF Ω mΩ
  rcases (hF.2.1 0).lt_or_eq with hL | hL
  · exact h κ hκ hκ4 h2 xL xR ρL ρR hF (Or.inl hL)
  rcases (hF.2.2.2 0).lt_or_eq with hR | hR
  · exact h κ hκ hκ4 h2 xL xR ρL ρR hF (Or.inr hR)
  have hxL : ∀ i, xL i = 0 := fun i => by rw [Subsingleton.elim i 0]; exact hL
  have hxR : ∀ i, xR i = 0 := fun i => by rw [Subsingleton.elim i 0]; exact hR.symm
  have hfL : Finset.univ.filter (fun i : Fin 1 => xL i = 0) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => hxL i
  have hfR : Finset.univ.filter (fun i : Fin 1 => xR i = 0) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => hxR i
  by_cases hρL : -2 < ρL 0
  · by_cases hρR : -2 < ρR 0
    · exact h2 xL xR ρL ρR hxL hxR (fun i => by rw [Subsingleton.elim i 0]; exact hρL)
        (fun i => by rw [Subsingleton.elim i 0]; exact hρR)
    · refine isCompleteForceWord_of_thresholdCondition (Or.inr ?_)
      rw [hfR, Fin.sum_univ_one]
      exact not_lt.1 hρR
  · refine isCompleteForceWord_of_thresholdCondition (Or.inl ?_)
    rw [hfL, Fin.sum_univ_one]
    exact not_lt.1 hρL

end Sec7

end InteractingSLE
