/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProbBase
import InteractingSLE.Spec.Supplement.LPAmalgamate

/-!
# §7.3: the revised induction for Theorem 1.3, `0 < κ < 4`, from its bases and steps

Packet PROVE-SEC7-C2. Specification §7.3, "Revised induction for Theorem 1.3, `0 < κ < 4`"
(`source/spec/p337-384.md` L843–L875, pp. 378–380):

> Aux. lemma 99 proves the full separated one-force assertion from the independent strip trace theorem.
> Aux. lemma 106 proves the two-force assertion for opposite sides […] from the admissible seed theorem.
> […] Zero force points give ordinary SLE, also covered by the admissible seed theorem with zero weights.
> The one-force seed case is part of that theorem, or has lifetime zero if inadmissible. Amalgamate
> coincident groups on the same side by adding their weights, and count these active groups. An
> inadmissible group initially at the seed gives an immediate continuation threshold. […]
> Suppose that the full continuity and transience assertion is known for at most `N − 1` active groups,
> where `N ≥ 2`. If `N = 2` and both sides contain a group, use Aux. lemma 106. If `N ≥ 3` and both sides
> contain groups, Aux. lemma 113 gives the result directly. […] It remains to consider marks on one side.
> […] This completes the induction step for every initial configuration with `N` groups.

This file proves the induction itself: the amalgamation of coincident marks (`LP.coincidentMarksTraceStatement`,
PROVE-LP), the zero-force base (`isCompleteForceWord_zero`, proved in `ContinuityProbBase`), the inadmissible
seed (`isCompleteForceWord_of_thresholdCondition`, proved here), the count of groups and the case analysis.
The bases and steps that the induction quotes are stated exactly, each as a `…Statement : Prop` with its
source, and are the hypotheses of **one conditional helper**, `revisedInductionLtFourStatement_of_inputs`. It
does not replace any source theorem; it isolates what remains.

| Input | Source | Section |
|---|---|---|
| `Prop73TraceStatement` | Proposition 7.3 (p. 242), the admissible two-seed theorem (continuity and transience) | §7.1 |
| `SeedOneForceTraceStatement` | the one-force seed case, "part of that theorem" (p. 378) | §7.1 |
| `Aux99Statement` | Aux. lemma 99 (p. 340), the full separated one-force assertion, `0 < κ < 4` | §7.3 |
| `Aux106Statement` | Aux. lemma 106 (p. 354), from the two-seed premise | §7.3 |
| `Aux113Statement` | Aux. lemma 113 (pp. 369–372) with its inputs Aux. 108–112, `N ≥ 3`, both sides | §7.3 |
| `OneSidedStepStatement` | the one-sided step of the revised induction (target change (C1)–(C2), pp. 378–380) | §7.3 |

Groups are counted on force words with distinct positions on each side (`LP.IsDistinctForceWord`), where every
mark is its own group; amalgamation reduces every ordered word to such a word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-! ### The inadmissible seed -/

/-- **An inadmissible seed group gives an immediate continuation threshold** (p. 378: "An inadmissible group
initially at the seed gives an immediate continuation threshold. There is then nothing to continue."). If the
threshold condition holds at the seed, the force word is complete: the lifetime is `0` almost surely, and the
constant trace `0` generates the (empty) chain on `[0, 0]`. -/
theorem isCompleteForceWord_of_thresholdCondition {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  filter_upwards [hE.ae_eq_zero_of_thresholdCondition] with ω hω
  have hζ : ζ ω = 0 := hω hthr
  refine ⟨fun _ => 0, ⟨rfl, continuousOn_const, fun t ht => ?_⟩, fun h => ?_⟩
  · rw [hζ] at ht
    exact absurd ht (not_lt.2 zero_le)
  · rw [hζ] at h
    exact absurd h ENNReal.zero_ne_top

/-! ### The bases and steps quoted by the induction (named inputs) -/

/-- **Named input (§7.1): the admissible two-seed theorem, Proposition 7.3** (Specification p. 242,
`source/spec/p241-288.md` L38; "the admissible seed theorem" of p. 378 and Aux. lemma 106, p. 354: "For
`0 < κ < 4` the premise is the preceding seed theorem"; graph node `SPEC.p337-384:revised-induction-kappa-lt-4#bases`
reads it as Proposition 7.3). For `0 < κ < 4` and weights `ρ^L, ρ^R > −2` at `0⁻, 0⁺`, the two-seed force word
is complete (continuous transient trace). -/
def Prop73TraceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (xL xR ρL ρR : Fin 1 → ℝ), (∀ i, xL i = 0) → (∀ i, xR i = 0) →
    (∀ i, -2 < ρL i) → (∀ i, -2 < ρR i) → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input (§7.1): the one-force seed case of the admissible seed theorem** (p. 378: "The one-force
seed case is part of that theorem, or has lifetime zero if inadmissible"). For `0 < κ < 4`, one mark at the
seed (`0⁻` or `0⁺`) with weight `ρ > −2` gives a complete force word. (The inadmissible case is proved:
`isCompleteForceWord_of_thresholdCondition`.) -/
def SeedOneForceTraceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), nL + nR = 1 → (∀ i, xL i = 0) → (∀ i, xR i = 0) → (∀ i, -2 < ρL i) →
    (∀ i, -2 < ρR i) → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input (§7.3): Aux. lemma 99, the full separated one-force assertion for `0 < κ < 4`**
(Specification p. 340, `source/spec/p337-384.md` L89–L140; p. 378: "Aux. lemma 99 proves the full separated
one-force assertion from the independent strip trace theorem"): one mark strictly away from the seed, with
any weight, gives a complete force word (continuity through the first swallow, the endpoint table (B1), and
for `0 < κ < 4` the continuation after an admissible swallow by the seed theorem). -/
def Aux99Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), nL + nR = 1 → (∀ i, xL i < 0) → (∀ i, 0 < xR i) →
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input (§7.3): Aux. lemma 106** (Specification p. 354, `source/spec/p337-384.md` L382–L416):
"Assume, for this parameter, continuity and transience for every two-force process whose marks are both at
the seed and whose weights exceed `−2`. Then the full continuity and transience assertion holds when there is
one force mark on each side of the seed, with arbitrary weights allowed up to the continuation threshold."
(Stated for `0 < κ < 4`, the range the induction uses.) -/
def Aux106Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
    (∀ (xL xR ρL ρR : Fin 1 → ℝ), (∀ i, xL i = 0) → (∀ i, xR i = 0) → (∀ i, -2 < ρL i) →
      (∀ i, -2 < ρR i) → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ (xL xR ρL ρR : Fin 1 → ℝ), IsOrderedForceWord xL xR → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input (§7.3): Aux. lemma 113, two-sided induction reduction, with its inputs** (Specification
pp. 369–372, `source/spec/p337-384.md` L688–L740; its premise "the local GFF comparison used in Aux. lemma
111" is Aux. lemmas 108–111, pp. 356–368, included here; for `κ ≤ 4` its alternatives (TI13.1) always hold,
`ti13_1_of_le_four`). For `0 < κ < 4` and `N ≥ 3`: if every force word with distinct positions and at most
`N − 1` groups is complete, then so is every such word with `N` groups, at least one on each side (the base
results it also assumes have at most two groups). -/
def Aux113Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ N : ℕ, 3 ≤ N →
    (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR ≤ N - 1 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 1 ≤ nL → 1 ≤ nR →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input (§7.3): the one-sided step of the revised induction** (Specification pp. 378–380,
`source/spec/p337-384.md` L847–L875: the target change `ψ(z) = z/(x₂ − z)` (C1), the transformed word (C2)
with exactly `N` groups on both sides, the pullback of the transformed stop through `ψ⁻¹` (old target
swallowed / transformed threshold / new target reached), the restart with at most `N − 1` groups and the join
through the continuously extended inverse map). For `0 < κ < 4` and `N ≥ 2`: if every distinct-position word
with at most `N − 1` groups and every one with `N` groups on both sides is complete, then so is every one with
`N` groups all on one side. -/
def OneSidedStepStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ N : ℕ, 2 ≤ N →
    (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR ≤ N - 1 → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → 1 ≤ nL → 1 ≤ nR →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      LP.IsDistinctForceWord xL xR → nL + nR = N → (nL = 0 ∨ nR = 0) →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR

/-! ### The induction -/

/-- A single force mark: the seed case, the inadmissible seed and the separated case. -/
theorem isCompleteForceWord_one (h1 : SeedOneForceTraceStatement.{u}) (h99 : Aux99Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) (hN : nL + nR = 1) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  obtain ⟨hxLa, hxL0, hxRm, hxR0⟩ := hF
  rcases (by omega : (nL = 0 ∧ nR = 1) ∨ (nL = 1 ∧ nR = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases (hxR0 0).lt_or_eq with hpos | hzero
    · exact h99 κ hκ hκ4 xL xR ρL ρR hN (fun i => i.elim0) (Fin.forall_fin_one.2 hpos)
    · by_cases hρ : -2 < ρR 0
      · exact h1 κ hκ hκ4 xL xR ρL ρR hN (fun i => i.elim0) (Fin.forall_fin_one.2 hzero.symm)
          (fun i => i.elim0) (Fin.forall_fin_one.2 hρ)
      · refine isCompleteForceWord_of_thresholdCondition (Or.inr ?_)
        have hf : Finset.univ.filter (fun i : Fin 1 => xR i = 0) = Finset.univ :=
          Finset.filter_true_of_mem fun i _ => by rw [Subsingleton.elim i 0]; exact hzero.symm
        rw [hf, Fin.sum_univ_one]
        exact not_lt.1 hρ
  · rcases (hxL0 0).lt_or_eq with hneg | hzero
    · exact h99 κ hκ hκ4 xL xR ρL ρR hN (Fin.forall_fin_one.2 hneg) (fun i => i.elim0)
    · by_cases hρ : -2 < ρL 0
      · exact h1 κ hκ hκ4 xL xR ρL ρR hN (Fin.forall_fin_one.2 hzero) (fun i => i.elim0)
          (Fin.forall_fin_one.2 hρ) (fun i => i.elim0)
      · refine isCompleteForceWord_of_thresholdCondition (Or.inl ?_)
        have hf : Finset.univ.filter (fun i : Fin 1 => xL i = 0) = Finset.univ :=
          Finset.filter_true_of_mem fun i _ => by rw [Subsingleton.elim i 0]; exact hzero
        rw [hf, Fin.sum_univ_one]
        exact not_lt.1 hρ

/-- **The revised induction for Theorem 1.3, `0 < κ < 4`, from its bases and steps** (conditional helper;
Specification pp. 378–380). Every ordered force word is complete for every `0 < κ < 4`, given the two-seed
and one-force seed theorems (Proposition 7.3, §7.1), Aux. lemmas 99, 106 and 113, and the one-sided step. The
induction on the number of groups, the amalgamation of coincident marks, the zero-force base and the
inadmissible seed are proved. -/
theorem revisedInductionLtFourStatement_of_inputs (h73 : Prop73TraceStatement.{u})
    (h1 : SeedOneForceTraceStatement.{u}) (h99 : Aux99Statement.{u}) (h106 : Aux106Statement.{u})
    (h113 : Aux113Statement.{u}) (h1s : OneSidedStepStatement.{u}) :
    LP.RevisedInductionLtFourStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF
  -- the two-sided words with one group on each side (Aux. lemma 106 from Proposition 7.3)
  have h2 : ∀ (xL xR ρL ρR : Fin 1 → ℝ), IsOrderedForceWord xL xR →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := h106 κ hκ hκ4 (h73 κ hκ hκ4)
  -- the induction on the number of groups of a distinct-position word
  have key : ∀ N : ℕ, ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
      (ρR : Fin nR → ℝ), LP.IsDistinctForceWord xL xR → nL + nR ≤ N →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
    intro N
    induction N with
    | zero =>
      intro nL nR xL xR ρL ρR _ hN
      obtain ⟨rfl, rfl⟩ : nL = 0 ∧ nR = 0 := by omega
      exact isCompleteForceWord_of_forall_eq_zero hκ xL xR (fun i => i.elim0) (fun i => i.elim0)
    | succ N ih =>
      intro nL nR xL xR ρL ρR hD hN
      rcases (Nat.lt_or_ge (nL + nR) (N + 1)) with hlt | hge
      · exact ih xL xR ρL ρR hD (by omega)
      have hM : nL + nR = N + 1 := le_antisymm hN hge
      have ih' : ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
          (ρR : Fin nR → ℝ), LP.IsDistinctForceWord xL xR → nL + nR ≤ (N + 1) - 1 →
          LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := fun xL xR ρL ρR hD hle =>
        ih xL xR ρL ρR hD (by omega)
      -- the two-sided words with `N + 1` groups
      have htwo : ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
          (ρR : Fin nR → ℝ), LP.IsDistinctForceWord xL xR → nL + nR = N + 1 → 1 ≤ nL → 1 ≤ nR →
          LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
        intro nL nR xL xR ρL ρR hD hM hL hR
        rcases (by omega : N + 1 = 2 ∨ 3 ≤ N + 1) with h2' | h3
        · obtain ⟨rfl, rfl⟩ : nL = 1 ∧ nR = 1 := by omega
          exact h2 xL xR ρL ρR hD.1
        · exact h113 κ hκ hκ4 (N + 1) h3 ih' xL xR ρL ρR hD hM hL hR
      rcases (by omega : N + 1 = 1 ∨ 2 ≤ N + 1) with h1' | h2'
      · have hN1 : nL + nR = 1 := by omega
        intro Ω mΩ
        exact isCompleteForceWord_one h1 h99 hκ hκ4 xL xR ρL ρR hD.1 hN1
      · intro Ω mΩ
        by_cases hside : nL = 0 ∨ nR = 0
        · exact h1s κ hκ hκ4 (N + 1) h2' ih' htwo xL xR ρL ρR hD hM hside
        · push Not at hside
          exact htwo xL xR ρL ρR hD hM (Nat.one_le_iff_ne_zero.2 hside.1)
            (Nat.one_le_iff_ne_zero.2 hside.2)
  intro Ω mΩ
  exact LP.coincidentMarksTraceStatement κ (fun xL xR ρL ρR hD => key _ xL xR ρL ρR hD le_rfl)
    xL xR ρL ρR hF

end Sec7

end InteractingSLE
