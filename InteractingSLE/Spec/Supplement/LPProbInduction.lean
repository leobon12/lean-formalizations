/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPProbReflect
import InteractingSLE.Spec.Supplement.LPProbRetarget

/-!
# Theorem LP10: the large-parameter finite-force induction

Packet PROVE-R17. Supplement §6.5, Theorem LP10 (`source/spec/p481-528.md` L134–L161, pp. 486–487):
"Fix `k > 4`. Assume the full two-seed continuity and transience theorem for every admissible pair,
the independent one-force first-swallow theorem, and the whole-history buffered comparisons of Aux.
108–111. Then every integrated finite-force law has a continuous trace up to and including its finite
continuation threshold, and its trace tends to infinity on infinite lifetime."

This file formalizes **the proof of LP10** — the induction on the number of finite force groups, its
base cases, the choice of the low-total side, the choice of the retargeted mark, and the sector
bookkeeping through (LP9.1) — from named statements of the results it cites:

| Named input | Source | Section |
|---|---|---|
| `ZeroForceStatement` | ordinary SLE (§7.3 L843; LP10 p. 486) | §7.3 / Foundations |
| `OneForceStatement` | Aux. lemma 99 + the one-seed theorem (§7.3 L89; supplement p. 479) | §7.3, §6.1 |
| `Aux106Statement` | Aux. lemma 106 (§7.3 L382) | §7.3 |
| `Aux113Statement` | Aux. lemma 113, (LP10.1) (§7.3 L688) | §7.3 |
| `LP6Statement` | Proposition LP6 (p. 483) | supplement §6.4 |
| `LP8Statement` | Lemma LP8 (p. 485) | supplement §6.5 |
| `LP9Statement` | Lemma LP9 (p. 485) | supplement §6.5 |

The main results are `distinctCompleteBelow_of_reductions` (the induction),
`isCompleteForceWord_of_reductions` (LP10 at one parameter, all ordered words, by amalgamation) and
`lp10Statement_of_reductions` (the named input `LP10Statement` of LP11's assembly). **LP10 is not
proved outright**: LP6, LP8, LP9 (this section) and the §7.3 inputs remain; see
`planning/handoffs/PROVE-R17.md`.

Counting convention. After amalgamation (`LPAmalgamate.lean`) a word has distinct positions on each
side and its finite force groups are its marks; the induction is on `nL + nR`.
`isCompleteForceWord_of_distinctCompleteBelow` shows that the induction state `DistinctCompleteBelow κ N`
gives the source's "at most `N − 1` groups" form for every ordered word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.LP

/-! ### Partial sums of a side -/

/-- The weights of a side extended by zero to `ℕ`. -/
def extWeight {n : ℕ} (ρ : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then ρ ⟨i, h⟩ else 0

/-- The partial sum `S_k = ρ_1 + ⋯ + ρ_k` (source indexing) of a side. -/
def partialSum {n : ℕ} (ρ : Fin n → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, extWeight ρ i

/-- `extWeight` agrees with the weights on `Fin n`. -/
theorem extWeight_val {n : ℕ} (ρ : Fin n → ℝ) (i : Fin n) : extWeight ρ i = ρ i := by
  simp [extWeight]

/-- `S_n` is the side total. -/
theorem partialSum_self {n : ℕ} (ρ : Fin n → ℝ) : partialSum ρ n = ∑ i, ρ i := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => extWeight_val ρ i

/-- `S_{j−1}` (source indexing) of a right list split at the target. -/
theorem partialSum_retarget {j m : ℕ} (ρ : Fin (j + 1 + m) → ℝ) :
    partialSum ρ j = ∑ i : Fin j, ρ (Fin.castAdd m i.castSucc) := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [extWeight, show (i : ℕ) < j + 1 + m by omega, ↓reduceDIte]
  rfl

/-- `S_j` (source indexing) of a right list split at the target. -/
theorem partialSum_retarget_succ {j m : ℕ} (ρ : Fin (j + 1 + m) → ℝ) :
    partialSum ρ (j + 1) = (∑ i : Fin j, ρ (Fin.castAdd m i.castSucc)) + ρ (retargetIdx j m) := by
  rw [partialSum, sum_range_succ, ← partialSum, partialSum_retarget]
  simp only [extWeight, show j < j + 1 + m by omega, ↓reduceDIte]
  rfl


/-! ### The induction state and the two-seed premise -/

/-- **The induction state of LP10**: every force word with distinct positions on each side and
fewer than `N` marks (= finite force groups) is complete at `κ`. By amalgamation
(`isCompleteForceWord_of_distinctCompleteBelow`) this is the source's "complete continuity and
transience theorem for every configuration with at most `N − 1` finite force groups". -/
def DistinctCompleteBelow (κ : ℝ) (N : ℕ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsDistinctForceWord xL xR → nL + nR < N → IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **The premise of LP6, LP8, LP10 and Aux. lemma 106**: "the full two-seed continuity and
transience theorem for every admissible pair", i.e. the two-seed word `SLE_k(r_L; r_R)` is complete
for all `r_L, r_R > −2`. -/
def TwoSeedComplete (κ : ℝ) : Prop :=
  ∀ rL rR : ℝ, -2 < rL → -2 < rR →
    IsCompleteForceWord.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR)

/-- The induction state is equivalent to the source's group-count form: an ordered force word with
fewer than `N` distinct positions in total (its finite force groups, counted side by side) is
complete once all distinct words with fewer than `N` marks are (amalgamation, `LPAmalgamate.lean`). -/
theorem isCompleteForceWord_of_distinctCompleteBelow {κ : ℝ} {N : ℕ}
    (h : DistinctCompleteBelow.{u} κ N) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hcount : (Finset.univ.image xL).card + (Finset.univ.image xR).card < N) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact h (amXL xL) (amPos xR) _ _ (isDistinctForceWord_amalgamate hF) hcount P 𝓕 W _ _ B ζ
    (hE.amalgamate hF)

/-! ### Named inputs

Each is a `…Statement : Prop` stating one result of the specification, with its exact source, on the
frozen carriers. The inputs from §7.3 are results of another section (Aux. lemmas 99, 106, 113,
stated there for every `κ > 0`); LP6, LP8 and LP9 are results of supplement §6 whose proofs need the
integrated target-change identity, the strong Markov property and the buffered comparisons (see the
handoff `planning/handoffs/PROVE-R17.md`); they are not proved here. -/

/-- **Named input: the zero-force base** (§7.3, `source/spec/p337-384.md` L843: "Zero force points
give ordinary SLE"; LP10, p. 486: "With zero groups use ordinary SLE"). The empty word is complete.
Provided for every `κ > 0` by `Sec7.isCompleteForceWord_zero` (PROVE-SEC7-C2, in flight). -/
def ZeroForceStatement (κ : ℝ) : Prop :=
  ∀ (xL : Fin 0 → ℝ) (xR : Fin 0 → ℝ) (ρL : Fin 0 → ℝ) (ρR : Fin 0 → ℝ),
    IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input: one force group** (LP10, p. 486: "With one group use Aux. lemma 99 through its
first swallow and the one-seed theorem for every admissible continuation"; Aux. lemma 99,
`source/spec/p337-384.md` L89, and the one-seed theorem, supplement p. 479 "One-seed parameter
coverage"). Every word with a single right mark `x ≥ 0` (any weight) is complete. The left-mark case
follows by reflection (`oneForce_left`). -/
def OneForceStatement (κ : ℝ) : Prop :=
  ∀ (xL : Fin 0 → ℝ) (ρL : Fin 0 → ℝ) (xR : Fin 1 → ℝ) (ρR : Fin 1 → ℝ), 0 ≤ xR 0 →
    IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input: Aux. lemma 106** (`source/spec/p337-384.md` L382, §7.3: "Assume, for this
parameter, continuity and transience for every two-force process whose marks are both at the seed
and whose weights exceed `−2`. Then the full continuity and transience assertion holds when there
is one force mark on each side of the seed, with arbitrary weights allowed up to the continuation
threshold"). -/
def Aux106Statement (κ : ℝ) : Prop :=
  TwoSeedComplete.{u} κ → ∀ (xL xR ρL ρR : Fin 1 → ℝ), IsOrderedForceWord xL xR →
    IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input: Proposition LP6** (supplement §6.4, `source/spec/p481-528.md` L77, p. 483: "Assume
that every canonical two-seed law with both weights greater than `−2` has a continuous trace on every
finite interval and is transient. Assume the integrated target-change identity […]. Then every law
with two same-side force groups has a continuous trace up to and including its finite continuation
threshold and is transient on infinite lifetime."), after its first proof step "Reflect so that the
positions are `0 ≤ x₁ < x₂`" (the reflection is `isCompleteForceWord_reflect_iff`). The
target-change identity is an input of its proof, not a premise here. -/
def LP6Statement (κ : ℝ) : Prop :=
  TwoSeedComplete.{u} κ → ∀ (xL ρL : Fin 0 → ℝ) (xR ρR : Fin 2 → ℝ), 0 ≤ xR 0 → xR 0 < xR 1 →
    IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input: Aux. lemma 113** (`source/spec/p337-384.md` L688, §7.3, the two-sided induction
reduction including transience: "Let `κ > 0`, `N ≥ 3`, and `d = κ/2 − 4`. Assume the full continuity
and transience assertion for at most `N − 1` active groups, the one- and two-force-point base results
for this parameter, and the local GFF comparison used in Aux. lemma 111. Suppose at least one of the
`N` groups lies on each side of the seed […]. The full assertion for this configuration follows if
`s_L ≤ −2` or `s_R ≤ −2` or `s_L, s_R > d`" ((LP10.1), p. 487)). The local GFF comparison (Aux.
lemmas 108–111) is an input of its proof. -/
def Aux113Statement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → DistinctCompleteBelow.{u} κ N → TwoSeedComplete.{u} κ →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsDistinctForceWord xL xR → nL + nR = N → 0 < nL → 0 < nR →
      ((∑ i, ρL i) ≤ -2 ∨ (∑ i, ρR i) ≤ -2 ∨
        (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i)) →
        IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input: Lemma LP8** (supplement §6.5, `source/spec/p481-528.md` L109, p. 485, the singleton
extension of Aux. lemma 113: "Fix `k > 0`, `N ≥ 3`, and assume the complete continuity and
transience theorem for every configuration with at most `N − 1` finite force groups, together with
the complete two-seed theorem. Besides the three alternatives stated in Aux. lemma 113, its
conclusion holds if one side is a single admissible group and the total weight of the other side
exceeds `d = k/2 − 4`"), in the orientation of its proof ("Suppose the right side is the
singleton"); "Reflection proves the other orientation" is `lp8_left`. -/
def LP8Statement (κ : ℝ) : Prop :=
  ∀ N : ℕ, 3 ≤ N → DistinctCompleteBelow.{u} κ N → TwoSeedComplete.{u} κ →
    ∀ {nL : ℕ} (xL : Fin nL → ℝ) (xR : Fin 1 → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin 1 → ℝ),
      IsDistinctForceWord xL xR → nL + 1 = N → -2 < ρR 0 → κ / 2 - 4 < ∑ i, ρL i →
        IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input: Lemma LP9** (supplement §6.5, `source/spec/p481-528.md` L117, p. 485,
retargeting with a strict group-count decrease: "Suppose a configuration has `N` designated finite
force groups and at least two groups on its right. […] For an index `j ≥ 2`, target the actual mark
`x_j` by `ψ(z) = z/(x_j − z)`. […] If the complete theorem is available for that transformed word and
for all words with at most `N − 1` groups, then it holds for the original word."). The transformed
word is `retargetXL`, `retargetXR`, `retargetρL`, `retargetρR` (`LPProbRetarget.lean`); the Lean
target index `j ≥ 1` is the source index `j + 1 ≥ 2`. -/
def LP9Statement (κ : ℝ) : Prop :=
  ∀ N : ℕ, DistinctCompleteBelow.{u} κ N →
    ∀ {nL j m : ℕ} (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) (ρL : Fin nL → ℝ)
      (ρR : Fin (j + 1 + m) → ℝ), IsDistinctForceWord xL xR → nL + (j + 1 + m) = N → 1 ≤ j →
      IsCompleteForceWord.{u} κ (retargetXL xL xR) (retargetXR xR) (retargetρL κ ρL ρR)
        (retargetρR ρR) →
        IsCompleteForceWord.{u} κ xL xR ρL ρR


/-! ### Application lemmas

`IsCompleteForceWord` unfolds to a statement with implicit binders; these lemmas apply a named input
with a folded conclusion, so that it closes a goal in either form. -/

section Apply

variable {κ : ℝ}

/-- Completeness of a word from completeness of its reflection. -/
theorem complete_of_reflect {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (h : IsCompleteForceWord.{u} κ (-xR) (-xL) ρR ρL) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact isCompleteForceWord_reflect_iff.1 h

/-- Application of `DistinctCompleteBelow`. -/
theorem DistinctCompleteBelow.complete {N : ℕ} (h : DistinctCompleteBelow.{u} κ N) {nL nR : ℕ}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hD : IsDistinctForceWord xL xR) (hc : nL + nR < N) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact h xL xR ρL ρR hD hc

/-- Application of `ZeroForceStatement`. -/
theorem ZeroForceStatement.complete (h : ZeroForceStatement.{u} κ) (xL xR ρL ρR : Fin 0 → ℝ) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact h xL xR ρL ρR

/-- Application of `OneForceStatement`. -/
theorem OneForceStatement.complete (h : OneForceStatement.{u} κ) (xL ρL : Fin 0 → ℝ)
    (xR ρR : Fin 1 → ℝ) (hx : 0 ≤ xR 0) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact h xL ρL xR ρR hx

/-- Application of `Aux106Statement`. -/
theorem Aux106Statement.complete (h : Aux106Statement.{u} κ) (h2 : TwoSeedComplete.{u} κ)
    (xL xR ρL ρR : Fin 1 → ℝ) (hF : IsOrderedForceWord xL xR) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact h h2 xL xR ρL ρR hF

/-- Application of `LP6Statement`. -/
theorem LP6Statement.complete (h : LP6Statement.{u} κ) (h2 : TwoSeedComplete.{u} κ)
    (xL ρL : Fin 0 → ℝ) (xR ρR : Fin 2 → ℝ) (hx0 : 0 ≤ xR 0) (hx : xR 0 < xR 1) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact h h2 xL ρL xR ρR hx0 hx

/-- Application of `Aux113Statement`. -/
theorem Aux113Statement.complete (h : Aux113Statement.{u} κ) {N : ℕ} (hN : 3 ≤ N)
    (IH : DistinctCompleteBelow.{u} κ N) (h2 : TwoSeedComplete.{u} κ) {nL nR : ℕ}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hD : IsDistinctForceWord xL xR) (hc : nL + nR = N) (hL : 0 < nL) (hR : 0 < nR)
    (hs : (∑ i, ρL i) ≤ -2 ∨ (∑ i, ρR i) ≤ -2 ∨
        (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i)) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact h N hN IH h2 xL xR ρL ρR hD hc hL hR hs

/-- Application of `LP8Statement`. -/
theorem LP8Statement.complete (h : LP8Statement.{u} κ) {N : ℕ} (hN : 3 ≤ N)
    (IH : DistinctCompleteBelow.{u} κ N) (h2 : TwoSeedComplete.{u} κ) {nL : ℕ} (xL : Fin nL → ℝ)
    (xR : Fin 1 → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin 1 → ℝ) (hD : IsDistinctForceWord xL xR)
    (hc : nL + 1 = N) (hr : -2 < ρR 0) (hl : κ / 2 - 4 < ∑ i, ρL i) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact h N hN IH h2 xL xR ρL ρR hD hc hr hl

/-- Application of `LP9Statement`. -/
theorem LP9Statement.complete (h : LP9Statement.{u} κ) {N : ℕ}
    (IH : DistinctCompleteBelow.{u} κ N) {nL j m : ℕ} (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin (j + 1 + m) → ℝ) (hD : IsDistinctForceWord xL xR)
    (hc : nL + (j + 1 + m) = N) (hj : 1 ≤ j)
    (hW : IsCompleteForceWord.{u} κ (retargetXL xL xR) (retargetXR xR) (retargetρL κ ρL ρR)
      (retargetρR ρR)) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ; exact h N IH xL xR ρL ρR hD hc hj hW

end Apply

/-! ### Reflected orientations -/

section Orientations

variable {κ : ℝ}

/-- The left-mark case of `OneForceStatement`, by reflection. -/
theorem oneForce_left (h1 : OneForceStatement.{u} κ) (xL ρL : Fin 1 → ℝ) (xR ρR : Fin 0 → ℝ)
    (hx : xL 0 ≤ 0) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  refine complete_of_reflect ?_
  exact OneForceStatement.complete h1 (-xR) ρR (-xL) ρL (neg_nonneg.2 hx)

/-- The left-side case of LP6 ("Reflect so that the positions are `0 ≤ x₁ < x₂`"). -/
theorem lp6_left (h6 : LP6Statement.{u} κ) (h2 : TwoSeedComplete.{u} κ) (xL ρL : Fin 2 → ℝ)
    (xR ρR : Fin 0 → ℝ) (hx0 : xL 0 ≤ 0) (hx : xL 1 < xL 0) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  refine complete_of_reflect ?_
  exact LP6Statement.complete h6 h2 (-xR) ρR (-xL) ρL (neg_nonneg.2 hx0) (neg_lt_neg hx)

/-- The left-singleton case of LP8 ("Reflection proves the other orientation"). -/
theorem lp8_left (h8 : LP8Statement.{u} κ) {N : ℕ} (hN : 3 ≤ N) (IH : DistinctCompleteBelow.{u} κ N)
    (h2 : TwoSeedComplete.{u} κ) {nR : ℕ} (xL : Fin 1 → ℝ) (xR : Fin nR → ℝ) (ρL : Fin 1 → ℝ)
    (ρR : Fin nR → ℝ) (hD : IsDistinctForceWord xL xR) (hc : 1 + nR = N) (hl : -2 < ρL 0)
    (hr : κ / 2 - 4 < ∑ i, ρR i) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  refine complete_of_reflect ?_
  exact LP8Statement.complete h8 hN IH h2 (-xR) (-xL) ρR ρL hD.reflect (by omega) hl hr

end Orientations

/-! ### The base cases: at most two groups -/

section Base

variable {κ : ℝ}

/-- No marks: ordinary SLE. -/
theorem complete_of_card_eq_zero (h0 : ZeroForceStatement.{u} κ) {nL nR : ℕ} (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hc : nL + nR = 0) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  obtain ⟨rfl, rfl⟩ : nL = 0 ∧ nR = 0 := by omega
  exact ZeroForceStatement.complete h0 xL xR ρL ρR

/-- One mark: Aux. lemma 99 with the one-seed theorem, on either side. -/
theorem complete_of_card_eq_one (h1 : OneForceStatement.{u} κ) {nL nR : ℕ} (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hD : IsDistinctForceWord xL xR)
    (hc : nL + nR = 1) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  rcases Nat.eq_zero_or_pos nL with rfl | hL
  · obtain rfl : nR = 1 := by omega
    exact OneForceStatement.complete h1 xL ρL xR ρR (hD.1.2.2.2 0)
  · obtain ⟨rfl, rfl⟩ : nL = 1 ∧ nR = 0 := by omega
    exact oneForce_left h1 xL ρL xR ρR (hD.1.2.1 0)

/-- Two marks: Aux. lemma 106 (opposite sides) and LP6 (same side, either orientation). -/
theorem complete_of_card_eq_two (h106 : Aux106Statement.{u} κ) (h6 : LP6Statement.{u} κ)
    (h2 : TwoSeedComplete.{u} κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hD : IsDistinctForceWord xL xR) (hc : nL + nR = 2) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  rcases (by omega : (nL = 0 ∧ nR = 2) ∨ (nL = 1 ∧ nR = 1) ∨ (nL = 2 ∧ nR = 0)) with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact LP6Statement.complete h6 h2 xL ρL xR ρR (hD.1.2.2.2 0) (hD.2.2 (by decide))
  · exact Aux106Statement.complete h106 h2 xL xR ρL ρR hD.1
  · exact lp6_left h6 h2 xL ρL xR ρR (hD.1.2.1 0) (hD.2.1 (by decide))

end Base


/-! ### The induction step at `N ≥ 3` groups (LP10's proof) -/

section Step

variable {κ : ℝ}

/-- **The good sectors of LP10 at level `N`**: (LP10.1) by Aux. lemma 113, and the singleton
extension by LP8 in both orientations ("Aux. lemma 113 proves (LP10.1) and LP8 proves the singleton
extension", p. 487). -/
theorem complete_of_goodSector (h113 : Aux113Statement.{u} κ) (h8 : LP8Statement.{u} κ) {N : ℕ}
    (hN : 3 ≤ N) (IH : DistinctCompleteBelow.{u} κ N) (h2 : TwoSeedComplete.{u} κ) {nL nR : ℕ}
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hD : IsDistinctForceWord xL xR) (hc : nL + nR = N) (hL : 0 < nL) (hR : 0 < nR)
    (hs : ((∑ i, ρL i) ≤ -2 ∨ (∑ i, ρR i) ≤ -2 ∨
        (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i)) ∨
      (nR = 1 ∧ -2 < ∑ i, ρR i ∧ κ / 2 - 4 < ∑ i, ρL i) ∨
      (nL = 1 ∧ -2 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i)) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  rcases hs with hs | ⟨rfl, hr, hl⟩ | ⟨rfl, hl, hr⟩
  · exact Aux113Statement.complete h113 hN IH h2 xL xR ρL ρR hD hc hL hR hs
  · rw [Fin.sum_univ_one] at hr
    exact LP8Statement.complete h8 hN IH h2 xL xR ρL ρR hD hc hr hl
  · rw [Fin.sum_univ_one] at hl
    exact lp8_left h8 hN IH h2 xL xR ρL ρR hD hc hl hr

/-- **A low-total right side with at least two groups** (LP10's proof, p. 487: "Reflect to make it
the right side, write its partial sums as `S_i`, and let it contain `n ≥ 2` groups. Thus
`S_n ≤ d`. If `S_2 ≤ d`, retarget its actual second mark. […] If instead `S_2 > d`, let `j ≥ 3` be the
first subsequent index with `S_j ≤ d` […]. In either case the complete transformed theorem has
already been proved at this induction level. LP9 transfers it to the original word"). The transformed
word lies in a good sector whatever the left side is: its left total is `k − 6 − S_j ≥ k − 6 − d =
c > d` by (LP9.1). -/
theorem complete_of_right_low (h113 : Aux113Statement.{u} κ) (h8 : LP8Statement.{u} κ)
    (h9 : LP9Statement.{u} κ) {N : ℕ} (hN : 3 ≤ N) (IH : DistinctCompleteBelow.{u} κ N)
    (h2 : TwoSeedComplete.{u} κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hD : IsDistinctForceWord xL xR) (hc : nL + nR = N)
    (hR : 2 ≤ nR) (hlow : ∑ i, ρR i ≤ κ / 2 - 4) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  classical
  -- the first index `k₀ ≥ 2` with `S_{k₀} ≤ d`
  have hex : ∃ k, 2 ≤ k ∧ partialSum ρR k ≤ κ / 2 - 4 := ⟨nR, hR, by rwa [partialSum_self]⟩
  obtain ⟨k₀, hk₀2, hk₀le, hk₀P, hk₀min⟩ : ∃ k₀, 2 ≤ k₀ ∧ k₀ ≤ nR ∧
      partialSum ρR k₀ ≤ κ / 2 - 4 ∧ ∀ k, 2 ≤ k → k < k₀ → κ / 2 - 4 < partialSum ρR k :=
    ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hR, by rwa [partialSum_self]⟩,
      (Nat.find_spec hex).2, fun k hk hlt => lt_of_not_ge fun hle => Nat.find_min hex hlt ⟨hk, hle⟩⟩
  obtain ⟨j, rfl⟩ : ∃ j, k₀ = j + 1 := ⟨k₀ - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, nR = j + 1 + m := ⟨nR - (j + 1), by omega⟩
  have hj : 1 ≤ j := by omega
  -- the transformed word and its side totals
  have hD' := isDistinctForceWord_retarget hD hj
  have hc' : nL + (m + 1) + j = N := by rw [retarget_card]; exact hc
  have hsL : κ / 2 - 4 < ∑ i, retargetρL κ ρL ρR i := by
    rw [sum_retargetρL, ← partialSum_retarget_succ]; linarith
  have hsR : ∑ i, retargetρR ρR i = partialSum ρR j := by
    rw [sum_retargetρR, partialSum_retarget]
  have hsec : ((∑ i, retargetρL κ ρL ρR i) ≤ -2 ∨ (∑ i, retargetρR ρR i) ≤ -2 ∨
        (κ / 2 - 4 < ∑ i, retargetρL κ ρL ρR i ∧ κ / 2 - 4 < ∑ i, retargetρR ρR i)) ∨
      (j = 1 ∧ -2 < ∑ i, retargetρR ρR i ∧ κ / 2 - 4 < ∑ i, retargetρL κ ρL ρR i) ∨
      (nL + (m + 1) = 1 ∧ -2 < ∑ i, retargetρL κ ρL ρR i ∧ κ / 2 - 4 < ∑ i, retargetρR ρR i) := by
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · -- `S_2 ≤ d`: the transformed right side is the singleton of weight `S_1`
      have hj1 : j = 1 := by omega
      rcases le_or_gt (∑ i, retargetρR ρR i) (-2) with hle | hgt
      · exact Or.inl (Or.inr (Or.inl hle))
      · exact Or.inr (Or.inl ⟨hj1, hgt, hsL⟩)
    · -- `S_2 > d`: both transformed totals exceed `d`
      refine Or.inl (Or.inr (Or.inr ⟨hsL, ?_⟩))
      rw [hsR]; exact hk₀min j hj2 (by omega)
  have hW : IsCompleteForceWord.{u} κ (retargetXL xL xR) (retargetXR xR) (retargetρL κ ρL ρR)
      (retargetρR ρR) :=
    complete_of_goodSector h113 h8 hN IH h2 _ _ _ _ hD' hc' (by omega) (by omega) hsec
  exact @LP9Statement.complete κ h9 N IH nL j m xL xR ρL ρR hD hc hj hW

/-- **Two-sided configurations with `N ≥ 3` groups** (LP10's proof, p. 487: "Consider any remaining
`N`-group configuration with groups on both sides. Both total side weights exceed `−2`, and at least
one total is at most `d`. If such a low-total side is a singleton and the other total exceeds `d`,
the singleton good sector already applies. If both totals are at most `d` and one side is a
singleton, choose the other side, which has at least two groups since `N ≥ 3`. Otherwise choose any
low-total side containing at least two groups."). -/
theorem complete_of_twoSided (h113 : Aux113Statement.{u} κ) (h8 : LP8Statement.{u} κ)
    (h9 : LP9Statement.{u} κ) {N : ℕ} (hN : 3 ≤ N) (IH : DistinctCompleteBelow.{u} κ N)
    (h2 : TwoSeedComplete.{u} κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hD : IsDistinctForceWord xL xR) (hc : nL + nR = N)
    (hL : 0 < nL) (hR : 0 < nR) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  rcases em (((∑ i, ρL i) ≤ -2 ∨ (∑ i, ρR i) ≤ -2 ∨
        (κ / 2 - 4 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i)) ∨
      (nR = 1 ∧ -2 < ∑ i, ρR i ∧ κ / 2 - 4 < ∑ i, ρL i) ∨
      (nL = 1 ∧ -2 < ∑ i, ρL i ∧ κ / 2 - 4 < ∑ i, ρR i)) with hs | hs
  · exact complete_of_goodSector h113 h8 hN IH h2 xL xR ρL ρR hD hc hL hR hs
  rcases em ((∑ i, ρR i) ≤ κ / 2 - 4 ∧ 2 ≤ nR) with hRlow | hRlow
  · exact complete_of_right_low h113 h8 h9 hN IH h2 xL xR ρL ρR hD hc hRlow.2 hRlow.1
  rcases em ((∑ i, ρL i) ≤ κ / 2 - 4 ∧ 2 ≤ nL) with hLlow | hLlow
  · refine complete_of_reflect ?_
    exact complete_of_right_low h113 h8 h9 hN IH h2 (-xR) (-xL) ρR ρL hD.reflect (by omega)
      hLlow.2 hLlow.1
  exfalso
  simp only [not_or, not_and, not_le, not_lt] at hs hRlow hLlow
  obtain ⟨⟨hsL2, hsR2, hdd⟩, hsing1, hsing2⟩ := hs
  rcases le_or_gt (∑ i, ρR i) (κ / 2 - 4) with hRd | hRd
  · have hnR : nR = 1 := by have := hRlow hRd; omega
    have hLd : ∑ i, ρL i ≤ κ / 2 - 4 := hsing1 hnR hsR2
    have hnL : nL = 1 := by have := hLlow hLd; omega
    omega
  · have hLd : ∑ i, ρL i ≤ κ / 2 - 4 := le_of_not_gt fun h => (not_le.2 hRd) (hdd h)
    have hnL : nL = 1 := by have := hLlow hLd; omega
    exact (not_le.2 hRd) (hsing2 hnL hsL2)

/-- **One-sided configurations with `N ≥ 3` groups** (LP10's proof, p. 487: "Finally consider `N`
groups all on one side. Reflect to the right and retarget the second actual mark. The transformed
configuration has a right singleton and a nonempty left list, including the retained old target. It
has at most `N` groups, and belongs to the two-sided `N`-group class just proved; no total-weight
inequality is needed at this stage. Apply LP9 again."). -/
theorem complete_of_oneSided_right (h113 : Aux113Statement.{u} κ) (h8 : LP8Statement.{u} κ)
    (h9 : LP9Statement.{u} κ) {N : ℕ} (hN : 3 ≤ N) (IH : DistinctCompleteBelow.{u} κ N)
    (h2 : TwoSeedComplete.{u} κ) {nR : ℕ} (xL : Fin 0 → ℝ) (xR : Fin nR → ℝ) (ρL : Fin 0 → ℝ)
    (ρR : Fin nR → ℝ) (hD : IsDistinctForceWord xL xR) (hc : 0 + nR = N) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  obtain ⟨m, rfl⟩ : ∃ m, nR = 1 + 1 + m := ⟨nR - 2, by omega⟩
  refine LP9Statement.complete h9 IH xL xR ρL ρR hD hc le_rfl ?_
  exact complete_of_twoSided h113 h8 h9 hN IH h2 _ _ _ _ (isDistinctForceWord_retarget hD le_rfl)
    (by rw [retarget_card]; exact hc) (by omega) (by omega)

/-- **LP10's induction step**: the complete theorem for every word with exactly `N ≥ 3` groups, from
the smaller-count theorem. -/
theorem complete_of_card_eq_of_three_le (h113 : Aux113Statement.{u} κ) (h8 : LP8Statement.{u} κ)
    (h9 : LP9Statement.{u} κ) {N : ℕ} (hN : 3 ≤ N) (IH : DistinctCompleteBelow.{u} κ N)
    (h2 : TwoSeedComplete.{u} κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hD : IsDistinctForceWord xL xR) (hc : nL + nR = N) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  rcases Nat.eq_zero_or_pos nL with rfl | hL
  · exact complete_of_oneSided_right h113 h8 h9 hN IH h2 xL xR ρL ρR hD hc
  rcases Nat.eq_zero_or_pos nR with rfl | hR
  · refine complete_of_reflect ?_
    exact complete_of_oneSided_right h113 h8 h9 hN IH h2 (-xR) (-xL) ρR ρL hD.reflect
      (by omega)
  exact complete_of_twoSided h113 h8 h9 hN IH h2 xL xR ρL ρR hD hc hL hR

end Step


/-! ### The induction and Theorem LP10 -/

section Main

variable {κ : ℝ}

/-- **The induction of Theorem LP10** (pp. 486–487): from the named reductions, every force word with
distinct positions on each side is complete, by strong induction on the number of marks. Bases: zero
groups (ordinary SLE), one group (Aux. lemma 99 with the one-seed theorem), two opposite-side groups
(Aux. lemma 106) and two same-side groups (LP6). Step (`N ≥ 3`): good sectors by Aux. lemma 113 and
LP8; every other configuration by retargeting a low-total side (LP9). -/
theorem distinctCompleteBelow_of_reductions (h0 : ZeroForceStatement.{u} κ)
    (h1 : OneForceStatement.{u} κ) (h106 : Aux106Statement.{u} κ) (h6 : LP6Statement.{u} κ)
    (h113 : Aux113Statement.{u} κ) (h8 : LP8Statement.{u} κ) (h9 : LP9Statement.{u} κ)
    (h2 : TwoSeedComplete.{u} κ) (N : ℕ) : DistinctCompleteBelow.{u} κ N := by
  induction N with
  | zero => intro nL nR xL xR ρL ρR _ h; omega
  | succ N IH =>
    intro nL nR xL xR ρL ρR hD hlt
    rcases Nat.lt_or_ge (nL + nR) N with h | h
    · exact DistinctCompleteBelow.complete IH xL xR ρL ρR hD h
    have hc : nL + nR = N := by omega
    rcases (by omega : N = 0 ∨ N = 1 ∨ N = 2 ∨ 3 ≤ N) with rfl | rfl | rfl | hN
    · exact @complete_of_card_eq_zero κ h0 nL nR xL xR ρL ρR hc
    · exact @complete_of_card_eq_one κ h1 nL nR xL xR ρL ρR hD hc
    · exact @complete_of_card_eq_two κ h106 h6 h2 nL nR xL xR ρL ρR hD hc
    · exact @complete_of_card_eq_of_three_le κ h113 h8 h9 N hN IH h2 nL nR xL xR ρL ρR hD hc

/-- **Theorem LP10 for one parameter, from the named reductions**: if the two-seed word is complete
for every admissible pair, every ordered force word is complete ("Then every integrated
finite-force law has a continuous trace up to and including its finite continuation threshold, and
its trace tends to infinity on infinite lifetime. No restriction on the two side totals or on
intermediate partial sums is needed."). Coincident marks are amalgamated first ("Amalgamate initial
coincident groups on each side", `coincidentMarksTraceStatement`). The combinatorics does not use
`k > 4`: the retargeted left total `k − 6 − S_j ≥ k − 6 − d = c = d + 2` exceeds `d` for every `k`. -/
theorem isCompleteForceWord_of_reductions (h0 : ZeroForceStatement.{u} κ)
    (h1 : OneForceStatement.{u} κ) (h106 : Aux106Statement.{u} κ) (h6 : LP6Statement.{u} κ)
    (h113 : Aux113Statement.{u} κ) (h8 : LP8Statement.{u} κ) (h9 : LP9Statement.{u} κ)
    (h2 : TwoSeedComplete.{u} κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) :
    IsCompleteForceWord.{u} κ xL xR ρL ρR :=
  coincidentMarksTraceStatement κ (fun xL xR ρL ρR hD =>
    DistinctCompleteBelow.complete
      (distinctCompleteBelow_of_reductions h0 h1 h106 h6 h113 h8 h9 h2 _) xL xR ρL ρR hD
      (Nat.lt_succ_self _)) xL xR ρL ρR hF

end Main

/-- **The named input `LP10Statement` of LP11's assembly (`LPAssembly.lean`), from the reductions**:
for every `k > 4`, the zero-force and one-force bases, Aux. lemmas 106 and 113 (§7.3), and LP6, LP8,
LP9 at `k` give Theorem LP10 at `k`. -/
theorem lp10Statement_of_reductions (h0 : ∀ κ : ℝ, 4 < κ → ZeroForceStatement.{u} κ)
    (h1 : ∀ κ : ℝ, 4 < κ → OneForceStatement.{u} κ) (h106 : ∀ κ : ℝ, 4 < κ → Aux106Statement.{u} κ)
    (h6 : ∀ κ : ℝ, 4 < κ → LP6Statement.{u} κ) (h113 : ∀ κ : ℝ, 4 < κ → Aux113Statement.{u} κ)
    (h8 : ∀ κ : ℝ, 4 < κ → LP8Statement.{u} κ) (h9 : ∀ κ : ℝ, 4 < κ → LP9Statement.{u} κ) :
    LP10Statement.{u} := by
  intro κ hκ h2 nL nR xL xR ρL ρR hF
  exact isCompleteForceWord_of_reductions (h0 κ hκ) (h1 κ hκ) (h106 κ hκ) (h6 κ hκ) (h113 κ hκ)
    (h8 κ hκ) (h9 κ hκ) h2 xL xR ρL ρR hF

end InteractingSLE.LP
