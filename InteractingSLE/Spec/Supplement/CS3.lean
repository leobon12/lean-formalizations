/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S8Weights
import InteractingSLE.Spec.Supplement.GW2Tip

/-!
# Lemma CS3: exhaustion at weak critical original sums — statement and the exact boundary calculation

Packet PROVE-T14-TIP6. **Lemma CS3** (supplement, `source/spec/p577-624.md` L398–L426, pp. 593–595):

> Let the complete finite-word counterflow have every side partial sum `S ≥ d = k/2 − 4`, with `k > 4` and
> `κ = 16/k < 4`. Let `Θ` be a fixed countable dense subset of `(−π/2, π/2)`. There is a deterministic countable dense
> schedule set `Q` such that the closure of all finite `Θ`-angle prefixes from the original target, with switch times
> in `Q`, is exactly the completed counterflow range.

* `CS3Statement`: the lemma, stated in the vocabulary of the Theorem 1.4 surface (the centred counterflow of `h`, the
  counterflow word `counterflowData κ b` at parameter `16/κ` from `0`, the GW2 histories of the schedules from the
  original target `0`; staged families as in the version-2 anchors, ruling R51).
* **(CS3.1)**, the exact original-boundary partial sums of an angle-`θ` flow beside an original counterflow piece with
  partial sum `S` (`cs3_rL_eq`, `cs3_rR_eq`):
  `r_L(S, θ) = −2 + (κ/4)(S − d) + (π/2 − θ)χ/λ`, `r_R(S, θ) = −2 + (κ/4)(S − d) + (π/2 + θ)χ/λ`.
  They are `> −2` for `θ ∈ (−π/2, π/2)` when `S ≥ d` (`cs3_rL_gt`, `cs3_rR_gt`: "They are strictly greater than `−2` for
  every `θ ∈ Θ`").
* **The extreme stages** (p. 594, "A positive-capacity stage before every bad far collision", and GW2's (GW2.3), p. 622;
  shortcut note (1)): at `θ = π/2` the opposite (right) original sums are `−2 + (κ/4)(S + 2)`, `> −2` as soon as
  `S > −2`, and the left ones are `−2 + (κ/4)(S − d)`, equal to `−2` only at `S = d` (`cs3_rR_half_pi`,
  `cs3_rL_half_pi`, `cs3_rR_half_pi_gt`); the reflected statements at `θ = −π/2` (`cs3_rL_neg_half_pi`,
  `cs3_rR_neg_half_pi`, `cs3_rL_neg_half_pi_gt`).

The proof of CS3's exhaustion is the central-band experiment of GW2 and GB9 (see `GW2Tip.lean`); its remaining inputs
are listed in `planning/handoffs/PROVE-T14-TIP6.md`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Real
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE

namespace Theorem14

namespace CS3

open Sec4 Sec7 Sec7.StripSysField

/-! ### (CS3.1): the exact original-boundary partial sums -/

section Weights

variable {κ : ℝ}

/-- **(CS3.1), left side**: the height `−λ'(1 + S) + πχ` of an original counterflow piece with partial sum `S` gives an
angle-`θ` flow the left partial sum `−2 + (κ/4)(S − d) + (π/2 − θ)χ/λ`, `d = k/2 − 4`, `k = 16/κ`. -/
theorem cs3_rL_eq (hκ : 0 < κ) (S θ : ℝ) :
    cumWeightLeft κ (-sleLambda (16 / κ) * (1 + S) + π * chiC κ + θ * chiC κ) =
      -2 + κ / 4 * (S - (16 / κ / 2 - 4)) + (π / 2 - θ) * chiC κ / sleLambda κ := by
  have hL := sleLambda_ne_zero hκ
  have h := pi_mul_chiC hκ
  have hκ0 : κ ≠ 0 := hκ.ne'
  rw [cumWeightLeft, sleLambda_sixteen_div hκ]
  field_simp
  linear_combination (-12 : ℝ) * h

/-- **(CS3.1), right side**: the height `λ'(1 + S) − πχ` gives an angle-`θ` flow the right partial sum
`−2 + (κ/4)(S − d) + (π/2 + θ)χ/λ`. -/
theorem cs3_rR_eq (hκ : 0 < κ) (S θ : ℝ) :
    cumWeightRight κ (sleLambda (16 / κ) * (1 + S) - π * chiC κ + θ * chiC κ) =
      -2 + κ / 4 * (S - (16 / κ / 2 - 4)) + (π / 2 + θ) * chiC κ / sleLambda κ := by
  have hL := sleLambda_ne_zero hκ
  have h := pi_mul_chiC hκ
  have hκ0 : κ ≠ 0 := hκ.ne'
  rw [cumWeightRight, sleLambda_sixteen_div hκ]
  field_simp
  linear_combination (-12 : ℝ) * h

/-- **CS3: strict interior angles are admissible** (left side): for `S ≥ d` and `θ < π/2`, `r_L(S, θ) > −2`. -/
theorem cs3_rL_gt (hκ : 0 < κ) (hκ4 : κ < 4) {S θ : ℝ} (hS : 16 / κ / 2 - 4 ≤ S) (hθ : θ < π / 2) :
    -2 < cumWeightLeft κ (-sleLambda (16 / κ) * (1 + S) + π * chiC κ + θ * chiC κ) := by
  rw [cs3_rL_eq hκ]
  have h1 : 0 ≤ κ / 4 * (S - (16 / κ / 2 - 4)) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 < (π / 2 - θ) * chiC κ / sleLambda κ :=
    div_pos (mul_pos (by linarith) (chiC_pos hκ hκ4)) (sleLambda_pos hκ)
  linarith

/-- **CS3: strict interior angles are admissible** (right side): for `S ≥ d` and `θ > −π/2`, `r_R(S, θ) > −2`. -/
theorem cs3_rR_gt (hκ : 0 < κ) (hκ4 : κ < 4) {S θ : ℝ} (hS : 16 / κ / 2 - 4 ≤ S) (hθ : -(π / 2) < θ) :
    -2 < cumWeightRight κ (sleLambda (16 / κ) * (1 + S) - π * chiC κ + θ * chiC κ) := by
  rw [cs3_rR_eq hκ]
  have h1 : 0 ≤ κ / 4 * (S - (16 / κ / 2 - 4)) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 < (π / 2 + θ) * chiC κ / sleLambda κ :=
    div_pos (mul_pos (by linarith) (chiC_pos hκ hκ4)) (sleLambda_pos hκ)
  linarith

/-- `κ/4 · d = 2 − κ`. -/
theorem quarter_mul_d (hκ : 0 < κ) : κ / 4 * (16 / κ / 2 - 4) = 2 - κ := by
  have hκ0 : κ ≠ 0 := hκ.ne'
  field_simp
  ring

/-- **The upper extreme, opposite side** ((GW2.3), p. 622; shortcut note (1)): at `θ = π/2` the right original sums are
`−2 + (κ/4)(S + 2)`. -/
theorem cs3_rR_half_pi (hκ : 0 < κ) (S : ℝ) :
    cumWeightRight κ (sleLambda (16 / κ) * (1 + S) - π * chiC κ + π / 2 * chiC κ) = -2 + κ / 4 * (S + 2) := by
  rw [cs3_rR_eq hκ]
  have hM : (π / 2 + π / 2) * chiC κ / sleLambda κ = 2 - κ / 2 := by
    rw [show π / 2 + π / 2 = π by ring]
    exact pi_mul_chiC_div_sleLambda hκ
  rw [hM]
  have e := quarter_mul_d hκ
  linear_combination (-1 : ℝ) * e

/-- **The upper extreme, opposite side, is admissible under only `S > −2`** ((GW2.3)). -/
theorem cs3_rR_half_pi_gt (hκ : 0 < κ) {S : ℝ} (hS : -2 < S) :
    -2 < cumWeightRight κ (sleLambda (16 / κ) * (1 + S) - π * chiC κ + π / 2 * chiC κ) := by
  rw [cs3_rR_half_pi hκ]
  have : 0 < κ / 4 * (S + 2) := mul_pos (by linarith) (by linarith)
  linarith

/-- **The upper extreme, attracting side** (p. 594: "(CS3.1) permits equality `−2` only on the original left side"): at
`θ = π/2` the left original sums are `−2 + (κ/4)(S − d)`. -/
theorem cs3_rL_half_pi (hκ : 0 < κ) (S : ℝ) :
    cumWeightLeft κ (-sleLambda (16 / κ) * (1 + S) + π * chiC κ + π / 2 * chiC κ) =
      -2 + κ / 4 * (S - (16 / κ / 2 - 4)) := by
  rw [cs3_rL_eq hκ]
  simp

/-- **The lower extreme, opposite side** (reflected (GW2.3)): at `θ = −π/2` the left original sums are
`−2 + (κ/4)(S + 2)`. -/
theorem cs3_rL_neg_half_pi (hκ : 0 < κ) (S : ℝ) :
    cumWeightLeft κ (-sleLambda (16 / κ) * (1 + S) + π * chiC κ + -(π / 2) * chiC κ) = -2 + κ / 4 * (S + 2) := by
  rw [cs3_rL_eq hκ]
  have hM : (π / 2 - -(π / 2)) * chiC κ / sleLambda κ = 2 - κ / 2 := by
    rw [show π / 2 - -(π / 2) = π by ring]
    exact pi_mul_chiC_div_sleLambda hκ
  rw [hM]
  have e := quarter_mul_d hκ
  linear_combination (-1 : ℝ) * e

/-- **The lower extreme, opposite side, is admissible under only `S > −2`**. -/
theorem cs3_rL_neg_half_pi_gt (hκ : 0 < κ) {S : ℝ} (hS : -2 < S) :
    -2 < cumWeightLeft κ (-sleLambda (16 / κ) * (1 + S) + π * chiC κ + -(π / 2) * chiC κ) := by
  rw [cs3_rL_neg_half_pi hκ]
  have : 0 < κ / 4 * (S + 2) := mul_pos (by linarith) (by linarith)
  linarith

/-- **The lower extreme, attracting side**: at `θ = −π/2` the right original sums are `−2 + (κ/4)(S − d)`. -/
theorem cs3_rR_neg_half_pi (hκ : 0 < κ) (S : ℝ) :
    cumWeightRight κ (sleLambda (16 / κ) * (1 + S) - π * chiC κ + -(π / 2) * chiC κ) =
      -2 + κ / 4 * (S - (16 / κ / 2 - 4)) := by
  rw [cs3_rR_eq hκ]
  simp

end Weights

/-! ### The statement -/

/-- **Named statement: Lemma CS3** (exhaustion at weak critical original sums, p. 593). For `0 < κ < 4` (`k = 16/κ`),
boundary data `b` whose complete counterflow word (`counterflowData κ b` at parameter `k` from `0`, the word of the
centred counterflow `W'`) has every side partial sum `S ≥ d = k/2 − 4`, and a countable dense `Θ ⊂ (−π/2, π/2)`, there
is a deterministic countable dense `Q ⊂ (0, ∞)` such that, for every staged family (with almost surely continuous
launched pieces, ruling R51), almost surely the closure of the finite `Θ`-angle schedules from the original target `0`
with switch and terminal times in `Q` (each retained through its available portion), with the initial point, is the
completed counterflow range. -/
def CS3Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    (∀ i : Fin (flowLineNL (counterflowData κ b) (counterflowJumps jumps) 0),
      16 / κ / 2 - 4 ≤ ∑ l ∈ Finset.univ.filter (fun l => l ≤ i),
        flowLineRhoL (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0 l) →
    (∀ i : Fin (flowLineNR (counterflowData κ b) (counterflowJumps jumps) 0),
      16 / κ / 2 - 4 ≤ ∑ l ∈ Finset.univ.filter (fun l => l ≤ i),
        flowLineRhoR (16 / κ) (counterflowData κ b) (counterflowJumps jumps) 0 0 l) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(π / 2)) (π / 2) → Θ.Countable → Ioo (-(π / 2)) (π / 2) ⊆ closure Θ →
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ᵐ ω ∂P, closure ((⋃ l ∈ {l | IsSchedule Θ Q l}, ExplState.physSet κ b jumps
            ⟨0, true, scheduleProgram 0 l⟩ (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω)) ∪ {0}) =
          counterflowCompletedRange (fun t => W' t ω)

end CS3

end Theorem14

end InteractingSLE
