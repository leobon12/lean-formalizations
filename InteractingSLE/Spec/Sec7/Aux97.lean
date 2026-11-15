/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsFlowLine
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.ForceWord_ThresholdCondition

/-!
# Aux. lemma 97: localized equal-seed monotonicity (statement)

Packet PROVE-AUX97. Source: Aux. lemma 97 (`source/spec/p289-336.md` L550–L551, p. 326; proof L553–L576, pp. 326–327).

**Aux. lemma 97** (Localized equal-seed monotonicity). "Let `0 < κ < 4`. Suppose that a GFF on `ℍ` has piecewise
constant boundary data, with finitely many changes, and that its boundary values on `(−R, 0)` and `(0, R)` are the
constants `b₋` and `b₊`, respectively. Let `θ₁ < θ₂` be angles for which neither flow line from `0` is at an immediate
continuation threshold. Fix `0 < r < R`, and stop each path on first leaving `B̄(0, r)` or at an earlier terminal time.
The angle-`θ₁` path lies to the right of the angle-`θ₂` path up to these stopping times. The conclusion is a statement
about these stopped ranges; it does not assert a global ordering after either path leaves the ball."

* `ballExit r γ = inf {t | r < ‖γ t‖}` (`⊤` if `γ` never leaves `B̄(0, r)`): "first leaving `B̄(0, r)`";
  `le_ballExit_iff` (a prefix `γ[0, a]` stays in `B̄(0, r)` before `a`), `ballExit_pos` (a path continuous at its seed
  `0` leaves the ball only after a positive time);
* **`Aux97Statement`** (named input; exact statement on the frozen carriers). "Immediate continuation threshold" is
  the frozen continuation-threshold condition (`ForceWord.ThresholdCondition`: a seed group of weight `≤ −2`) at the
  initial state of the flow-line force word. "Lies to the right up to these stopping times" is the W0 convention of the
  frozen Theorem 1.5: every pair of finite prefixes within the stopped ranges has ordered proper completions with the
  angle-`θ₂` path on the closed left side. As in the frozen Theorem 1.5 and Theorem W5, the prefixes are taken strictly
  before the lifetimes (a finite terminal endpoint inside the ball is not included); this is the form W5 consumes.

**Not proved here.** Only the final step of its proof (Proposition 7.4's reference ordering transferred by one common
Cameron–Martin density and Lemma G1) is in Lean, abstractly: `Sec7/Aux97Transfer.lean`. Its consumer, W5's
common-seed comparison, is `Supplement/W5CommonSeed.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-- **The first exit time from the closed ball `B̄(0, r)`**: `inf {t | r < ‖γ t‖}`, and `⊤` if the path never
leaves the ball. -/
def ballExit (r : ℝ) (γ : ℝ≥0 → ℂ) : ℝ≥0∞ := ⨅ (t : ℝ≥0) (_ : r < ‖γ t‖), (t : ℝ≥0∞)

/-- A time is at most the exit time iff the path stays in `B̄(0, r)` strictly before it. -/
theorem le_ballExit_iff {r : ℝ} {γ : ℝ≥0 → ℂ} {a : ℝ≥0∞} :
    a ≤ ballExit r γ ↔ ∀ t : ℝ≥0, (t : ℝ≥0∞) < a → ‖γ t‖ ≤ r := by
  unfold ballExit
  simp only [le_iInf_iff]
  constructor
  · intro h t ht
    by_contra hr
    exact absurd (h t (not_le.1 hr)) (not_le.2 ht)
  · intro h t hr
    by_contra hlt
    exact absurd (h t (not_le.1 hlt)) (not_le.2 hr)

/-- **The exit time is positive** for a path that starts at `0` and is continuous at time `0` within a set that is a
neighbourhood of `0` (e.g. `{t | t ≤ T}` with `0 < T`). -/
theorem ballExit_pos {r : ℝ} (hr : 0 < r) {γ : ℝ≥0 → ℂ} (h0 : γ 0 = 0) {T : ℝ≥0∞} (hT : 0 < T)
    (hc : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ T}) : 0 < ballExit r γ := by
  have hnhds : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ T} ∈ 𝓝 (0 : ℝ≥0) := by
    obtain ⟨δ, hδ0, hδT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hT
    refine Filter.mem_of_superset (Iio_mem_nhds (show (0 : ℝ≥0) < δ from ENNReal.coe_pos.1 hδ0)) ?_
    intro t ht
    exact le_of_lt (lt_trans (ENNReal.coe_lt_coe.2 ht) hδT)
  have hca : ContinuousAt γ 0 := hc.continuousAt hnhds
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ‖γ t‖ < r :=
    hca.norm.eventually (gt_mem_nhds (show ‖γ 0‖ < r by rw [h0, norm_zero]; exact hr))
  obtain ⟨δ, hδ0, hδ⟩ := exists_Ico_subset_of_mem_nhds hev ⟨1, one_pos⟩
  refine lt_of_lt_of_le (ENNReal.coe_pos.2 hδ0) (le_ballExit_iff.2 fun t ht => ?_)
  exact le_of_lt (hδ ⟨zero_le, ENNReal.coe_lt_coe.1 ht⟩)

/-- **Named input: Aux. lemma 97** (localized equal-seed monotonicity, p. 326), on the frozen carriers. For
`0 < κ < 4`, piecewise-constant data `b` that equals `b₋` on `(−R, 0)` and `b₊` on `(0, R)`, angles `θ₁ < θ₂` whose
flow lines from `0` are not at an immediate continuation threshold, and `0 < r < R`: almost surely, every pair of
finite prefixes `η₁[0, a]`, `η₂[0, c]` within the paths stopped on first leaving `B̄(0, r)` (and strictly before the
lifetimes) has ordered proper completions with `η₂` on the closed left side of `η₁`. -/
def Aux97Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ R bm bp : ℝ, 0 < R → (∀ y ∈ Ioo (-R) 0, b y = bm) → (∀ y ∈ Ioo 0 R, b y = bp) →
    ∀ θ₁ θ₂ : ℝ, θ₁ < θ₂ →
      ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ₁) (flowLineRhoR κ b jumps 0 θ₁) 0
        (flowLineXL b jumps 0) (flowLineXR b jumps 0) →
      ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b jumps 0 θ₂) (flowLineRhoR κ b jumps 0 θ₂) 0
        (flowLineXL b jumps 0) (flowLineXR b jumps 0) →
    ∀ r : ℝ, 0 < r → r < R →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps 0 θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps 0 θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) ≤ ballExit r (η₁ ω) → (a : ℝ≥0∞) < ζ₁ ω →
        (c : ℝ≥0∞) ≤ ballExit r (η₂ ω) → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c

end Sec7

end InteractingSLE
