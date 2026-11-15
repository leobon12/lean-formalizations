/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.InteractionProbLemma77
import InteractingSLE.Spec.Sec6.Aux39Arc
import InteractingSLE.Foundations.Topology.ThetaCurve
import InteractingSLE.Frozen.Spec.unboundedPart

/-!
# Lemma 7.6 (the first-exit barrier) in pathwise form

Packet PROVE-LEMMA77 (specification §7.2, Lemma 7.6, p. 267, `source/spec/p241-288.md#lem-7.6`).

> Suppose that `h` is a GFF on `ℍ` with piecewise constant boundary data which changes a finite number of times.
> Suppose that `x₁, x₂ ∈ ℝ` with `x₂ < x₁` and fix angles `θ₁ < θ₂ + π`. Let `Tᵢ` be a stopping time for `ηᵢ`
> […]. Let `τ̃₁ ≤ T₁` be a finite stopping time for `η₁`. […] Suppose that `τ̃₂ ≤ T₂` is a finite stopping time […]
> such that […] `η₂(τ̃₂)` is contained in the unbounded connected component of `ℍ \ (η₁([0, τ̃₁]) ∪ η₂([0, ξ₂]))`.
> […] If the revealed prefixes are disjoint, use `ξ₂ = 0` and `ξ₁ = τ̃₁`. Let `D` be the unbounded connected
> component of `ℍ \ (η₁([0, τ̃₁]) ∪ η₂([0, τ̃₂]))`. Then the first exit of the future path from `D`, if it occurs at
> or before `T₂`, cannot occur through the right side of `η₁([0, ξ₁))`. […] The analogous first-exit statement holds
> when the roles of the two paths are swapped.

This file states the disjoint-prefix case of Lemma 7.6, at the deterministic stops `τ̃₁ = r ∧ ζ₁`, `τ̃₂ = t ∧ ζ₂`
(`Tᵢ = ζᵢ`, the available lifetimes, as in `Theorem15Inputs.lean`), as the named input `Lemma76Statement`.

## The right side

The right side of the frozen first prefix is identified as in the specification's own side arguments (Aux. lemma 69,
p. 274, and Aux. lemma 71, p. 277): "Close `C` by a simple arc in the open lower half-plane from `x₂` to `x₁`. This
is a Jordan curve. Its orientation is positive […] the unbounded Jordan component is on the right of `C`." Here the
future path `β` first exits `D` at `β(e) = α(u)`, `u < ξ₁ = τ̃₁`; then `α([0, u]) ∪ β([0, e])` is a simple arc from
`x₁` to `x₂` through the exit point, closed below by `lowerArc x₂ x₁` into a positively oriented Jordan curve `J`. At
`α(u)` the path `β` arrives from the right side of `α` exactly when the onward first path `α((u, ξ₁])` lies on the left
of `J`, i.e. inside `J` (`α v ∈ jordanIn J` for some `v ∈ (u, ξ₁]`). For the reflected half (the roles swapped,
the left side of the second path), the same curve with the labels exchanged is negatively oriented, and arrival
from the left side of `η₂` is again "the onward path inside `J`". This is `IsForbiddenExit`.

The exit point may be a real point of `α([0, ξ₁))` (the specification includes "the original-real-boundary junction
cases", p. 270, with "the stated sides include their incident prime ends"); the future path itself stays in `D ⊆ ℍ`
until the exit, as "first exit from `D`" requires.

## Main definitions

* `truncAt ζ r = ζ ∧ r` as a finite parameter;
* `lowerArcPath`, `lowerArc`: the closing arc in the lower half-plane (a `V` through `(x₁ + x₂)/2 − i`);
* `IsForbiddenExit`, `FirstExitBarrier`: the pathwise conclusion of Lemma 7.6 for disjoint prefixes;
* `Lemma76Statement`: the named input (Lemma 7.6, disjoint prefixes, both halves, at every pair of deterministic
  stops).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Sec7

/-! ### Deterministic stops -/

/-- The stop `ζ ∧ r` as a finite parameter. -/
def truncAt (ζ : ℝ≥0∞) (r : ℝ≥0) : ℝ≥0 := (min ζ (r : ℝ≥0∞)).toNNReal

theorem coe_truncAt (ζ : ℝ≥0∞) (r : ℝ≥0) : (truncAt ζ r : ℝ≥0∞) = min ζ (r : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _))

theorem coe_truncAt_le (ζ : ℝ≥0∞) (r : ℝ≥0) : (truncAt ζ r : ℝ≥0∞) ≤ ζ := by
  rw [coe_truncAt]; exact min_le_left _ _

theorem truncAt_of_le {ζ : ℝ≥0∞} {r : ℝ≥0} (h : (r : ℝ≥0∞) ≤ ζ) : truncAt ζ r = r := by
  have : (truncAt ζ r : ℝ≥0∞) = r := by rw [coe_truncAt, min_eq_right h]
  exact_mod_cast this

/-! ### The lower closing arc -/

/-- The closing path in the lower half-plane: from `x₁` straight down to `(x₁ + x₂)/2 − i`, then up to `x₂`. -/
def lowerArcPath (x₂ x₁ : ℝ) : ℝ → ℂ :=
  Sec6.arcJoin (Sec6.segPath (x₁ : ℂ) ((((x₁ + x₂) / 2 : ℝ) : ℂ) - I))
    (Sec6.segPath ((((x₁ + x₂) / 2 : ℝ) : ℂ) - I) (x₂ : ℂ))

/-- The closing arc `lowerArcPath x₂ x₁ ([0, 1])`. -/
def lowerArc (x₂ x₁ : ℝ) : Set ℂ := lowerArcPath x₂ x₁ '' Icc 0 1

section LowerArc

variable {x₂ x₁ : ℝ}

theorem lowerArcPath_zero : lowerArcPath x₂ x₁ 0 = x₁ := by
  rw [lowerArcPath, Sec6.arcJoin_zero, Sec6.segPath_zero]

theorem lowerArcPath_one : lowerArcPath x₂ x₁ 1 = x₂ := by
  rw [lowerArcPath, Sec6.arcJoin_one, Sec6.segPath_one]

private theorem segPath_re_im (a b : ℂ) (t : ℝ) :
    (Sec6.segPath a b t).re = a.re + t * (b.re - a.re) ∧
      (Sec6.segPath a b t).im = a.im + t * (b.im - a.im) := by
  simp [Sec6.segPath]

theorem image_lowerArcPath :
    lowerArc x₂ x₁ = Sec6.segPath (x₁ : ℂ) ((((x₁ + x₂) / 2 : ℝ) : ℂ) - I) '' Icc 0 1 ∪
      Sec6.segPath ((((x₁ + x₂) / 2 : ℝ) : ℂ) - I) (x₂ : ℂ) '' Icc 0 1 := by
  rw [lowerArc, lowerArcPath, Sec6.image_arcJoin (by rw [Sec6.segPath_one, Sec6.segPath_zero])]

/-- Every point of the closing arc is in the closed lower half-plane, and its real points are the endpoints. -/
theorem im_le_zero_of_mem_lowerArc {z : ℂ} (hz : z ∈ lowerArc x₂ x₁) :
    z.im ≤ 0 ∧ (z.im = 0 → z = x₁ ∨ z = x₂) := by
  rw [image_lowerArcPath] at hz
  rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · obtain ⟨-, him⟩ := segPath_re_im (x₁ : ℂ) ((((x₁ + x₂) / 2 : ℝ) : ℂ) - I) t
    simp only [ofReal_im, sub_im, I_im, zero_sub] at him
    refine ⟨by rw [him]; nlinarith [ht.1], fun h0 => Or.inl ?_⟩
    have ht0 : t = 0 := by rw [him] at h0; linarith
    rw [ht0, Sec6.segPath_zero]
  · obtain ⟨-, him⟩ := segPath_re_im ((((x₁ + x₂) / 2 : ℝ) : ℂ) - I) (x₂ : ℂ) t
    simp only [sub_im, ofReal_im, I_im, zero_sub] at him
    refine ⟨by rw [him]; nlinarith [ht.2], fun h0 => Or.inr ?_⟩
    have ht1 : t = 1 := by rw [him] at h0; linarith
    rw [ht1, Sec6.segPath_one]

theorem notMem_lowerArc_of_mem_H {z : ℂ} (hz : z ∈ H) : z ∉ lowerArc x₂ x₁ := fun h =>
  absurd (im_le_zero_of_mem_lowerArc h).1 (not_le.2 hz)

theorem continuousOn_lowerArcPath : ContinuousOn (lowerArcPath x₂ x₁) (Icc 0 1) :=
  Sec6.continuousOn_arcJoin (Sec6.continuous_segPath _ _).continuousOn
    (Sec6.continuous_segPath _ _).continuousOn (by rw [Sec6.segPath_one, Sec6.segPath_zero])

theorem isCompact_lowerArc : IsCompact (lowerArc x₂ x₁) :=
  isCompact_Icc.image_of_continuousOn continuousOn_lowerArcPath

theorem isPreconnected_lowerArc : IsPreconnected (lowerArc x₂ x₁) :=
  isPreconnected_Icc.image _ continuousOn_lowerArcPath

theorem left_mem_lowerArc : (x₁ : ℂ) ∈ lowerArc x₂ x₁ :=
  ⟨0, ⟨le_rfl, zero_le_one⟩, lowerArcPath_zero⟩

theorem right_mem_lowerArc : (x₂ : ℂ) ∈ lowerArc x₂ x₁ :=
  ⟨1, ⟨zero_le_one, le_rfl⟩, lowerArcPath_one⟩

/-- The closing path is an arc from `x₁` to `x₂`. -/
theorem isArcFrom_lowerArcPath (hx : x₂ < x₁) :
    Foundations.ThetaCurve.IsArcFrom (lowerArcPath x₂ x₁) x₁ x₂ := by
  set m : ℂ := (((x₁ + x₂) / 2 : ℝ) : ℂ) - I with hm
  have hne₁ : (x₁ : ℂ) ≠ m := fun h => by
    have := congrArg Complex.im h; simp [hm] at this
  have hne₂ : m ≠ (x₂ : ℂ) := fun h => by
    have := congrArg Complex.im h; simp [hm] at this
  refine ⟨continuousOn_lowerArcPath, ?_, lowerArcPath_zero, lowerArcPath_one⟩
  refine Sec6.injOn_arcJoin (Sec6.injOn_segPath hne₁) (Sec6.injOn_segPath hne₂)
    (by rw [Sec6.segPath_one, Sec6.segPath_zero]) ?_
  rintro z ⟨⟨t, ht, rfl⟩, ⟨s, hs, hst⟩⟩
  obtain ⟨hre₁, -⟩ := segPath_re_im (x₁ : ℂ) m t
  obtain ⟨hre₂, -⟩ := segPath_re_im m (x₂ : ℂ) s
  have hre := congrArg Complex.re hst
  rw [hre₁, hre₂] at hre
  simp only [hm, ofReal_re, sub_re, I_re, sub_zero] at hre
  have ht1 : t = 1 := by nlinarith [ht.1, ht.2, hs.1, hs.2]
  rw [mem_singleton_iff, ht1]

end LowerArc

/-! ### The forbidden first exit -/

/-- **The forbidden first exit of Lemma 7.6** for disjoint revealed prefixes `α([0, a])`, `β([0, b])`: the future
path `β|(b, e)` runs in the joint unbounded component `D` and first leaves it at `β(e) = α(u)`, `u < a`, arriving
from the right side of `α` (the onward first path `α(v)`, `u < v ≤ a`, lies inside the Jordan curve
`α([0, u]) ∪ β([0, e]) ∪ L`, `L` the lower closing arc). -/
def IsForbiddenExit (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b e u v : ℝ≥0) (L : Set ℂ) : Prop :=
  b < e ∧ u < v ∧ v ≤ a ∧
    (∀ s ∈ Ioo b e, β s ∈ unboundedPart (H \ (α '' Icc 0 a ∪ β '' Icc 0 b))) ∧
    β e = α u ∧ α v ∈ WangWu.jordanIn (α '' Icc 0 u ∪ β '' Icc 0 e ∪ L)

/-- **The pathwise conclusion of Lemma 7.6 for disjoint prefixes**: if the revealed prefixes `α([0, a])`,
`β([0, b])` are disjoint and the second tip `β(b)` is in the unbounded component of `ℍ \ α([0, a])` (the
admissibility hypothesis with `ξ₂ = 0`), the first exit of the future path from the joint unbounded component, at
or before the available lifetime `ζβ`, is not a forbidden exit. -/
def FirstExitBarrier (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (ζβ : ℝ≥0∞) (b : ℝ≥0) (L : Set ℂ) : Prop :=
  Disjoint (α '' Icc 0 a) (β '' Icc 0 b) → β b ∈ unboundedPart (H \ α '' Icc 0 a) →
    ∀ e u v : ℝ≥0, (e : ℝ≥0∞) ≤ ζβ → ¬ IsForbiddenExit α a β b e u v L

/-- **Named input: Lemma 7.6** (§7.2, p. 267), its finite-prefix first-exit assertion for disjoint revealed
prefixes, with `Tᵢ = ζᵢ` and the deterministic stops `τ̃₁ = r ∧ ζ₁`, `τ̃₂ = t ∧ ζ₂`, both halves ("the analogous
first-exit statement holds when the roles of the two paths are swapped"): for `x₂ < x₁`, `θ₁ < θ₂ + π`, the second
path cannot first exit through the right side of the first prefix, and the first path cannot first exit through the
left side of the second prefix. The sides are identified by the lower closing arc as in Aux. lemmas 69 and 71 (see
the module docstring). A §7.2 statement **not proved in Lean**. -/
def Lemma76Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ r t : ℝ≥0, ∀ᵐ ω ∂P,
        FirstExitBarrier (η₁ ω) (truncAt (ζ₁ ω) r) (η₂ ω) (ζ₂ ω) (truncAt (ζ₂ ω) t) (lowerArc x₂ x₁) ∧
          FirstExitBarrier (η₂ ω) (truncAt (ζ₂ ω) t) (η₁ ω) (ζ₁ ω) (truncAt (ζ₁ ω) r) (lowerArc x₂ x₁)

end Sec7

end InteractingSLE
