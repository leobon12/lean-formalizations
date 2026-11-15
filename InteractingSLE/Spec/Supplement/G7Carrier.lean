/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem15D5Inputs

/-!
# Lemma G7 at the retained pair of Theorem 7.12D: the carrier, and the collar's joint activity

Packet PROVE-G7GB7A (Theorem 1.5's interface 4 of the follow-up note, D.5: "G7's actual stopped precontact kernel";
interface 5: "the rational-cut collar construction in 7.12D, which places a proposed interior contact on an exposed
old side in a genuine retained stopping-pair chart"). Sources: specification supplement §7.6, Lemma G7 (pp. 497–498,
`source/spec/p481-528.md`), and the proof of Theorem 7.12D (pp. 543–544, `source/spec/p529-576.md`).

The landed interface `Theorem15D5.G7GB7aFirstHitStatement` packs three steps of the 7.12D proof into one almost-sure
proposition. This file states the two of them that are not GB7a (`Supp8.GB7aFlowStatement`) separately, each on an
event of positive probability (so that neither is implied vacuously by the conclusion it serves):

* **G7 with the outer word, as a kernel carrier** (`G7RetainedPairStatement`), in the form of the first-contact
  restart carrier `Restart.FirstContactRestartStatement`: for every pair of own cutoffs `(u, r)` there are a
  canonical space `S` (chart field `H`, chart path `Γ`, its relative lifetime `U`), a measurable event `M`, the chart
  datum `β` and the restart variable `X`, and a Markov kernel `K` which is the conditional law of `X` given `β` on `M`,
  such that
  - for almost every datum `c`, under `K c` the chart field is a GFF with datum `c` and `Γ` is its angle-`θ₂` flow
    line from `0` (G7: "it is the canonical stopped flow of the conditional field");
  - almost surely, at an ordinary retained pair (`IsOrdinaryRetainedPair`: both tips interior, each off the other
    prefix, jointly active, W0's ordered completion at `(u, r)`), `ω ∈ M` and the pathwise relation
    `IsRetainedContinuation` holds: a common active chart `φ` of the joint unbounded component `D` at the second tip,
    its inverse `ψ`, the chart field of `h` (frozen `IsChartTransport`), an increasing clock `c₂` that maps the chart
    times `[0, σ]`, `σ ≤ U`, onto the physical continuation of the second path up to and including its first new
    contact with the retained union `A = η₁([0, u]) ∪ η₂([0, r])`, with `η₂ ∘ c₂ = ψ ∘ Γ` there (G7: "stop on its first
    new contact with the retained curve range A […] with its original stopping rule recovered in relative
    capacity"); and the **outer word** (Aux. lemmas 85–86, p. 543: "the outer-word argument of Aux. 85–86 gives the full
    canonical initial finite word"): every chart boundary point `y` whose inverse-chart image is an interior point of
    an exposed old curve side (not a tip, not an old common point) is off the jumps of the datum and has outward
    cumulative weight at least `c = κ/2 − 2` for the angle-`θ₂` path. The weights are `0` on the two sides of the
    second path (its canonical seed germs), `D − 2` on the exposed left side of the first path ((7.12D.1), the
    hypothesis below), and `D` on its exposed right side, where `D = (θ₂ − θ₁)χ/λ ≥ κ/2`.
* **The collar's joint activity** (`CollarActivityStatement`, deterministic; interface 5): at an interior first new
  hit of the retained first prefix after `r`, under W0's ordered completions and the strict contact order, every pair
  of cutoffs `u'` just after the hit parameter and `r'` just before the hit time has both tips active in the joint
  unbounded component (7.12D proof: "both incident collars are therefore in the own unbounded component […] The first
  tip `α(u)` is outside the individual filled hull of `β([0, r])` […] The second tip is outside the individual first
  hull by the choice of its active left collar. W5 gives ordered completion at `(u, r)`, so Aux. lemma 90 gives
  joint activity").

Neither proposition is proved in Lean. The reduction of `G7GB7aFirstHitStatement` to them and GB7a is
`G7FirstHit.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp7

open Restart Theorem15D5

/-- **An ordinary retained pair** at own cutoffs `u` (first path) and `r` (second path) (proof of Theorem 7.12D,
p. 543; Lemma G7, p. 497: "one current tip `p` is an interior physical point, is disjoint from the other retained
prefix, and is active"): both cutoffs are strictly available, both tips are interior, each tip is off the other
prefix, both tips lie on the boundary of the joint unbounded component (joint activity, Aux. lemma 90), and the
prefixes have W0's ordered proper completions. -/
def IsOrdinaryRetainedPair (η₁ : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (u : ℝ≥0) (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (r : ℝ≥0) :
    Prop :=
  (u : ℝ≥0∞) < ζ₁ ∧ (r : ℝ≥0∞) < ζ₂ ∧ η₁ u ∈ QuantumZipper.H ∧ η₂ r ∈ QuantumZipper.H ∧
    η₂ r ∉ η₁ '' Icc 0 u ∧ η₁ u ∉ η₂ '' Icc 0 r ∧
    η₁ u ∈ closure (activeDomain η₁ u η₂ r) ∧ η₂ r ∈ closure (activeDomain η₁ u η₂ r) ∧
    HasOrderedProperCompletions η₁ u η₂ r

/-- **The pathwise part of G7 at a retained pair, with the outer word** (Lemma G7, pp. 497–498; proof of Theorem
7.12D, p. 543). With `D = activeDomain η₁ u η₂ r` and `A = η₁([0, u]) ∪ η₂([0, r])`:
* `φ` is a common active chart of `D` at the second tip, `ψ` its inverse on `ℍ` (values off `ℍ` lie off `D`), `H` is
  the field `h` in the chart (frozen `IsChartTransport`, `σ = 1`, `a = 0`, `k = χ`) for a continuous branch `lift` of
  `arg φ′`;
* the clock `c₂` is strictly increasing on the chart times `[0, σ]`, `σ ≤ U`, and maps them onto the physical times
  `t ≥ r`, `t ≤ ζ₂`, with no new contact with `A` strictly between `r` and `t` (the continuation up to and including
  its first new contact with `A`), and `η₂ ∘ c₂ = ψ ∘ Γ` there;
* (outer word) every real `y` with `ψ y` an interior point of `A`'s exposed sides other than the two tips and the old
  common points is not `0`, is not a jump of the datum `c`, and has outward cumulative weight at least `κ/2 − 2` for
  the angle-`θ₂` path (right of `0`: `cumWeightRight κ (c y + θ₂χ)`; left of `0`: `cumWeightLeft κ (c y + θ₂χ)`). -/
def IsRetainedContinuation (κ θ₂ : ℝ) (h H : LQGMetric.DistOn upperHalfPlaneOpens) (η₁ : ℝ≥0 → ℂ) (u : ℝ≥0)
    (η₂ : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (r : ℝ≥0) (c : BoundaryWord) (Γ : ℝ≥0 → ℂ) (U : ℝ≥0∞) : Prop :=
  ∃ (φ ψ : ℂ → ℂ) (lift : ℂ → ℝ) (c₂ : ℝ≥0 → ℝ≥0) (σ : ℝ≥0∞),
    IsActiveChart (activeDomain η₁ u η₂ r) (η₂ r) φ ∧
    BijOn ψ QuantumZipper.H (activeDomain η₁ u η₂ r) ∧ (∀ w ∈ QuantumZipper.H, φ (ψ w) = w) ∧
    (∀ w ∉ QuantumZipper.H, ψ w ∉ activeDomain η₁ u η₂ r) ∧
    ContinuousOn lift (activeDomain η₁ u η₂ r) ∧
    (∀ z ∈ activeDomain η₁ u η₂ r,
      deriv φ z = (‖deriv φ z‖ : ℂ) * Complex.exp (Complex.I * (lift z : ℂ))) ∧
    IsChartTransport (φ, ψ, lift) 1 0 (QuantumZipper.chiC κ) h H ∧
    σ ≤ U ∧ StrictMonoOn c₂ {s | (s : ℝ≥0∞) ≤ σ} ∧
    c₂ '' {s | (s : ℝ≥0∞) ≤ σ} =
      {t | r ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂ ∧ ∀ t' : ℝ≥0, r < t' → t' < t → η₂ t' ∉ η₁ '' Icc 0 u ∪ η₂ '' Icc 0 r} ∧
    (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ σ → η₂ (c₂ s) = ψ (Γ s)) ∧
    ∀ y : ℝ, ψ y ∈ QuantumZipper.H → ψ y ≠ η₂ r → ψ y ≠ η₁ u → ψ y ∉ η₁ '' Icc 0 u ∩ η₂ '' Icc 0 r →
      y ≠ 0 ∧ y ∉ c.jumps ∧
        (0 < y → κ / 2 - 2 ≤ Sec4.cumWeightRight κ (c.fn y + θ₂ * QuantumZipper.chiC κ)) ∧
        (y < 0 → κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (c.fn y + θ₂ * QuantumZipper.chiC κ))

/-- **Named input: Lemma G7 at the retained pair of Theorem 7.12D, as a kernel carrier, with the outer word**
(specification supplement §7.6, Lemma G7, pp. 497–498; proof of Theorem 7.12D, p. 543: "At this ordinary retained
pair the outer-word argument of Aux. 85–86 gives the full canonical initial finite word […] Stop the actual second
future at its first new contact with the retained old union […] G7 identifies this entire conditional stopped
field–path law with the canonical finite-word flow"). Setting of `Theorem15D5.G7GB7aFirstHitStatement`: `η₁` the
angle-`θ₁` flow line from `x₁`, `η₂` the angle-`θ₂` flow line from `x₂ ≤ x₁`, with GB7a's weight hypothesis on the
exposed first left side ((7.12D.1)). For all own cutoffs `(u, r)`: a canonical space `S : Type` with measurable
coordinates (chart field `H`, chart path `Γ` continuous on its closed available interval, relative lifetime `U`), a
measurable event `M`, a measurable datum `β`, a measurable restart variable `X` and a Markov kernel `K` with
* `K` the conditional law of `X` given `β` on `M`;
* for almost every datum `c`, under `K c`: `H` is a GFF with datum `c`, and `Γ` (lifetime `U`) its angle-`θ₂` flow
  line from `0`;
* almost surely, at an ordinary retained pair `(u, r)`: `ω ∈ M` and `IsRetainedContinuation` for `X ω`, `β ω`.

**Not proved in Lean.** -/
def G7RetainedPairStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ →
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0,
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ : S → ℝ≥0 → ℂ)
      (U : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord) (X : Ω → S) (K : Kernel BoundaryWord S),
      Measurable H ∧ Measurable U ∧ (∀ t : ℝ≥0, Measurable fun s => Γ s t) ∧
      (∀ s, ContinuousOn (Γ s) {t | (t : ℝ≥0∞) ≤ U s}) ∧
      MeasurableSet M ∧ Measurable β ∧ Measurable X ∧ IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β,
        IsGFFWithBoundaryData (K c) H c.fn c.jumps ∧ IsFlowLine κ c.fn c.jumps 0 θ₂ (K c) H Γ U) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        ω ∈ M ∧ IsRetainedContinuation κ θ₂ (h ω) (H (X ω)) (η₁ ω) u (η₂ ω) (ζ₂ ω) r (β ω) (Γ (X ω)) (U (X ω))

/-- **Named input: joint activity in the rational-cut collar of Theorem 7.12D** (deterministic; D.5 interface 5;
proof of Theorem 7.12D, p. 543, with Aux. lemma 90). Let two paths have W0's ordered proper completions for all
strictly available prefixes and increasing strict contacts, and let the second path, after an own time `r` with
`η₂(r)` off `η₁([0, u])`, make its first new contact with `η₁([0, u])` at time `t` at an interior point `η₁(x)`,
`x < u`. Then there is `δ > 0` such that for every first cutoff `u' ∈ (x, x + δ)`, `u' ≤ u`, and second cutoff
`r' ∈ (t − δ, t)`, `r' > r`, both tips `η₁(u')`, `η₂(r')` lie on the boundary of the joint unbounded component of
`ℍ \ (η₁([0, u']) ∪ η₂([0, r']))`. **Not proved in Lean** (planar topology: the collars of the arc near the hit are
in each path's own unbounded component, and Aux. lemma 90). -/
def CollarActivityStatement : Prop :=
  ∀ (η₁ η₂ : ℝ≥0 → ℂ) (ζ₁ ζ₂ : ℝ≥0∞),
    (∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → (c : ℝ≥0∞) < ζ₂ → HasOrderedProperCompletions η₁ a η₂ c) →
    StrictContactsIncreasing η₁ ζ₁ η₂ ζ₂ →
    ∀ u r t x : ℝ≥0, (u : ℝ≥0∞) < ζ₁ → r < t → (t : ℝ≥0∞) < ζ₂ → x < u → η₂ t = η₁ x →
      η₁ x ∈ QuantumZipper.H → η₂ r ∉ η₁ '' Icc 0 u →
      (∀ t' : ℝ≥0, r < t' → t' < t → η₂ t' ∉ η₁ '' Icc 0 u) →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ u' r' : ℝ≥0, x < u' → u' < x + δ → u' ≤ u → r < r' → t < r' + δ → r' < t →
        η₁ u' ∈ closure (activeDomain η₁ u' η₂ r') ∧ η₂ r' ∈ closure (activeDomain η₁ u' η₂ r')

end Supp7

end InteractingSLE
