/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdDetLineFacts
import InteractingSLE.Spec.Supplement.RLCCondDetHist

/-!
# Leaf 3 (`RLC.RetOrdDetStatement`): the split by continuation and the later-line facts with the outer word

Packet PROVE-T15-ORDDET. Two pieces of structure for Theorem 1.5's leaf 3, (Det) for both continuations at an ordinary
retained pair (Lemma G7's conclusion, supplement pp. 497–498):

* **the split by continuation**: `RetOrdDetSndStatement` (the second continuation, seed `0`) and
  `RetOrdDetFstStatement` (the first continuation, seed `tipPos`), each with exactly the binders of
  `RetOrdDetStatement` minus the other code; **`retOrdDetStatement_of_fst_snd`**;
* **the later-line facts with the outer word**: at a later line of the second continuation, the slit heights of the
  later word (`OrdDet.ae_retLine_facts_of_meanIdent`'s pathwise input) follow from the outer word `IsRetainedWord` at
  the later pair (`slitHeights_of_sides`) once the chart images of the two sides of the new piece are known to be
  interior points of the second path off the first prefix and off the later tip. That planar Loewner fact is the named
  input **`OrdSlitSideStatement`** (deterministic). With it, **`ae_retLine_facts_of_retainedWord`** gives (III-a) and
  (III-b) at the line for every pair of mean-identified words with the outer word at the later line — the `hline` input
  of `RetAux79.hasSafeLaw_of_retLines` for the touching pairs and through real contacts.

For Theorem 1.5; uses Lemma 7.5 only (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart LQGMetric Sec7.Lemma76F

/-! ### The split by continuation -/

/-- **(Det) for the second continuation at an ordinary retained pair**: `RetOrdDetStatement` with the first code and
the first continuation's conclusion dropped. **Not proved in Lean.** -/
def RetOrdDetSndStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₂ F₂ →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≤
          (F₂ (((β ω).1, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s =
            decPath (F₂ (((β ω).1, 0), hd.chartField κ h ω)) s

/-- **(Det) for the first continuation at an ordinary retained pair**: `RetOrdDetStatement` with the second code and
the second continuation's conclusion dropped. **Not proved in Lean.** -/
def RetOrdDetFstStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ F₁ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₁ F₁ →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (tipPos d η₁ ω) ≤
          (F₁ (β ω, hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
              (tipPos d η₁ ω) →
          canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
              (tipPos d η₁ ω) s =
            decPath (F₁ (β ω, hd.chartField κ h ω)) s

/-- **Leaf 3 from its two continuations.** -/
theorem retOrdDetStatement_of_fst_snd (hF : RetOrdDetFstStatement.{u}) (hS : RetOrdDetSndStatement.{u}) :
    RetOrdDetStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₁ F₂ hF₁ hF₂ u₀ hu₀
    β hβ hmean hword
  have h1 := hF κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₁ hF₁ u₀ hu₀ β hβ hmean
    hword
  have h2 := hS κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂ u₀ hu₀ β hβ hmean
    hword
  filter_upwards [h1, h2] with ω h1 h2 hord
  obtain ⟨l₁, p₁⟩ := h1 hord
  obtain ⟨l₂, p₂⟩ := h2 hord
  exact ⟨l₁, p₁, l₂, p₂⟩

/-! ### The slit heights from the outer word -/

namespace OrdDet

open MartChar.RealFlow

/-- **The slit heights from the outer word**: if every chart point off a finite set on the two slit images `(ℓ, 0)`,
`(0, ϱ)` is sent by the chart inverse to an interior point of the second prefix, off the first prefix and off the second
tip, then a word with the outer word `IsRetainedWord` has the canonical new-side heights there. -/
theorem slitHeights_of_sides {κ θ₁ θ₂ : ℝ} {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {c : BoundaryWord}
    (hw : IsRetainedWord κ θ₁ θ₂ α a β b ψ c) {ℓ ϱ : ℝ} {S' : Set ℝ}
    (hside : ∀ y ∉ S', (ℓ < y ∧ y < 0) ∨ (0 < y ∧ y < ϱ) →
      ψ y ∈ H ∧ ψ y ∈ β '' Icc 0 b ∧ ψ y ≠ β b ∧ ψ y ∉ α '' Icc 0 a) :
    (∀ y ∉ S', ℓ < y → y < 0 → c.fn y = -sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
      (∀ y ∉ S', 0 < y → y < ϱ → c.fn y = sleLambda κ - θ₂ * QuantumZipper.chiC κ) := by
  have key : ∀ y ∉ S', (ℓ < y ∧ y < 0) ∨ (0 < y ∧ y < ϱ) →
      (y < 0 → c.fn y = -sleLambda κ - θ₂ * QuantumZipper.chiC κ) ∧
        (0 < y → c.fn y = sleLambda κ - θ₂ * QuantumZipper.chiC κ) := by
    intro y hy hint
    obtain ⟨hH, hβ, htip, hα⟩ := hside y hy hint
    have hα' : ψ y ≠ α a := fun e => hα (e ▸ ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩)
    exact ((hw y hH htip hα' fun h => hα h.1).2.2.1 hβ)
  exact ⟨fun y hy h1 h2 => (key y hy (Or.inl ⟨h1, h2⟩)).1 h2,
    fun y hy h1 h2 => (key y hy (Or.inr ⟨h1, h2⟩)).2 h1⟩

/-- **Named input: the slit sides of a later line** (deterministic planar Loewner geometry; supplement p. 497, G7's
proof: "the relative trace never continues in a newly filled relative pocket", and the boundary of the relative hull
in `ℍ` lies on the relative trace). Two retained data `d` (cutoffs `(u, r)`) and `d'` (cutoffs `(u, r + t)`) of the same
paths, a sample of both chart events at which the later pair is an ordinary retained pair and the continuation
`η₂((r, r + t])` has no new contact with the retained union, and a chart path `γ` of the
continuation in the stop-line chart (generated by a continuous driver `W`, injective, `0 < Q <` its lifetime, tracing
`η₂([r, r + t])` and ending at the later tip). Then off a finite set, every point `y` of the two slit images
`(V̂^{0,L}_Q, 0)` and `(0, V̂^{0,R}_Q)` is sent by the later chart inverse to an interior point of the second prefix,
off the first prefix and off the later tip. **Not proved in Lean.** -/
def OrdSlitSideStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] {d d' : RetData Ω}, d.IsMeasGood → d'.IsMeasGood → d'.η₁ = d.η₁ →
    d'.η₂ = d.η₂ → d'.u = d.u → ∀ {t : ℝ≥0}, d'.r = d.r + t → ∀ {ω : Ω}, ω ∈ d.E → ω ∈ d'.E →
    ∀ {ζ₁ ζ₂ : ℝ≥0∞}, IsOrdinaryRetainedPair (d.η₁ ω) ζ₁ d.u (d.η₂ ω) ζ₂ (d.r + t) →
    (∀ t' : ℝ≥0, d.r < t' → t' ≤ d.r + t → d.η₂ ω t' ∉ d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) →
    ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W → W 0 = 0 →
      InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
      (fun s => d.inv ω (γ s)) '' Icc 0 Q = d.η₂ ω '' Icc d.r (d.r + t) →
      d.inv ω (γ Q) = d.η₂ ω (d.r + t) →
      ∃ S' : Set ℝ, S'.Finite ∧ ∀ y ∉ S',
        (-rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q < y ∧ y < 0) ∨
          (0 < y ∧ y < rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q) →
        d'.inv ω y ∈ H ∧ d'.inv ω y ∈ d.η₂ ω '' Icc 0 (d.r + t) ∧ d'.inv ω y ≠ d.η₂ ω (d.r + t) ∧
          d'.inv ω y ∉ d.η₁ ω '' Icc 0 d.u

open Restart.RetAux79 in
/-- **The later-line facts with the outer word** (the `hline` facts (III-a) and (III-b) of
`RetAux79.hasSafeLaw_of_retLines` at one line, for the touching pairs and through real contacts): as
`ae_retLine_facts_of_meanIdent`, with the slit heights supplied by `OrdSlitSideStatement` and the outer word
`IsRetainedWord` of the later word at the later pair (angle `θ₂` of the second path). -/
theorem ae_retLine_facts_of_retainedWord (hslit : OrdSlitSideStatement.{u}) {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {d d' : RetData Ω} (hd : d.IsMeasGood) (hd' : d'.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hag' : ∀ᵐ ω ∂P, (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d'.G ∧
      (∀ s ≤ d'.u, d'.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d'.r, d'.η₂ ω t = η₂ ω t)
    (h₁ : d'.η₁ = d.η₁) (h₂ : d'.η₂ = d.η₂) (hu : d'.u = d.u) {t : ℝ≥0} (hr : d'.r = d.r + t)
    {O₀ O₁ : Set Ω} {β₀ β₁ : Ω → BoundaryWord}
    (hm₀ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O₀ β₀)
    (hm₁ : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd' O₁ β₁) :
    ∀ᵐ ω ∂P, ω ∈ O₀ → ω ∈ O₁ → (d'.u : ℝ≥0∞) < ζ₁ ω → (d'.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.E → ω ∈ d'.E →
      (β₀ ω).IsSorted → (β₁ ω).IsSorted →
      IsOrdinaryRetainedPair (d.η₁ ω) (ζ₁ ω) d.u (d.η₂ ω) (ζ₂ ω) (d.r + t) →
      (∀ t' : ℝ≥0, d.r < t' → t' ≤ d.r + t → d.η₂ ω t' ∉ d.η₁ ω '' Icc 0 d.u ∪ d.η₂ ω '' Icc 0 d.r) →
      IsRetainedWord κ θ₁ θ₂ (d.η₁ ω) d.u (d.η₂ ω) (d.r + t) (d'.inv ω) (β₁ ω) →
      ∀ (W : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (ζc : ℝ≥0∞) (Q : ℝ≥0), IsGeneratingTrace W ζc γ → Continuous W →
        W 0 = 0 → InjOn γ {s | (s : ℝ≥0∞) ≤ ζc} → (Q : ℝ≥0∞) < ζc → 0 < Q →
        (fun s => d.inv ω (γ s)) '' Icc 0 Q = d.η₂ ω '' Icc d.r (d.r + t) →
        d.inv ω (γ Q) = d.η₂ ω (d.r + t) →
        (∀ w ∈ H, (d'.chart ω).2.1 w = (d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)) ∧
        (∀ w ∈ H, (d'.chart ω).2.2 ((d'.chart ω).2.1 w) =
          (logDerivFwd (fun s : ℝ => W s.toNNReal) Q (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w)).im +
            (d.chart ω).2.2 ((d.chart ω).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) Q w))) ∧
        ∃ S : Set ℝ, S.Finite ∧ ∀ y ∉ S,
          forceBoundaryData κ (flowLineRhoL κ (β₀ ω).fn (β₀ ω).jumps 0 θ₂)
              (flowLineRhoR κ (β₀ ω).fn (β₀ ω).jumps 0 θ₂)
              (fun i => -rightImg (fun s : ℝ => -W s.toNNReal) (-flowLineXL (β₀ ω).fn (β₀ ω).jumps 0 i) Q - W Q)
              (fun j => rightImg (fun s : ℝ => W s.toNNReal) (flowLineXR (β₀ ω).fn (β₀ ω).jumps 0 j) Q - W Q) y =
            (β₁ ω).fn y + θ₂ * QuantumZipper.chiC κ := by
  have hl := ae_retLine_facts_of_meanIdent hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ hd hd' hag hag' h₁ h₂ hu hr hm₀ hm₁ θ₂
  filter_upwards [hl] with ω hlω
  intro hO₀ hO₁ hu₁ hr₁ hE hE' hs₀ hs₁ hord hnc hrw W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  obtain ⟨S', hS', hside⟩ := hslit hd hd' h₁ h₂ hu hr hE hE' hord hnc W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip
  obtain ⟨hL, hR⟩ := slitHeights_of_sides hrw (S' := S') (ℓ := -rightImg (fun s : ℝ => -W s.toNNReal) 0 Q - W Q)
    (ϱ := rightImg (fun s : ℝ => W s.toNNReal) 0 Q - W Q) hside
  exact hlω hO₀ hO₁ hu₁ hr₁ hE hE' hs₀ hs₁ W γ ζc Q hg hWc hW0 hinj hQ hQ0 himg htip ⟨S', hS', hL, hR⟩

end OrdDet

end RLC

end InteractingSLE
