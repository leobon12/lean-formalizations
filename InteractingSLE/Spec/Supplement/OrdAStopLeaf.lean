/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdAStopModel
import InteractingSLE.Spec.Supplement.OrdDetWire
import InteractingSLE.Spec.Exist.StagedLawData
import InteractingSLE.Spec.Exist.FlowField

/-!
# Leaf 3 from A-stopped models

Packet PROVE-T15-ASTOP. Theorem 1.5's leaf 3 (`RLC.RetOrdDetStatement`, split by PROVE-T15-ORDDET into
`RetOrdDetSndStatement` and `RetOrdDetFstStatement`) is (Det) for each continuation of an ordinary retained pair,
stopped at its first new contact with the retained union `A = η₁[0,u] ∪ η₂[0,r]` **only** (Lemma G7, supplement
p. 497; real contacts allowed). This file reduces it to the construction of stopped models whose announcing stops may
read an initial code (`OrdAStop.StoppedModelTransferJ`; the A-stop is announced by a process reading the chart image of
`A`, which is not a force coordinate in general):

* `RetOrdStoppedModelsSndStatement`: finitely many type events covering the ordinary pairs, each with an A-stopped
  model of the second continuation (word `β.1`, the retained chart field, the canonical retained clock with stop set
  `A`); **`retOrdDetSndStatement_of_stoppedModels`**: `RetOrdDetSndStatement` from it, Aux. lemma 54 and Theorem 1.3;
* `RetOrdDetFstRecStatement`: (Det) for the first continuation in the chart recentred at the first tip's chart point
  `τ = tipPos` (word `shiftW τ β.1` from the seed `0`, field `flowField τ 0` of the retained chart field, chart path
  of `φ − τ`); `RetOrdStoppedModelsFstStatement`, **`retOrdDetFstRecStatement_of_stoppedModels`**. The passage from
  the recentred form to `RetOrdDetFstStatement` (covariance of the canonical code under recentring,
  `canonRetPath_shift`) is PROVE-T15-ORDDET4's.

The two model statements are the remaining obligations of the A-stop plumbing (named statements, not inputs of any
frozen theorem). R43/R48: for Theorem 1.5; Theorem 1.3 is used (allowed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal

open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart LQGMetric Sec7.Lemma76F OrdAStop

/-! ### The second continuation -/

/-- **A-stopped models of the second continuation** (the remaining construction for `RetOrdDetSndStatement`): with the
binders of `RetOrdDetSndStatement` (without the code), finitely many measurable events cover the ordinary pairs almost
surely, and on each with positive probability the second continuation of `d`'s chart, stopped at its first new contact
with `η₁[0,u] ∪ η₂[0,r]` only, has a stopped model with an initial code, with word `β.1` and the retained chart
field. **Not proved in Lean.** -/
def RetOrdStoppedModelsSndStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∃ (n : ℕ) (M : Fin n → Set Ω), (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, P (M i) ≠ 0 → Nonempty (StoppedModelTransferJ κ θ₂ P (M i) (fun ω => (β ω).1)
        (hd.chartField κ h)
        (fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
        (fun ω => canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0))

/-- **(Det) for the second continuation from A-stopped models**, Aux. lemma 54 and Theorem 1.3. -/
theorem retOrdDetSndStatement_of_stoppedModels
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedExtend.StoppedHullExtendStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hmodels : RetOrdStoppedModelsSndStatement.{u}) :
    RetOrdDetSndStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂ u₀ hu₀
    β hβ hmean hword
  obtain ⟨n, M, hM, hcover, hmodel⟩ := hmodels κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hag u₀ hu₀ β hβ hmean hword
  exact ae_codeMatch_of_finite_stoppedModelsJ
    (F := {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r}) hM hcover hmodel (hext κ hκ hκ4) h13
    hκ hF₂

/-! ### The first continuation, in the chart recentred at the first tip -/

/-- **(Det) for the first continuation in the recentred chart**: `RetOrdDetFstStatement` read in the retained chart
translated by the first tip's chart point `τ = tipPos d η₁ ω`: the canonical retained clock of `φ − τ` from the seed
`0`, matched with the canonical code of the word `shiftW τ β.1` (seed `0`) and the translated chart field
`flowField τ 0`. **Not proved in Lean.** -/
def RetOrdDetFstRecStatement : Prop :=
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
      canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≤
          (F₁ ((Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β ω).1, 0),
            Exist.flowField (tipPos d η₁ ω) 0 (hd.chartField κ h ω))).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
            (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
          canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
              (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s =
            decPath (F₁ ((Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β ω).1, 0),
              Exist.flowField (tipPos d η₁ ω) 0 (hd.chartField κ h ω))) s

/-- **A-stopped models of the first continuation in the recentred chart** (the remaining construction for
`RetOrdDetFstRecStatement`). **Not proved in Lean.** -/
def RetOrdStoppedModelsFstStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∃ (n : ℕ) (M : Fin n → Set Ω), (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, P (M i) ≠ 0 → Nonempty (StoppedModelTransferJ κ θ₁ P (M i)
        (fun ω => Exist.StagedLaw.BoundaryWord.shiftW (tipPos d η₁ ω) (β ω).1)
        (fun ω => Exist.flowField (tipPos d η₁ ω) 0 (hd.chartField κ h ω))
        (fun ω => canonRetLife (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
        (fun ω => canonRetPath (d.D ω) (fun z => d.fwd ω z - tipPos d η₁ ω) (η₁ ω) (ζ₁ ω) d.u
          (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0))

/-- **(Det) for the first continuation in the recentred chart from A-stopped models**, Aux. lemma 54 and
Theorem 1.3. -/
theorem retOrdDetFstRecStatement_of_stoppedModels
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedExtend.StoppedHullExtendStatement.{0} κ)
    (h13 : Exist.Theorem13Statement.{0}) (hmodels : RetOrdStoppedModelsFstStatement.{u}) :
    RetOrdDetFstRecStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₁ hF₁ u₀ hu₀
    β hβ hmean hword
  obtain ⟨n, M, hM, hcover, hmodel⟩ := hmodels κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hag u₀ hu₀ β hβ hmean hword
  exact ae_codeMatch_of_finite_stoppedModelsJ
    (F := {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r}) hM hcover hmodel (hext κ hκ hκ4) h13
    hκ hF₁

end RLC

end InteractingSLE
