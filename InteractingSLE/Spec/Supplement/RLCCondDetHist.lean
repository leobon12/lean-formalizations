/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCondDetHistR1
import InteractingSLE.Spec.Supplement.RLCLRestartCond

/-!
# G7's conditional law given the retained histories: the reduction to the mean word and (Det)

Packet PROVE-CONDDET-HIST. Target: `RLC.RetainedCanonCondDetHistStatement` (PROVE-RLC-L), Lemma G7's conditional law of
the chart field given the two retained killed histories at an ordinary retained pair (supplement pp. 497–498), with the
outer word (Aux. 85–86, proof of Theorem 7.12D, p. 543) and (Det) for both continuations. Its three ingredients are
separated:

* **(R1)** is proved here from the mean identification at the ordinary pairs, for every word measurable for the
  retained σ-algebra (`exists_r1_of_meanIdentOrd`, `RLCCondDetHistR1.lean`): the ordinary-pair event need not be
  measurable; the event `M` of (R1) is its measurable hull in the conditioning σ-algebra;
* **`RetOrdMeanWordStatement`** (named input): the explicit initial word of the ordinary pair — a word measurable for
  the retained σ-algebra with the mean identification, sorted, with the canonical heights on the exposed sides
  (`IsRetainedWord`), the original datum on the untouched real points (`IsUntouchedWord`), and the first tip's chart
  position as positive seed (G7's premise "its inherited hydrodynamic chart gives a canonical finite-piece initial
  mean", from the outer-word argument of Aux. 85–86);
* **`RetOrdDetStatement`** (named input): (Det) for both continuations at the ordinary pairs, given such a word (G7's
  conclusion, p. 497: "it is the canonical stopped flow of the conditional field"); the analogue of
  `Sec7.Lemma76DetRStatement` for the ordinary pair and both curves;
* **`retainedCanonCondDetHistStatement_of_meanWord_det`**: the target from Lemma 7.5 and the two inputs;
  `retainedCanonCondDetUntouchedStatement_of_meanWord_det`: RLC-E's input.

R43/R48: Lemma 7.5 and the two inputs; for Theorem 1.5 only.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart LQGMetric Sec7.Lemma76F

/-- **Named input: the explicit initial word of an ordinary retained pair** (Lemma G7's premise, supplement p. 497:
"Assume its inherited hydrodynamic chart `φ : D → ℍ` gives a canonical finite-piece initial mean, with no extra singular
term"; at the ordinary retained pair of Theorem 7.12D, p. 543, "the outer-word argument of Aux. 85–86 gives the full
canonical initial finite word"). For two flow lines (`x₂ ≤ x₁`, `θ₁ < θ₂`), retained data `d` agreeing with them and the
bounded harmonic extension `u₀` of the boundary data, there is a datum `β = (word, seed)`, measurable for the retained
σ-algebra `retSigma76`, such that the conditional mean of the field given the stopped union, read in the retained chart,
is the word mean of `β.1` at almost every ordinary pair (`IsRetMeanIdentOn`), and almost surely at an ordinary pair:
the word is sorted, the seed is the chart position of the first tip and is positive, the word has the canonical heights
on the exposed sides and the original datum on the untouched real points. **Not proved in Lean.** -/
def RetOrdMeanWordStatement : Prop :=
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
    ∃ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β ∧
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1

/-- **Named input: (Det) for both continuations at an ordinary retained pair** (Lemma G7's conclusion, supplement
p. 497: "Hence it is the canonical stopped flow of the conditional field, with its original stopping rule recovered in
relative capacity"; both current tips, as in Lemma W2's proof, p. 531). Binders of `RetOrdMeanWordStatement`, canonical
flow codes `F₁`, `F₂` for the angles `θ₁`, `θ₂`, and a datum `β` with the conclusions of `RetOrdMeanWordStatement`
(G7's premises: the canonical conditional field with its initial word). Conclusion: almost surely at an ordinary pair,
each continuation's canonical retained clock, up to its first new contact with the retained union, is the canonical
flow of the chart field (from the seed `β.2` for the first path, `0` for the second), and its stop precedes the flow's
lifetime. The analogue of `Sec7.Lemma76DetRStatement` for the ordinary pair and both paths. **Not proved in Lean.** -/
def RetOrdDetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ F₁ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₁ F₁ → IsCanonicalFlowCode κ θ₂ F₂ →
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
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
              (tipPos d η₁ ω) →
          canonRetPath (d.D ω) (d.fwd ω) (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r)
              (tipPos d η₁ ω) s =
            decPath (F₁ (β ω, hd.chartField κ h ω)) s) ∧
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≤
          (F₂ (((β ω).1, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s =
            decPath (F₂ (((β ω).1, 0), hd.chartField κ h ω)) s

/-- **G7's conditional law given the retained histories, from Lemma 7.5, the initial word and (Det).** The datum is
`RetOrdMeanWordStatement`'s; (R1) with `𝒢 ⊇ retSigma76` on the measurable hull `M` of the ordinary-pair event is
`exists_r1_of_meanIdentOrd`; sortedness and positivity of the seed pass from the ordinary pairs to `M` by the hull
property (both are `𝒢`-events); the canonical clocks are the given chart paths at ordinary pairs
(`IsCanonRetClock`), so (Det) is `RetOrdDetStatement`. -/
theorem retainedCanonCondDetHistStatement_of_meanWord_det (hL75 : Theorem15.Lemma75Statement.{u})
    (hW : RetOrdMeanWordStatement.{u}) (hDet : RetOrdDetStatement.{u}) : RetainedCanonCondDetHistStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
    γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁ hV₂ hc₁ hc₂ hcanon F₁ F₂ hF₁ hF₂
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨β, hβ, hmean, hword⟩ :=
    hW κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  have hβ₁ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] fun ω => (β ω).1 := measurable_fst.comp hβ
  obtain ⟨𝒢, M, hR𝒢, hM, hOM, hhull, hR1⟩ :=
    exists_r1_of_meanIdentOrd hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hβ₁ hmean
  have hdet := hDet κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₁ F₂ hF₁ hF₂ u₀ hu₀
    β hβ hmean hword
  have hβ𝒢 : Measurable[𝒢.1] β := hβ.mono hR𝒢 le_rfl
  -- sortedness and a positive seed on `M`, through the hull
  have hA : MeasurableSet[𝒢.1] {ω | (β ω).1.IsSorted ∧ 0 < (β ω).2} :=
    ((measurable_fst.comp hβ𝒢) BoundaryWord.measurableSet_isSorted).inter
      (measurableSet_lt (mδ := 𝒢.1) measurable_const (measurable_snd.comp hβ𝒢))
  have hsortM := hhull _ hA (by
    filter_upwards [hword] with ω hω hord
    obtain ⟨hs, -, hpos, -⟩ := hω hord
    exact ⟨hs, hpos⟩)
  refine ⟨𝒢, M, β, hR𝒢, hM, hβ𝒢, hsortM, hR1, ?_⟩
  filter_upwards [hOM, hword, hdet, hcanon] with ω hωM hω hdω hcω hord
  obtain ⟨-, -, -, hret, hunt⟩ := hω hord
  obtain ⟨l₁, p₁, l₂, p₂⟩ := hdω hord
  obtain ⟨eV₁, eγ₁, eV₂, eγ₂⟩ := hcω hord
  refine ⟨hωM hord, hret, hunt, eV₁ ▸ l₁, fun s hs => ?_, eV₂ ▸ l₂, fun s hs => ?_⟩
  · rw [eγ₁ s hs]
    exact p₁ s (eV₁ ▸ hs)
  · rw [eγ₂ s hs]
    exact p₂ s (eV₂ ▸ hs)

/-- **RLC-E's two-tip input from Lemma 7.5, the initial word and (Det).** -/
theorem retainedCanonCondDetUntouchedStatement_of_meanWord_det (hL75 : Theorem15.Lemma75Statement.{u})
    (hW : RetOrdMeanWordStatement.{u}) (hDet : RetOrdDetStatement.{u}) :
    RetainedCanonCondDetUntouchedStatement.{u} :=
  retainedCanonCondDetUntouchedStatement_of_hist (retainedCanonCondDetHistStatement_of_meanWord_det hL75 hW hDet)

end RLC

end InteractingSLE
