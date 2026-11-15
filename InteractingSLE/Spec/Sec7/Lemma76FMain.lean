/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76FAssembly
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Lemma 7.6's conditional-law input from the mean identification and the determination identity

Packet PROVE-T15-CLOSE1 (2). PROVE-LEMMA76E's named input `Lemma76CondDetHeightsStatement` bundles three things at a
good disjoint pair: (R1) for the retained chart field, the right-side heights of the word, and (Det). Here (R1) is
proved (`exists_r1_of_meanIdent`: the marked locality of the two stopped prefixes with their killing records, the
stopped retained data and the random chart transport), and the input splits into two named inputs:

* **`Lemma76MeanIdentStatement`** (specification pp. 268–269: the canonical seed by Aux. 29 and Aux. 61, the new-slit
  germs `∓λ` of the second path, the first path's sides by nested retained comparison, the junction value): a datum `β`,
  measurable for the retained σ-algebra `retSigma76`, whose word mean is the chart transport of the conditional mean
  (`IsRetMeanIdent`), sorted and with the right-side heights at disjoint pairs;
* **`Lemma76DetStatement`** (Theorem W8's (Det), p. 541; the domain Markov step): for every such datum, the second
  continuation's canonical retained clock is the decoded canonical flow code of the chart field. Its restart variable
  can use the measurable clock `exists_retClock_snd` (`Lemma76FClock.lean`).

* **`lemma76CondDetHeightsStatement_of_meanIdent`**: `Lemma76CondDetHeightsStatement` from Lemma 7.5 and the two
  inputs; `lemma76Statement_of_meanIdent`: Lemma 7.6 from Theorems 1.2 (param) and 1.3, Lemma 7.5 and the two inputs.

The mean identification itself reduces to the boundary values of the conditional mean in the retained chart
(`Lemma76FAssembly.lean`, Aux. 28–29):

* **`Lemma76ChartBoundaryStatement`** (named input, finer): a retained-measurable datum, sorted and with the right-side
  heights at disjoint pairs, whose word datum is the boundary value of the conditional mean in the retained chart
  outside finitely many real chart points (`IsRetChartBoundaryLimit`);
* **`lemma76MeanIdentStatement_of_chartBoundary`**, **`lemma76CondDetHeightsStatement_of_chartBoundary`**,
  `lemma76Statement_of_chartBoundary`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar chiC)

universe u

namespace InteractingSLE

namespace Sec7

open LQGMetric Restart Supp7 Lemma76F

/-- **Named input: the mean identification and the right-side heights at a disjoint pair** (proof of Lemma 7.6,
pp. 268–269). For two flow lines as in Lemma 7.6, retained data `d` at deterministic stops agreeing with them and the
bounded harmonic extension `u₀` of the data, there is a datum `β`, measurable for the retained σ-algebra of the two
killed histories (`retSigma76`), such that the chart transport of the conditional mean given the germs of the stopped
union is the word mean of `β` (`IsRetMeanIdent`), and almost surely at a disjoint pair `β` is sorted and has the
right-side heights. **Not proved in Lean.** -/
def Lemma76MeanIdentStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∃ β : Ω → BoundaryWord, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β ∧
      IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).IsSorted ∧ IsRightSideHeights κ θ₁ b (η₁ ω) d.u (d.inv ω) (β ω)

/-- **Named input: (Det) at a disjoint pair** (Theorem W8's (Det), p. 541, in G7's retained chart). For every datum
`β` measurable for the retained σ-algebra, with the mean identification and sorted at disjoint pairs, and every
canonical flow code `F₂` of the angle `θ₂`, almost surely at a disjoint pair the second continuation's canonical
retained clock agrees, up to its lifetime, with the decoded canonical flow code of the chart field from `0`, whose
lifetime is at least that of the clock. **Not proved in Lean.** -/
def Lemma76DetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
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
    ∀ β : Ω → BoundaryWord, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdent κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β →
      (∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → (β ω).IsSorted) →
    ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 ≤
          (F₂ ((β ω, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 →
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0 s =
            decPath (F₂ ((β ω, 0), hd.chartField κ h ω)) s

/-- **`Lemma76CondDetHeightsStatement` from the mean identification and (Det)**: (R1) is `exists_r1_of_meanIdent`
(with `𝒢` the retained σ-algebra enlarged by the germs and the killed histories, `M` the disjoint-pair event read from
the retained histories); sortedness, the heights and (Det) are passed through. -/
theorem lemma76CondDetHeightsStatement_of_meanIdent (hL75 : Theorem15.Lemma75Statement.{u})
    (hMI : Lemma76MeanIdentStatement.{u}) (hDet : Lemma76DetStatement.{u}) : Lemma76CondDetHeightsStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  obtain ⟨β, hβ, hmean, hsort⟩ :=
    hMI κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  obtain ⟨𝒢, M, hR𝒢, hM, hMiff, hR1⟩ := exists_r1_of_meanIdent hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ hmean
  have hdet := hDet κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂ u₀ hu₀ β hβ
    hmean (by filter_upwards [hsort] with ω hω hp using (hω hp).1)
  refine ⟨𝒢, M, β, hM, hβ.mono hR𝒢 le_rfl, ?_, hR1, ?_⟩
  · filter_upwards [hMiff, hsort] with ω hiff hs hωM
    exact (hs (hiff.1 hωM)).1
  · filter_upwards [hMiff, hsort, hdet] with ω hiff hs hd' hp
    exact ⟨hiff.2 hp, (hs hp).2, (hd' hp).1, (hd' hp).2⟩

/-- **Lemma 7.6** from Theorem 1.2 (word-measurable form), Theorem 1.3, Lemma 7.5 and the two named inputs (the
junction inequality is `Lemma76E.flowLineJunctionStatement`, Aux. lemma 60 is `Lemma76E.pos_of_inv_mem_fst`). -/
theorem lemma76Statement_of_meanIdent (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hMI : Lemma76MeanIdentStatement.{u}) (hDet : Lemma76DetStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_param_heights h12p h13 (lemma76CondDetHeightsStatement_of_meanIdent hL75 hMI hDet)

/-- **Named input (finer): the boundary values of the conditional mean in the retained chart at a disjoint pair**
(proof of Lemma 7.6, pp. 268–269: the canonical seed at the second tip, the new-slit germs `∓λ − θ₂χ` on the two
sides of the second prefix, the first prefix's sides `λ − θ₁χ` and `−λ − θ₁χ` by nested retained comparison, the
original data on the untouched real boundary, the junction). There is a datum `β`, measurable for the retained
σ-algebra, sorted and with the right-side heights at disjoint pairs, whose word datum is, outside finitely many real
chart points, the boundary value of `v + 𝔥₀ + χ arg φ′` read through the chart inverse (`IsRetChartBoundaryLimit`).
**Not proved in Lean.** -/
def Lemma76ChartBoundaryStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω), d.IsMeasGood →
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∃ β : Ω → BoundaryWord, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β ∧
      IsRetChartBoundaryLimit κ P h η₁ η₂ ζ₁ ζ₂ u₀ d β ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).IsSorted ∧ IsRightSideHeights κ θ₁ b (η₁ ω) d.u (d.inv ω) (β ω)

/-- **The mean identification from the chart boundary values** (Aux. 28–29 in bounded coordinates,
`isRetMeanIdent_of_chartBoundaryLimit`). -/
theorem lemma76MeanIdentStatement_of_chartBoundary (hL75 : Theorem15.Lemma75Statement.{u})
    (hCB : Lemma76ChartBoundaryStatement.{u}) : Lemma76MeanIdentStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  obtain ⟨β, hβ, hbd, hsort⟩ := hCB κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀
  refine ⟨β, hβ, ?_, hsort⟩
  exact isRetMeanIdent_of_chartBoundaryLimit hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀
    (by filter_upwards [hsort] with ω hω hp using (hω hp).1) hbd

/-- **`Lemma76CondDetHeightsStatement` from the chart boundary values and (Det).** -/
theorem lemma76CondDetHeightsStatement_of_chartBoundary (hL75 : Theorem15.Lemma75Statement.{u})
    (hCB : Lemma76ChartBoundaryStatement.{u}) (hDet : Lemma76DetStatement.{u}) :
    Lemma76CondDetHeightsStatement.{u} :=
  lemma76CondDetHeightsStatement_of_meanIdent hL75 (lemma76MeanIdentStatement_of_chartBoundary hL75 hCB) hDet

/-- **Lemma 7.6** from Theorem 1.2 (word-measurable form), Theorem 1.3, Lemma 7.5, the chart boundary values and
(Det). -/
theorem lemma76Statement_of_chartBoundary (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hCB : Lemma76ChartBoundaryStatement.{u}) (hDet : Lemma76DetStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_param_heights h12p h13 (lemma76CondDetHeightsStatement_of_chartBoundary hL75 hCB hDet)

end Sec7

end InteractingSLE
