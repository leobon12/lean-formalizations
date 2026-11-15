/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GMain
import InteractingSLE.Spec.Restart.RetLife

/-!
# Lemma 7.6 from (Det) with the source's lifetime (ruling R55)

Packet PROVE-RETAUX79C. The specification's second continuation in the proof of Lemma 7.6 (p. 268) is "a simple
interior curve until its first new contact with `∂D`", i.e. it stops at its first contact with
`η₁[0, u] ∪ η₂[0, r] ∪ ℝ`. PROVE-RETAUX79B found that the named input `Lemma76DetStatement` (lifetime: first contact
with `η₁[0, u] ∪ η₂[0, r]` only) cannot be reached by the domain Markov route (the later pairs need not be disjoint
pairs). Ruling R55: state the source-faithful form beside the old one and re-derive Lemma 7.6's wiring from it.

* **`Lemma76DetRStatement`**: (Det) for the canonical retained clock of the second continuation stopped at its first
  contact with `η₁[0, u] ∪ η₂[0, r] ∪ ℝ` (`Lemma76DetStatement` is kept unchanged for reference);
* `Lemma76CondDetHeightsRStatement`, `Lemma76CondDetRStatement`: the corresponding conditional-law inputs;
* `lemma76CondDetHeightsRStatement_of_meanIdent`, `lemma76CondDetRStatement_of_heights`: passed through as for the old
  lifetime;
* **`lemma76KernelLtStatement_of_condDetR`**: Lemma 7.6's restart kernel at good configurations. A forbidden exit
  stays in the joint unbounded domain before its exit time, so it never touches `ℝ` before that time and the exit time
  is at most the new stop (`RetAux79.le_contStop_of_avoid`); the canonical retained clock of the new stop is the old
  clock of the path with its lifetime shortened to the new stop (`RetAux79.canonRetPath_shorten`), so G7's clock
  relation and the chart visit of the forbidden exit apply unchanged;
* **`lemma76Statement_of_detR`**: Lemma 7.6 from Theorems 1.2 (word-measurable form) and 1.3, Lemma 7.5 and
  `Lemma76DetRStatement`.

**R43.** As for the old lifetime, canonical codes use Theorems 1.2–1.3; Lemma 7.6 feeds only Theorem 1.5.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Sec7

open LQGMetric Restart Supp7 Lemma76F

/-- **Named input: (Det) at a disjoint pair, with the source's lifetime** (Theorem W8's (Det), p. 541, in G7's
retained chart; ruling R55). As `Lemma76DetStatement`, but the second continuation stops at its first contact with
`η₁[0, u] ∪ η₂[0, r] ∪ ℝ` (spec p. 268: first new contact with `∂D`). **Not proved in Lean.** -/
def Lemma76DetRStatement : Prop :=
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
      canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 ≤
          (F₂ ((β ω, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 →
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 s =
            decPath (F₂ ((β ω, 0), hd.chartField κ h ω)) s

/-- **`Lemma76CondDetHeightsStatement` with the source's lifetime** (ruling R55). **Not proved in Lean** (it follows
from Lemma 7.5 and `Lemma76DetRStatement`, `lemma76CondDetHeightsRStatement_of_det`). -/
def Lemma76CondDetHeightsRStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₂ F₂ →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ IsRightSideHeights κ θ₁ b (η₁ ω) d.u (d.inv ω) (β ω) ∧
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 ≤
          (F₂ ((β ω, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 →
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 s =
            decPath (F₂ ((β ω, 0), hd.chartField κ h ω)) s

/-- **`Lemma76CondDetStatement` with the source's lifetime** (ruling R55). **Not proved in Lean** (it follows from
Lemma 7.5 and `Lemma76DetRStatement`). -/
def Lemma76CondDetRStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₂ F₂ →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ IsRightSideWord κ θ₁ (η₁ ω) d.u (d.inv ω) (β ω) ∧
        canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 ≤
          (F₂ ((β ω, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤
            canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 →
          canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r ∪ realLine) 0 s =
            decPath (F₂ ((β ω, 0), hd.chartField κ h ω)) s

/-- **`Lemma76CondDetHeightsRStatement` from the mean identification and (Det) with the source's lifetime** (as
`lemma76CondDetHeightsStatement_of_meanIdent`: (R1) is `exists_r1_of_meanIdent`; the rest is passed through). -/
theorem lemma76CondDetHeightsRStatement_of_meanIdent (hL75 : Theorem15.Lemma75Statement.{u})
    (hMI : Lemma76MeanIdentStatement.{u}) (hDet : Lemma76DetRStatement.{u}) :
    Lemma76CondDetHeightsRStatement.{u} := by
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

/-- **`Lemma76CondDetRStatement` from the junction inequality and the heights** (as
`lemma76CondDetStatement_of_heights`). -/
theorem lemma76CondDetRStatement_of_heights (hJ : FlowLineJunctionStatement.{u})
    (hD : Lemma76CondDetHeightsRStatement.{u}) : Lemma76CondDetRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂
  refine ⟨𝒢, M, β, hM, hβ, hsort, hR1, ?_⟩
  filter_upwards [hpath, hag, hJ κ hκ hκ4 b jumps hb x₁ θ₁ P h η₁ ζ₁ hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hω hagω hjω hp₁ hp₂ hpair
  obtain ⟨hωM, hH, hlife, hdet⟩ := hω hpair
  obtain ⟨hG, a₁, a₂⟩ := hagω hpair.1 hpair.2.1
  refine ⟨hωM, isRightSideWord_of_heights hκ (pos_of_retChart hd hp₁ hp₂ hx hG a₁ a₂ hpair) ?_ hH, hlife, hdet⟩
  intro u hu him hmax
  have huζ : (u : ℝ≥0∞) < ζ₁ ω := lt_trans (ENNReal.coe_lt_coe.2 hu) hpair.1
  exact hjω u huζ him fun s hs => hmax s (hs.trans hu.le)

/-- **Lemma 7.6's restart kernel at good configurations from the conditional-determination input with the source's
lifetime** (as `lemma76KernelLtStatement_of_condDet`). The second continuation's canonical retained clock stopped at
its first contact with `A ∪ ℝ`, `A = η₁[0, u] ∪ η₂[0, r]`, is the canonical clock stopped at `A` of the path with its
lifetime shortened to that stop (`RetAux79.canonRetPath_shorten`); the forbidden exit runs in the joint unbounded
domain, hence off `A ∪ ℝ`, before its exit time, which is therefore at most the new stop. -/
theorem lemma76KernelLtStatement_of_condDetR (hF : CanonicalFlowCodeStatement)
    (hD : Lemma76CondDetRStatement.{u}) : Lemma76KernelLtStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ a r
  obtain ⟨d, hd, hdu, hdr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ a r
  subst hdu hdr
  obtain ⟨F₂, hF₂⟩ := hF κ θ₂ hκ hκ4
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hMm : MeasurableSet M := 𝒢.2 _ hM
  set Hc := hd.chartField κ h with hHc
  have hHcm : Measurable Hc := hd.measurable_chartField κ hh.1
  have hFm : Measurable fun ω => F₂ ((β ω, (0 : ℝ)), Hc ω) :=
    hF₂.1.comp ((hβm.prodMk measurable_const).prodMk hHcm)
  set X : Ω → RestartSpace := fun ω => (Hc ω, F₂ ((β ω, 0), Hc ω), F₂ ((β ω, 0), Hc ω)) with hXdef
  have hXm : Measurable X := hHcm.prodMk (hFm.prodMk hFm)
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hXm
  have hco := isRestartCoordinates_restartSpace
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word 𝒢.2 hM hβ measurable_id
    (by filter_upwards [hsort] with ω hω hωM; exact hω hωM) hXm (H := RestartSpace.field)
    measurable_fst hlaw hR1
  have hfl := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw measurable_id (x := fun _ => (0 : ℝ))
    measurable_const (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₂) hco.2.2.2.2.1
    hco.2.2.1 hco.2.2.2.2.2.2 hF₂ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  refine ⟨RestartSpace, inferInstance, RestartSpace.field, RestartSpace.path₂, RestartSpace.life₂, M, β, X, K,
    hco.1, hco.2.2.1, hco.2.2.2.2.1, hco.2.2.2.2.2.2, hMm, hβm, hXm, hK, hlaw, ?_, ?_⟩
  · filter_upwards [hgff, hfl] with c hc1 hc2
    exact ⟨hc1.2, hc2⟩
  · filter_upwards [hpath, hag, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hω hagω hp₁ hp₂ hpair hexit
    obtain ⟨hωM, hW, hlife, hdet⟩ := hω hpair
    obtain ⟨hG, a₁, a₂⟩ := hagω hpair.1 hpair.2.1
    have hωE := mem_E_of_isDisjointPair hd hG a₁ a₂ hpair
    obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hωE
    have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
        ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
      ⟨x₀, fun z => by
        show d.g ω z - d.shift ω = _
        rw [hx₀, RetData.g, RetData.K_of_mem hωE]⟩
    have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => a₁ s hs.2
    have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => a₂ t ht.2
    have hi₁ : d.η₁ ω '' Icc 0 d.u = η₁ ω '' Icc 0 d.u := e₁.image_eq
    have hdom : activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r = activeDomain (η₁ ω) d.u (η₂ ω) d.r :=
      activeDomain_congr_Icc e₁ e₂
    have htip : d.η₂ ω d.r = η₂ ω d.r := a₂ d.r le_rfl
    have hR₂ := isRetCont_snd (hd.good ω (RetData.E_subset_G hωE)) hC hφ hp₂ a₂ hpair.2.1
      (by rw [htip]; exact hpair.2.2.1)
      (by
        rw [htip, hi₁]
        exact fun h' => Set.disjoint_left.1 hpair.2.2.2.1 h' ⟨d.r, ⟨zero_le, le_rfl⟩, rfl⟩)
      (by rw [htip, hdom]; exact hpair.2.2.2.2.1)
    rw [hi₁] at hR₂
    set A := η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r with hA
    have hKc : IsCompact A := (Sec7.IsPathGood.isCompact_image_Icc hp₁ hpair.1.le).union
      (Sec7.IsPathGood.isCompact_image_Icc hp₂ hpair.2.1.le)
    have hDeq : d.D ω = H \ fillH A := by
      rw [hd.D_of_mem hωE, hdom]
      exact Lemma76Exit.unboundedPart_eq hKc.isClosed
    -- the continuation with its lifetime shortened to the boundary stop
    have hR₂' := RetAux79.isRetCont_shorten hR₂
    have hclk := isRetainedClock_canon hR₂'.shift_zero rfl hDeq
    rw [RetAux79.canonRetPath_shorten, RetAux79.canonRetLife_shorten] at hclk
    have hclk' : IsRetainedClock (η₂ ω) (contStop (η₂ ω) (ζ₂ ω) d.r (A ∪ realLine)) d.r A (d.inv ω)
        (RestartSpace.path₂ (X ω)) (RestartSpace.life₂ (X ω)) :=
      hclk.mono hlife fun s hs => (hdet s hs).symm
    obtain ⟨e, v, he, hex⟩ := hexit
    have he' : (e : ℝ≥0∞) ≤ contStop (η₂ ω) (ζ₂ ω) d.r (A ∪ realLine) := by
      refine RetAux79.le_contStop_of_avoid hex.1.le he fun t h1 h2 => ?_
      have hD' := hex.2.2.2.1 t ⟨h1, h2⟩
      rintro (hAt | hRt)
      · exact hD'.1.2 hAt
      · exact (ne_of_gt (show (0 : ℝ) < (η₂ ω t).im from hD'.1.1)) hRt
    obtain ⟨s, hsU, y, hΓy, hψy, w, hψw, hwy⟩ := Lemma76Exit.exists_chartVisit_of_isForbiddenExit hR₂' hclk'
      (hco.2.2.2.2.2.2 (X ω)) (Sec7.IsPathGood.continuousOn_Icc hp₁ hpair.1.le)
      (Sec7.IsPathGood.injOn_Icc hp₁ hpair.1.le) isCompact_lowerArc.isClosed
      (Set.disjoint_left.2 fun z hz hzH => notMem_lowerArc_of_mem_H hzH hz) hex he'
      (by rw [← Lemma76Exit.unboundedPart_eq hKc.isClosed]; exact hpair.2.2.2.2.2)
    obtain ⟨hy0, hadm⟩ := isAdmissibleRight_of_isRightSideWord hκ hκ4 hθ hW hψw hwy hex.2.1 hψy
    exact ⟨hωM, s, hsU, y, hy0, hΓy, hadm⟩

/-- **Lemma 7.6 (both halves) from canonical flow codes and the conditional-determination input with the source's
lifetime.** -/
theorem lemma76Statement_of_condDetR (hF : CanonicalFlowCodeStatement) (hD : Lemma76CondDetRStatement.{u}) :
    Lemma76Statement.{u} :=
  lemma76Statement_of_kernelLt (lemma76KernelLtStatement_of_condDetR hF hD)

/-- **PROVE-LEMMA76C's `Lemma76KernelStatement` from canonical flow codes and the conditional-determination input
with the source's lifetime.** -/
theorem lemma76KernelStatement_of_condDetR (hF : CanonicalFlowCodeStatement) (hD : Lemma76CondDetRStatement.{u}) :
    Lemma76KernelStatement.{u} :=
  lemma76KernelStatement_of_kernelLt (lemma76KernelLtStatement_of_condDetR hF hD)

/-- **Lemma 7.6's conditional-law input from Lemma 7.5 and (Det) with the source's lifetime.** -/
theorem lemma76CondDetHeightsRStatement_of_det (hL75 : Theorem15.Lemma75Statement.{u})
    (hDet : Lemma76DetRStatement.{u}) : Lemma76CondDetHeightsRStatement.{u} :=
  lemma76CondDetHeightsRStatement_of_meanIdent hL75 (Lemma76G.lemma76MeanIdentStatement_of_lemma75 hL75) hDet

/-- **Lemma 7.6** from Theorems 1.2 (word-measurable form) and 1.3, Lemma 7.5 and (Det) with the source's lifetime
(ruling R55; replaces `Lemma76G.lemma76Statement_of_det`). -/
theorem lemma76Statement_of_detR (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hL75 : Theorem15.Lemma75Statement.{u})
    (hDet : Lemma76DetRStatement.{u}) : Lemma76Statement.{u} :=
  lemma76Statement_of_condDetR (canonicalFlowCodeStatement_of_param h12p h13)
    (lemma76CondDetRStatement_of_heights Lemma76E.flowLineJunctionStatement
      (lemma76CondDetHeightsRStatement_of_det hL75 hDet))

end Sec7

end InteractingSLE
