/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.CondDet
import InteractingSLE.Spec.Restart.KernelG7
import InteractingSLE.Spec.Restart.KernelFC

/-!
# Lemma G7's retained kernel and the first-contact kernel (R2′) with canonical flow codes

Packet PROVE-CONDDET. PROVE-RESTARTKERNEL reduced `Supp7.RetainedKernelClockStatement` (G7) and
`Restart.FirstContactWordKernelStatement` (R2′) to `FlowCodeStatement` plus the P-side inputs
`RetainedCondDetStatement` / `FirstContactCondDetStatement` (`KernelG7.lean`, `KernelFC.lean`). Both inputs quantify
over codes satisfying `IsFlowCode`, which no map satisfies (`FlowCode.lean`): the inputs are vacuous and
`FlowCodeStatement` is false, so those reductions prove nothing. This file restates the inputs with canonical flow codes
(`IsCanonicalFlowCode`) and redoes the reductions:

* `RetainedCanonCondDetStatement`, **`retainedKernelClockStatement_of_canonCondDet`**,
  `retainedPairRestartStatement_of_canonCondDet`, **`retainedKernelClockStatement_of_param`**;
* `FirstContactCanonCondDetStatement`, **`firstContactWordKernelStatement_of_canonCondDet`**,
  `firstContactKernelClockStatement_of_canonCondDet`, **`firstContactWordKernelStatement_of_param`**.

The `_of_param` forms discharge the code input from `Theorem12ParamStatement` and `Theorem13Statement`
(`canonicalFlowCodeStatement_of_param`), so the only remaining input of each target is its P-side (R1)/word/(Det)
statement. By `restartKernel_codeMatch_iff` its (Det) clause is equivalent to "under almost every kernel measure the
continuations are flow lines of the chart field", and it does not depend on the canonical code chosen.

**R43.** G7 and the first-contact restart feed Theorems 1.4–1.5, downstream of Theorem 1.2; not Lemma 7.1's chain.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace Restart

open LQGMetric Supp7

/-- **Named input (corrected): the retained pair's conditional field, outer word and determination identity**, with
canonical flow codes (`IsCanonicalFlowCode`) in place of the unsatisfiable `IsFlowCode` of `RetainedCondDetStatement`
(Lemma G7, pp. 497–498; Theorem W8's proof, pp. 539–541; Aux. lemmas 85–86 for the word). Binders of
`Supp7.RetainedKernelClockStatement` (two flow lines, retained data `d`, the canonical relative capacity clocks
`γᵢ`, `Vᵢ`), and any canonical flow codes `F₁` (angle `θ₁`) and `F₂` (angle `θ₂`). There are a sub-σ-algebra `𝒢`, a
`𝒢`-event `M` and a `𝒢`-measurable datum `β = (word, tip position)` such that:
* on `M` the word is sorted and the tip position is positive;
* (R1) on `M`, conditionally on `𝒢`, the chart field has the Gaussian characteristic functional of the word;
* almost surely at an ordinary retained pair: `ω ∈ M`, the outer word `IsRetainedWord` holds, and (Det) each
  canonical clock `γᵢ` agrees up to its stop `Vᵢ` with the decoded canonical flow code of the chart field (from the
  tip position for the first path, from `0` for the second), whose lifetime is at least `Vᵢ`. -/
def RetainedCanonCondDetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (V₁ V₂ : Ω → ℝ≥0∞), (∀ t, Measurable fun ω => γ₁ ω t) →
      (∀ t, Measurable fun ω => γ₂ ω t) → Measurable V₁ → Measurable V₂ →
      (∀ ω, ContinuousOn (γ₁ ω) {s | (s : ℝ≥0∞) ≤ V₁ ω}) → (∀ ω, ContinuousOn (γ₂ ω) {s | (s : ℝ≥0∞) ≤ V₂ ω}) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        IsCanonRetClock d η₁ η₂ ζ₁ ζ₂ γ₁ γ₂ V₁ V₂ ω) →
    ∀ F₁ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₁ F₁ → IsCanonicalFlowCode κ θ₂ F₂ →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord × ℝ),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).1.IsSorted ∧ 0 < (β ω).2) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω).1 φ) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        V₁ ω ≤ (F₁ (β ω, hd.chartField κ h ω)).2 ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₁ ω → γ₁ ω s = decPath (F₁ (β ω, hd.chartField κ h ω)) s) ∧
        V₂ ω ≤ (F₂ (((β ω).1, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₂ ω → γ₂ ω s = decPath (F₂ (((β ω).1, 0), hd.chartField κ h ω)) s

/-- **Lemma G7's retained kernel from the general restart kernel**: canonical flow codes and the retained pair's
conditional field, outer word and determination identity give `Supp7.RetainedKernelClockStatement`. -/
theorem retainedKernelClockStatement_of_canonCondDet (hF : CanonicalFlowCodeStatement)
    (hD : RetainedCanonCondDetStatement.{u}) : RetainedKernelClockStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
    γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁ hV₂ hc₁ hc₂ hcanon
  obtain ⟨F₁, hF₁⟩ := hF κ θ₁ hκ hκ4
  obtain ⟨F₂, hF₂⟩ := hF κ θ₂ hκ hκ4
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁
      hV₂ hc₁ hc₂ hcanon F₁ F₂ hF₁ hF₂
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hMm : MeasurableSet M := 𝒢.2 _ hM
  set Hc := hd.chartField κ h with hHc
  have hHcm : Measurable Hc := hd.measurable_chartField κ hh.1
  set X : Ω → RestartSpace := fun ω =>
    (Hc ω, F₁ (((β ω).1, (β ω).2), Hc ω), F₂ (((β ω).1, 0), Hc ω)) with hXdef
  have hXm : Measurable X := by
    refine hHcm.prodMk ((hF₁.1.comp ?_).prodMk (hF₂.1.comp ?_))
    · exact ((measurable_fst.comp hβm).prodMk (measurable_snd.comp hβm)).prodMk hHcm
    · exact ((measurable_fst.comp hβm).prodMk measurable_const).prodMk hHcm
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hXm
  have hco := isRestartCoordinates_restartSpace
  -- (R1) under the kernel
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word 𝒢.2 hM hβ measurable_fst
    (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).1) hXm (H := RestartSpace.field)
    measurable_fst hlaw hR1
  -- the two continuations are the canonical flows of the chart field, by construction
  have hfl₁ := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw measurable_fst measurable_snd
    (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₁) hco.2.2.2.1 hco.2.1
    hco.2.2.2.2.2.1 hF₁ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  have hfl₂ := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw measurable_fst (x := fun _ => (0 : ℝ))
    measurable_const (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₂) hco.2.2.2.2.1
    hco.2.2.1 hco.2.2.2.2.2.2 hF₂ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  have hpos : ∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 :=
    (ae_map_iff (p := fun c : BoundaryWord × ℝ => 0 < c.2) hβm.aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).2
      ((ae_restrict_iff' hMm).2 (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).2))
  refine ⟨RestartSpace, inferInstance, RestartSpace.field, RestartSpace.path₁, RestartSpace.path₂,
    RestartSpace.life₁, RestartSpace.life₂, M, β, X, K, hco, hMm, hβm, hXm, hK, hlaw, ?_, ?_⟩
  · filter_upwards [hgff, hfl₁, hfl₂, hpos] with c ⟨_, hcg⟩ h1 h2 hc
    exact ⟨hc, hcg, h1, h2⟩
  · filter_upwards [hpath] with ω hω hord
    obtain ⟨hωM, hw, hV₁, he₁, hV₂, he₂⟩ := hω hord
    exact ⟨hωM, rfl, hV₁, fun s hs => (he₁ s hs).symm, hV₂, fun s hs => (he₂ s hs).symm, hw⟩

/-- **Lemma G7's `RetainedPairRestartStatement` from the general restart kernel** (with PROVE-G7B's clocks). -/
theorem retainedPairRestartStatement_of_canonCondDet (hF : CanonicalFlowCodeStatement)
    (hD : RetainedCanonCondDetStatement.{u}) : RetainedPairRestartStatement.{u} :=
  retainedPairRestartStatement_of_clock (retainedKernelClockStatement_of_canonCondDet hF hD)

open LQGMetric

/-- **Named input (corrected): Lemma 7.8's word and mean formula, and the determination identity of the
continuations**, with canonical flow codes (`IsCanonicalFlowCode`) in place of the unsatisfiable `IsFlowCode` of
`FirstContactCondDetStatement`
(Lemma 7.8, pp. 290–295; Theorem W8's proof, pp. 539–541). Binders of `FirstContactWordKernelStatement`, and any
canonical flow codes `F₁` (angle `θ₁`), `F₂` (angle `θ₂`). There is a datum `β`, measurable for the retained
σ-algebra `retSigma d P` and sorted on the meeting branch `meetSet d`, satisfying Lemma 7.8's mean identification on
every box, such that almost surely on `meetSet d` each canonical chart path `γᵢ` with lifetime `Uᵢ` is the decoded
canonical flow code of the chart field with the word `β` from the seed `0` ((Det)). -/
def FirstContactCanonCondDetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : PairData Ω) (hd : d.IsMeasGood), d.ζ₁ = ζ₁ → d.ζ₂ = ζ₂ →
      (∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t) →
    ∀ Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens, Hc = hd.chartField κ h →
    ∀ (γ₁ γ₂ : Ω → ℝ≥0 → ℂ) (U₁ U₂ : Ω → ℝ≥0∞), (∀ t, Measurable fun ω => γ₁ ω t) →
      (∀ t, Measurable fun ω => γ₂ ω t) → Measurable U₁ → Measurable U₂ → d.IsCanonClock P γ₁ γ₂ U₁ U₂ →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ F₁ F₂ : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₁ F₁ → IsCanonicalFlowCode κ θ₂ F₂ →
    ∃ β : Ω → BoundaryWord,
      Measurable[retSigma d P] β ∧ (∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted) ∧
      IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β ∧
      ∀ᵐ ω ∂P, ω ∈ meetSet d →
        IsCodeMatch (F₁ ((β ω, 0), Hc ω)) (γ₁ ω) (U₁ ω) ∧ IsCodeMatch (F₂ ((β ω, 0), Hc ω)) (γ₂ ω) (U₂ ω)

/-- **The first-contact restart kernel (R2′) from the general restart kernel**: Lemma 7.5, Lemma 7.7, canonical flow
codes and the word-and-determination input give `FirstContactWordKernelStatement` (Aux. lemma 56 at first entrances is
`WholeField.retainedRangeEntranceStatement`). -/
theorem firstContactWordKernelStatement_of_canonCondDet (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hF : CanonicalFlowCodeStatement)
    (hD : FirstContactCanonCondDetStatement.{u}) :
    FirstContactWordKernelStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂ hae Hc hHc
    γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon u₀ hu₀
  obtain ⟨F₁, hF₁⟩ := hF κ θ₁ hκ hκ4
  obtain ⟨F₂, hF₂⟩ := hF κ θ₂ hκ hκ4
  obtain ⟨β, hβ, hsort, hmean, hdet⟩ := hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hζ₁ hζ₂ hae Hc hHc γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon u₀ hu₀ F₁ F₂ hF₁ hF₂
  have hR1 := fun φ => ae_condExp_cexp_chartField_eq_gaussCF_meetSet hL75 hL77
    WholeField.retainedRangeEntranceStatement hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae hu₀ hβ hmean φ
  subst hHc
  have hβm : Measurable β := hβ.mono (retSigma_le P) le_rfl
  have hM := hd.measurableSet_meetSet P
  have hMm : MeasurableSet (meetSet d) := retSigma_le P _ hM
  have hHcm : Measurable (hd.chartField κ h) := hd.measurable_chartField κ hh.1
  set X : Ω → RestartSpace × Unit := fun ω =>
    (RestartSpace.mk' (hd.chartField κ h ω) (γ₁ ω) (U₁ ω) (γ₂ ω) (U₂ ω), ()) with hXdef
  have hXm : Measurable X :=
    (RestartSpace.measurable_mk' hHcm hγ₁ hγ₂ hU₁ hU₂).prodMk measurable_const
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P (meetSet d) hβm hXm
  have hco := isRestartCoordinates_restartSpace
  have hHm : Measurable fun s : RestartSpace × Unit => s.1.field := measurable_fst.comp measurable_fst
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word (retSigma_le P) hM hβ (w := fun c => c)
    measurable_id hsort hXm (H := fun s : RestartSpace × Unit => s.1.field) hHm hlaw hR1
  have hfl₁ := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw (w := fun c => c) measurable_id
    (x := fun _ => (0 : ℝ)) measurable_const hHm (Γ := fun s : RestartSpace × Unit => s.1.path₁)
    (fun t => (hco.2.2.2.1 t).comp measurable_fst) (hco.2.1.comp measurable_fst)
    (fun s => hco.2.2.2.2.2.1 s.1) hF₁ hgff (by
      filter_upwards [hdet] with ω hω hωM
      exact isCodeMatch_path₁_mk' _ (hω hωM).1)
  have hfl₂ := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw (w := fun c => c) measurable_id
    (x := fun _ => (0 : ℝ)) measurable_const hHm (Γ := fun s : RestartSpace × Unit => s.1.path₂)
    (fun t => (hco.2.2.2.2.1 t).comp measurable_fst) (hco.2.2.1.comp measurable_fst)
    (fun s => hco.2.2.2.2.2.2 s.1) hF₂ hgff (by
      filter_upwards [hdet] with ω hω hωM
      exact isCodeMatch_path₂_mk' _ (hω hωM).2)
  refine ⟨β, Unit, inferInstance, fun _ => (), K, hβ, hsort, hmean, measurable_const, hK, hlaw, ?_⟩
  filter_upwards [hfl₁, hfl₂] with c h1 h2
  exact ⟨h1, h2⟩

/-- **CPL5's `FirstContactKernelClockStatement` from the general restart kernel** (through CPL7's reduction). -/
theorem firstContactKernelClockStatement_of_canonCondDet (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hF : CanonicalFlowCodeStatement)
    (hD : FirstContactCanonCondDetStatement.{u}) :
    FirstContactKernelClockStatement.{u} :=
  firstContactKernelClockStatement_of_word hL75 hL77 WholeField.retainedRangeEntranceStatement
    (firstContactWordKernelStatement_of_canonCondDet hL75 hL77 hF hD)

/-- **G7's retained kernel from Theorems 1.2–1.3 and the corrected P-side input.** -/
theorem retainedKernelClockStatement_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetStatement.{u}) :
    RetainedKernelClockStatement.{u} :=
  retainedKernelClockStatement_of_canonCondDet (canonicalFlowCodeStatement_of_param h12p h13) hD

/-- **The first-contact kernel (R2′) from Lemmas 7.5, 7.7, Theorems 1.2–1.3 and the corrected P-side input.** -/
theorem firstContactWordKernelStatement_of_param (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : FirstContactCanonCondDetStatement.{u}) :
    FirstContactWordKernelStatement.{u} :=
  firstContactWordKernelStatement_of_canonCondDet hL75 hL77 (canonicalFlowCodeStatement_of_param h12p h13) hD

end Restart

end InteractingSLE
