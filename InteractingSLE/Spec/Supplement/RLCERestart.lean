/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCDReal

/-!
# The retained-pair restart with the word on untouched original-real intervals

Packet PROVE-RLC-E, piece (ii) of `RLC.RetainedChartRealCompletionStatement` (PROVE-RLC-D, "What remains" 4). Source:
Lemma G7 (supplement pp. 497–498): G7 identifies the **whole** conditional mean of the retained pair's chart field, so
the chart word is the canonical one on every boundary arc of the active component; on an untouched original-real
interval it is the original datum transported by the chart (Lemma G7's proof, p. 497: "An untouched original-real point
has a trace-free upper half-neighborhood […] The map `φ` extends analytically by reflection across such an interval";
Aux. lemma 57 fixes the argument lift there; cf. Aux. lemma 96, p. 325: "all original jumps of `H₀` survive with their
actual positions transported by the mapping-out map"). The landed restart chain records only the exposed sides
(`Supp7.IsRetainedWord`).

* `IsUntouchedWord b jumps A ψ c`: every chart real `y` whose image `ψ y` is a real point off `A` and off the jump
  candidates of `b` is not a jump of the word `c`, and `c(y) = b(ψ y)`;
* `RetainedCanonCondDetUntouchedStatement` (**named input**, the strengthened PROVE-CONDDET two-tip input
  `Restart.RetainedCanonCondDetStatement`: the same statement with `IsUntouchedWord` added to the outer word at an
  ordinary retained pair) and `retainedCanonCondDetStatement_of_untouched` (it implies the landed input);
* `RetainedPairRestartUntouchedStatement` (the strengthened `Supp7.RetainedPairRestartStatement`) and
  **`retainedPairRestartUntouchedStatement_of_param`**: from Theorems 1.2 (param), 1.3 and the strengthened input (the
  proofs of `Restart.retainedKernelClockStatement_of_canonCondDet` and `Supp7.retainedPairRestartStatement_of_clock`
  with the word clause carried along; the word `β` is passed through unchanged);
* `RealJointChartUntouchedStatement`, **`realJointChartUntouchedStatement_of_restart`**, `_of_param`: PROVE-RLC-D's
  real joint chart (`RLC.RealJointChartStatement`) with the untouched word in the same chart `ψ = d.inv ω`.

R43/R48: downstream of Theorem 1.2; for Theorem 1.5 only.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Supp9D Restart LQGMetric

/-- **The chart word on untouched original-real points**: every chart real `y` whose image `ψ y` is a real point off
the retained union `A` and off the jump candidates of the original data `b` is not a jump of the word `c`, and the word
there is the original height, `c(y) = b(ψ y)`. -/
def IsUntouchedWord (b : ℝ → ℝ) (jumps : Finset ℝ) (A : Set ℂ) (ψ : ℂ → ℂ) (c : BoundaryWord) : Prop :=
  ∀ y : ℝ, (ψ y).im = 0 → ψ y ∉ A → (ψ y).re ∉ jumps → y ∉ c.jumps ∧ c.fn y = b (ψ y).re

/-- **Named input: PROVE-CONDDET's two-tip input with the untouched word** (Lemma G7, pp. 497–498: the whole
conditional mean, hence the word on the untouched original-real intervals too). `Restart.RetainedCanonCondDetStatement`
with `IsUntouchedWord` added at an ordinary retained pair, for the same datum `β`. **Not proved in Lean.** -/
def RetainedCanonCondDetUntouchedStatement : Prop :=
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
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1 ∧
        V₁ ω ≤ (F₁ (β ω, hd.chartField κ h ω)).2 ∧
        (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₁ ω → γ₁ ω s = decPath (F₁ (β ω, hd.chartField κ h ω)) s) ∧
        V₂ ω ≤ (F₂ (((β ω).1, 0), hd.chartField κ h ω)).2 ∧
        ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₂ ω → γ₂ ω s = decPath (F₂ (((β ω).1, 0), hd.chartField κ h ω)) s

/-- The strengthened two-tip input implies the landed one. -/
theorem retainedCanonCondDetStatement_of_untouched (hD : RetainedCanonCondDetUntouchedStatement.{u}) :
    RetainedCanonCondDetStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
    γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁ hV₂ hc₁ hc₂ hcanon F₁ F₂ hF₁ hF₂
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag γ₁ γ₂ V₁ V₂ hγ₁ hγ₂ hV₁
      hV₂ hc₁ hc₂ hcanon F₁ F₂ hF₁ hF₂
  refine ⟨𝒢, M, β, hM, hβ, hsort, hR1, ?_⟩
  filter_upwards [hpath] with ω hω hord
  obtain ⟨h1, h2, -, h4⟩ := hω hord
  exact ⟨h1, h2, h4⟩

/-- **The strengthened retained-pair restart** (`Supp7.RetainedPairRestartStatement` with the untouched word for the
same datum `β`). -/
def RetainedPairRestartUntouchedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∃ (S : Type) (_ : MeasurableSpace S) (H : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ)
      (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S)
      (K : Kernel (BoundaryWord × ℝ) S),
      IsRestartCoordinates H Γ₁ Γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 ∧ IsGFFWithBoundaryData (K c) H c.1.fn c.1.jumps ∧
        IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ (K c) H Γ₁ U₁ ∧ IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ (K c) H Γ₂ U₂) ∧
      ∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        ω ∈ M ∧ H (X ω) = hd.chartField κ h ω ∧
        IsRetainedClock (η₁ ω) (ζ₁ ω) d.u (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω)
          (Γ₁ (X ω)) (U₁ (X ω)) ∧
        IsRetainedClock (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω)
          (Γ₂ (X ω)) (U₂ (X ω)) ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1

/-- **The strengthened retained-pair restart from Theorems 1.2 (param), 1.3 and the strengthened two-tip input**: the
proofs of `Restart.retainedKernelClockStatement_of_canonCondDet` (canonical flow codes, the restart kernel) and
`Supp7.retainedPairRestartStatement_of_clock` (the canonical relative capacity clocks), with the untouched word carried
along for the same datum `β`. -/
theorem retainedPairRestartUntouchedStatement_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetUntouchedStatement.{u}) :
    RetainedPairRestartUntouchedStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  obtain ⟨γ₁, γ₂, V₁, V₂, hγ₁, hγ₂, hV₁, hV₂, hc₁, hc₂, hcanon⟩ := exists_retClock hκ hκ4 hη₁ hη₂ hd hag
  have hF := canonicalFlowCodeStatement_of_param h12p h13
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
  -- the clocks (`Supp7.retainedPairRestartStatement_of_clock`)
  filter_upwards [hpath, hcanon, ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂, hag] with ω hω hc hg₁ hg₂ hagω hord
  obtain ⟨hMω, hW, hUW, hU₁, he₁, hU₂, he₂⟩ := hω hord
  obtain ⟨hL₁, hP₁, hL₂, hP₂⟩ := hc hord
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  have hωE := hd.mem_E_of_ordinary hG a₁ a₂ hord
  obtain ⟨⟨x₀, hx₀⟩, hC⟩ := hd.isRetChart hωE
  have hφ : ∃ x₀ : ℝ, ∀ z, d.fwd ω z =
      ConformalImage.mapOut (fillH (prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r)) z - x₀ :=
    ⟨x₀, fun z => by
      show d.g ω z - d.shift ω = _
      rw [hx₀, RetData.g, RetData.K_of_mem hωE]⟩
  obtain ⟨k₁, k₂⟩ := isRetainedClock_of_ordinary (hd.good ω (RetData.E_subset_G hωE)) hC hφ hg₁ hg₂ a₁ a₂ hord
  have hDd : d.D ω = activeDomain (d.η₁ ω) d.u (d.η₂ ω) d.r := hd.D_of_mem hωE
  rw [← hDd] at k₁ k₂
  have htip : (limUnder (𝓝[d.D ω] (η₁ ω d.u)) (d.fwd ω)).re = tipPos d η₁ ω := rfl
  rw [htip] at k₁
  have hΓ₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₁ ω → RestartSpace.path₁ (X ω) s = γ₁ ω s :=
    fun s hs => (he₁ s hs).symm
  have hΓ₂ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ V₂ ω → RestartSpace.path₂ (X ω) s = γ₂ ω s :=
    fun s hs => (he₂ s hs).symm
  refine ⟨hMω, rfl, k₁.mono (by rw [← hL₁]; exact hU₁) fun s hs => ?_,
    k₂.mono (by rw [← hL₂]; exact hU₂) fun s hs => ?_, hW, hUW⟩
  · rw [← hL₁] at hs
    rw [hΓ₁ s hs, hP₁ s hs]
  · rw [← hL₂] at hs
    rw [hΓ₂ s hs, hP₂ s hs]

/-- **The real joint chart with the untouched word**: `RLC.RealJointChartStatement` with, in the same chart `ψ`, the
datum's word equal to the original data on the untouched original-real points (`IsUntouchedWord`). -/
def RealJointChartUntouchedStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ u r : ℝ≥0,
    ∃ (S : Type) (_ : MeasurableSpace S) (H₀ : S → LQGMetric.DistOn upperHalfPlaneOpens) (Γ₁ Γ₂ : S → ℝ≥0 → ℂ)
      (U₁ U₂ : S → ℝ≥0∞) (M : Set Ω) (β : Ω → BoundaryWord × ℝ) (X : Ω → S)
      (K : Kernel (BoundaryWord × ℝ) S),
      IsRestartCoordinates H₀ Γ₁ Γ₂ U₁ U₂ ∧ MeasurableSet M ∧ Measurable β ∧ Measurable X ∧
      IsMarkovKernel K ∧
      (P.restrict M).map (fun ω => (β ω, X ω)) = (P.restrict M).map β ⊗ₘ K ∧
      (∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 ∧ IsGFFWithBoundaryData (K c) H₀ c.1.fn c.1.jumps ∧
        IsFlowLine κ c.1.fn c.1.jumps c.2 θ₁ (K c) H₀ Γ₁ U₁ ∧ IsFlowLine κ c.1.fn c.1.jumps 0 θ₂ (K c) H₀ Γ₂ U₂) ∧
      ∀ᵐ ω ∂P, Supp7.IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r →
        ω ∈ M ∧ ∃ ψ : ℂ → ℂ,
          IsRealJointChart (η₁ ω) (ζ₁ ω) u (η₂ ω) (ζ₂ ω) r (Γ₁ (X ω)) (Γ₂ (X ω)) (U₁ (X ω)) (U₂ (X ω)) ψ ∧
          IsRetainedWord κ θ₁ θ₂ (η₁ ω) u (η₂ ω) r ψ (β ω).1 ∧
          IsUntouchedWord b jumps (η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) ψ (β ω).1

/-- **The real joint chart with the untouched word from the strengthened restart** (the proof of
`RLC.realJointChartStatement_of_restart`, with the word clause carried along). -/
theorem realJointChartUntouchedStatement_of_restart (hR : RetainedPairRestartUntouchedStatement.{u}) :
    RealJointChartUntouchedStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨d, hd, hu, hr, hag⟩ := exists_retData_of_isFlowLine hκ hκ4 hη₁ hη₂ u r
  subst hu hr
  obtain ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag
  refine ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hdis, hlaw, ?_⟩
  filter_upwards [hpath, hag] with ω hω hagω hord
  obtain ⟨hG, ha₁, ha₂⟩ := hagω hord.1 hord.2.1
  have hE := hd.mem_E_of_ordinary hG ha₁ ha₂ hord
  obtain ⟨hMω, -, ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, hpth₁, hH₁⟩, ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, hpth₂, hH₂⟩, hword,
    huw⟩ := hω hord
  have hg := hd.good ω (RetData.E_subset_G hE)
  obtain ⟨-, hC⟩ := hd.isRetChart hE
  have e₁ : EqOn (d.η₁ ω) (η₁ ω) (Icc 0 d.u) := fun s hs => ha₁ s hs.2
  have e₂ : EqOn (d.η₂ ω) (η₂ ω) (Icc 0 d.r) := fun t ht => ha₂ t ht.2
  have hdom := activeDomain_congr_Icc e₁ e₂
  have htip : d.η₂ ω d.r = η₂ ω d.r := ha₂ d.r le_rfl
  refine ⟨hMω, d.inv ω, ⟨?_, ?_, hC.continuousOn_inv, hC.2.2.2.2.2.2.2.2.2.1, ?_,
    ⟨c₁, σ₁, hσ₁, hmono₁, himg₁, fun s hs => ⟨hpth₁ s hs, hH₁ s hs⟩⟩,
    ⟨c₂, σ₂, hσ₂, hmono₂, himg₂, fun s hs => ⟨hpth₂ s hs, hH₂ s hs⟩⟩, ?_⟩, hword, huw⟩
  · rw [← hdom]; exact hC.bijOn hg.2.2.2.2.2.1
  · rw [← hdom]; exact hC.inv_notMem hg.2.2.2.2.2.1
  · rw [← htip]; exact hC.inv_zero hg.2.2.2.2.2.1
  · intro y y' he _ hA
    have hK : d.inv ω (y : ℂ) ∉ prefixSet (d.η₁ ω) d.u (d.η₂ ω) d.r := by
      rw [prefixSet_congr_Icc e₁ e₂]; exact hA
    exact ofReal_injective (eq_of_inv_eq_of_notMem hC hg.1 hg.2.1 hg.2.2.2.2.1 hg.2.2.2.2.2.1
      (ofReal_mem_Hbar y) (ofReal_mem_Hbar y') he hK)

/-- **The real joint chart with the untouched word from Theorems 1.2 (param), 1.3 and the strengthened two-tip
input** (R43/R48: downstream of Theorem 1.2; for Theorem 1.5 only). -/
theorem realJointChartUntouchedStatement_of_param (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetUntouchedStatement.{u}) :
    RealJointChartUntouchedStatement.{u} :=
  realJointChartUntouchedStatement_of_restart (retainedPairRestartUntouchedStatement_of_param h12p h13 hD)

/-- Forgetting the untouched word gives PROVE-RLC-D's real joint chart. -/
theorem realJointChartStatement_of_untouched (hR : RealJointChartUntouchedStatement.{u}) :
    RealJointChartStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  obtain ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hdat, hpath⟩ :=
    hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ u r
  refine ⟨S, mS, H₀, Γ₁, Γ₂, U₁, U₂, M, β, X, K, hco, hM, hβ, hX, hK, hlaw, hdat, ?_⟩
  filter_upwards [hpath] with ω hω hord
  obtain ⟨hMω, ψ, hJ, hW, -⟩ := hω hord
  exact ⟨hMω, ψ, hJ, hW⟩

end RLC

end InteractingSLE
