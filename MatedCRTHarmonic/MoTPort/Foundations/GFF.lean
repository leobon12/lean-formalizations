/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.Foundations.Field
import LQGMetric.Field.ZeroBoundary
import LQGMetric.Field.ExistGFF
import LQGMetric.Field.GFFInvariance
import LQGMetric.Field.CircleAvgRate
import LQGMetric.Papers.CONF.S3L35B8
import LQGMetric.Papers.CONF.S3D112N3
import LQGMetric.Field.KilledHeat

/-!
# GFF with boundary data

* `ofFunOn U f : FieldOn U`: the distribution `φ ↦ ∫ φ f` on `U` (mathlib `Distribution.ofFun`;
  junk `0` when `f` is not locally integrable on `U`), the `U`-version of LQGMetric's `ofCont`.
* `IsGFFBoundary U 𝔥 X P`: `X` is a GFF on `U` with (random) harmonic boundary data `𝔥`, i.e.
  `X|_U − 𝔥` is a zero-boundary GFF on `U` in the sense of `LQGMetric.IsZeroBoundaryGFF`
  (Sheffield, *Gaussian free fields for mathematicians*, math/0312099 §2; IG1 §1 / §3.2).
* `exists_isGFFBoundary`: existence for deterministic harmonic data `𝔥` on an open set `U`
  missing some circle, when the zero extension of `𝔥` is locally integrable on `ℂ`
  (e.g. bounded `𝔥`, `exists_isGFFBoundary_of_bounded`). Construction: LQGMetric's whole-plane
  GFF `h` (`GFFExist.exists_wholePlaneGFF`), normalized on the circle, Markov decomposition
  `LQGMetric.CONF.markov_harmPart_dec` (LM Lemma 2.1 transported) gives the zero-boundary part
  `h − G`; add the extension by zero of `𝔥`.

* `NonPolarCompl U`: planar Brownian motion started at any
  point of `U` exits `U` almost surely (the harmonically nontrivial boundary condition of IG4). `IsGFFBoundary U` is only meaningful under this hypothesis (see its
  docstring).

The expression `restrictTo U (X − ofFunOn U 𝔥)` does not typecheck (`ofFunOn U 𝔥` lives on `U`); we use `restrictTo U X − ofFunOn U 𝔥`. Since a
`Field` is a distribution on all of `ℂ`, a field with boundary data `𝔥` exists only when `𝔥` (on `U`)
is the restriction of a distribution on `ℂ`; our existence theorem assumes local integrability
of the zero extension.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions

namespace MatedCRTHarmonic.MoTPort

open LQGMetric

/-- the distribution `φ ↦ ∫ φ f` on the open set `U` (junk `0` if `f` is not locally integrable
on `U`) -/
def ofFunOn (U : Opens ℂ) (f : ℂ → ℝ) : FieldOn U := Distribution.ofFun U f volume ⊤

/-- the distribution on `ℂ` of a function (junk `0` if not locally integrable) -/
def ofFunC (f : ℂ → ℝ) : Field := Distribution.ofFun ⊤ f volume ⊤

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **GFF on `U` with boundary data `𝔥`**: `X` is measurable, `𝔥 ω` is a.s.
harmonic on `U`, and `X|_U − 𝔥` is a zero-boundary GFF on `U`.

**Scope.** (a) The predicate is only meaningful when
`NonPolarCompl U` holds, and every statement using it assumes `NonPolarCompl U` explicitly.
For `U` with polar complement (`U = ℂ`, `ℂ ∖ {pt}`, `ℂ ∖ countable`) LQGMetric's dual Dirichlet
norm is `+∞`, its `toReal` is `0`, so `LQGMetric.IsZeroBoundaryGFF U` is satisfied by the zero
field and the predicate is vacuous (whole-plane objects use `IsWPGFFMod` instead).
(b) For random boundary data `𝔥 : Ω → ℂ → ℝ` it constrains only the **marginal** law of
`X|_U − 𝔥`; it does not say that `X|_U − 𝔥` is independent of `𝔥` (or of anything else). When a
statement needs "a GFF with boundary data `𝔥` given `𝔥`", the independence is stated
separately (or the statement goes through `condDistrib`). -/
def IsGFFBoundary (U : Opens ℂ) (𝔥 : Ω → ℂ → ℝ) (X : Ω → Field) (P : Measure Ω) : Prop :=
  Measurable X ∧ (∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (𝔥 ω) (U : Set ℂ)) ∧
    IsZeroBoundaryGFF U (fun ω => restrictTo U (X ω) - ofFunOn U (𝔥 ω)) P

namespace GFFBdry

lemma ofFunOn_apply {U : Opens ℂ} {f : ℂ → ℝ} (hf : LocallyIntegrableOn f U volume)
    (φ : TestOn U) : ofFunOn U f φ = ∫ x, φ x * f x := by
  rw [ofFunOn, Distribution.ofFun_apply hf]; rfl

/-- restriction of `ofFunC g` to `U` is `ofFunOn U g` -/
lemma restrictTo_ofFunC (U : Opens ℂ) {g : ℂ → ℝ} (hg : LocallyIntegrable g volume) :
    restrictTo U (ofFunC g) = ofFunOn U g := by
  ext φ
  rw [ofFunOn_apply (hg.locallyIntegrableOn _)]
  show ofFunC g (TestFunction.monoCLM ℝ φ) = _
  rw [ofFunC, Distribution.ofFun_apply (hg.locallyIntegrableOn _)]
  simp only [TestFunction.monoCLM_apply, le_refl, le_top, and_self, ite_true, smul_eq_mul]

/-- on `U`, a function and its zero extension define the same distribution -/
lemma ofFunOn_indicator (U : Opens ℂ) (f : ℂ → ℝ) :
    ofFunOn U ((U : Set ℂ).indicator f) = ofFunOn U f :=
  Distribution.ofFun_congr_ae (indicator_ae_eq_restrict U.isOpen.measurableSet)

lemma restrictTo_add (U : Opens ℂ) (a b : Field) :
    restrictTo U (a + b) = restrictTo U a + restrictTo U b := rfl

lemma restrictTo_sub (U : Opens ℂ) (a b : Field) :
    restrictTo U (a - b) = restrictTo U a - restrictTo U b := rfl

lemma measurable_add_const {α : Type*} {mα : MeasurableSpace α} {X : α → Field}
    (hX : Measurable X) (F : Field) : Measurable fun a => X a + F :=
  GFFInv.measurable_distC_iff.2 fun φ =>
    ((GFFInv.measurable_distC_iff.1 hX φ).add_const (F φ) :)

lemma measurable_sub {α : Type*} {mα : MeasurableSpace α} {X Y : α → Field}
    (hX : Measurable X) (hY : Measurable Y) : Measurable fun a => X a - Y a :=
  GFFInv.measurable_distC_iff.2 fun φ =>
    ((GFFInv.measurable_distC_iff.1 hX φ).sub (GFFInv.measurable_distC_iff.1 hY φ) :)

end GFFBdry

open GFFBdry

/-- **Existence of a GFF with deterministic harmonic boundary data** on an open set `U` disjoint
from some circle, for `𝔥` harmonic on `U` whose zero extension is locally integrable. -/
theorem exists_isGFFBoundary (U : Opens ℂ) {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hU : Disjoint (U : Set ℂ) (sphere z₀ ρ)) (𝔥 : ℂ → ℝ)
    (h𝔥 : InnerProductSpace.HarmonicOnNhd 𝔥 (U : Set ℂ))
    (hint : LocallyIntegrable ((U : Set ℂ).indicator 𝔥) volume) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Field),
      IsProbabilityMeasure P ∧ IsGFFBoundary U (fun _ => 𝔥) X P := by
  obtain ⟨Ω, _, P, g, hP, hg⟩ := GFFExist.exists_wholePlaneGFF
  have := hP
  set h : Ω → Field := fun ω => addConst (g ω) (-circleAvg (g ω) ρ z₀)
  have hh : IsWholePlaneGFF h P :=
    IsWholePlaneGFF.addConst hg ((measurable_circleAvg_left ρ z₀).comp hg.measurable).neg
  have hn : ∀ᵐ ω ∂P, circleAvg (h ω) ρ z₀ = 0 := by
    filter_upwards [CircleAvg.ae_tendsto_mollAvg hg z₀ hρ] with ω ⟨a, ha⟩
    rw [CircleAvg.circleAvg_addConst_of_tendsto ha, add_neg_cancel]
  obtain ⟨H, G, hz, -, hGm, hdec, -, hzb, -⟩ :=
    CONF.markov_harmPart_dec hh hρ z₀ hn U.isOpen hU
  have hUo : Blueprint.toOpens (U : Set ℂ) U.isOpen = U := rfl
  rw [hUo] at hzb
  have hhm : Measurable h := hh.measurable
  refine ⟨Ω, inferInstance, P, fun ω => h ω - G ω + ofFunC ((U : Set ℂ).indicator 𝔥), hP,
    measurable_add_const (measurable_sub hhm hGm) _, ae_of_all _ fun _ => h𝔥, ?_⟩
  refine CONF.hlz_isZeroBoundaryGFF_congr hzb ?_ ?_
  · simp only [restrictTo_add, restrictTo_ofFunC U hint, ofFunOn_indicator, add_sub_cancel_right]
    exact (measurable_restrictTo U).comp (measurable_sub hhm hGm)
  · filter_upwards [hdec] with ω hω
    simp only [restrictTo_add, restrictTo_ofFunC U hint, ofFunOn_indicator, add_sub_cancel_right]
    rw [hω, add_sub_cancel_left]

/-- **`ℂ ∖ U` is non-polar** (IG4's "harmonically non-trivial boundary"; STATEMENT_SPEC S-23):
for every `z ∈ U`, a standard planar Brownian motion started at `z` exits `U` almost surely.
Brownian motion is LQGMetric's `KilledHeat.IsPlanarBM` (a.s. continuous centred Gaussian process
with independent coordinates of covariance `min(s,t)`); the condition is required of every such
process on every probability space (the property depends only on the law). -/
def NonPolarCompl (U : Opens ℂ) : Prop :=
  ∀ z ∈ (U : Set ℂ), ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : NNReal → Ω → ℂ),
    IsProbabilityMeasure P → KilledHeat.IsPlanarBM W P →
      ∀ᵐ ω ∂P, ∃ t : NNReal, z + W t ω ∉ (U : Set ℂ)

/-- non-polarity of the complement passes to smaller open sets -/
theorem NonPolarCompl.mono {U V : Opens ℂ} (hVU : V ≤ U) (hU : NonPolarCompl U) :
    NonPolarCompl V := by
  intro z hz Ω _ P W hP hW
  filter_upwards [hU z (hVU hz) Ω P W hP hW] with ω ⟨t, ht⟩
  exact ⟨t, fun h => ht (hVU h)⟩

end MatedCRTHarmonic.MoTPort
