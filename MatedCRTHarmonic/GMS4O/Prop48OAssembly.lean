import MatedCRTHarmonic.GMS4.Prop48Statement

/-!
# Proposition 4.8 without the uniform regularity event

[18] proves Proposition 4.8 on the uniform event `E^ε ⊂ ⋂_{z ∈ B_ρ} F^ε(z)` of Proposition 4.5
, whose degree part needs the
superpolynomial tail of Lemma 4.6. Here the uniform event is replaced by a **per-point truncation
estimate**: for a test pair `(D, f)` with `N = ‖f‖_∞` and a threshold `thr`, let

* `B = {∫⁻_D f(z) 1_{F(z)^c} u_*(z) dz ≤ thr}` (`p48oSmallError`),
* `localEvent z = F(z) ∪ B`, `goodEvent = B ∩ {∫⁻_{B_ρ} u_* < ∞}` (`p48oGood`).

On `goodEvent` every local event holds, so the truncated and untruncated integrals agree; the
record fluctuation differs from the source fluctuation `∫_D f (1_F u_* − m)` by at most `thr`
(`p48o_fluct_sq_le`); and Markov plus Tonelli bound `P(B^c)` by the pointwise truncation errors
`E[1_{F(z)^c} u_*(z)]` (`p48o_smallError_compl_le`). With `thr = ε^{2α} N`:

* `p48o_fixedTestInputs`: the record's lower inputs (`Prop48WholePlaneFixedTestInputs`) follow from
  a pointwise truncation bound `E[1_{F(z)^c} u_*(z)] ≤ C₁ ε^{3α}` (for `z ∈ B_ρ`) and the source
  second-moment bound `E[(∫_D f(1_F u_* − m))²] ≤ C₀ ε^{3α} N²`;
* `p48o_allScalesProducer`: the all-scales producer `GMS4.Prop48WholePlaneAllScalesProducer` of
  the `GMS4/Prop48Statement.lean`, with the exponent chosen before `ρ`.

The conditional mean `m` is any jointly measurable version bounded by the constant `A` of (4.27)
(on the canonical coupling: `p48oCondMeanJoint` of `GMS4O/Prop48OCondMean.lean`).

**Caveats.** (1) The legacy target does not pin the realized density: its realization record fixes
only the domain, test and mean constant, so it is also satisfied by a zero record. The canonical
statement (`GMS4.Canonical.*`) supersedes it; this file records the per-point truncation mechanism.
(2) The pointwise truncation bound needs an unmasked moment of `u_*(z)` (a crude, polynomial-in-`ε⁻¹`
bound uniform over `z ∈ B_ρ` suffices), hence degree moments at single points; it saves the union
bound behind the uniform event of Proposition 4.5, not the degree tails themselves.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4O

open MatedCRTHarmonic.GMS4

/-! ### Fixed-scale data -/

/-- Fixed-scale data of the localized observable of Proposition 4.8 on `(Ω, P)`, for test
pairs supported in `B_ρ(0)`. `uStar` is the density `u_*^ε`, `F z` the local event `F^ε(z)`, and `m`
a version of the conditional mean (4.27), bounded by `A`. -/
structure P48OScaleData {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ρ : ℝ) where
  uStar : Ω → ℂ → ℝ
  F : ℂ → Set Ω
  m : Ω → ℂ → ℝ
  A : ℝ
  measurable_uStar : Measurable fun p : Ω × ℂ => uStar p.1 p.2
  measurableSet_F : MeasurableSet {p : Ω × ℂ | p.1 ∈ F p.2}
  measurable_m : Measurable fun p : Ω × ℂ => m p.1 p.2
  uStar_nonneg : ∀ ω z, 0 ≤ uStar ω z
  m_nonneg : ∀ ω z, 0 ≤ m ω z
  m_le : ∀ ω z, m ω z ≤ A
  ae_lintegral_lt_top :
    ∀ᵐ ω ∂P, ∫⁻ z in ball (0 : ℂ) ρ, ENNReal.ofReal (uStar ω z) < ⊤

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ρ : ℝ}

/-- The test function extended by zero outside `B_ρ(0)`; it is measurable for admissible pairs. -/
def p48oTestExt (ρ : ℝ) (f : ℂ → ℝ) : ℂ → ℝ := (ball (0 : ℂ) ρ).indicator f

lemma measurable_p48oTestExt {f : ℂ → ℝ}
    (hf : Measurable fun z : ball (0 : ℂ) ρ => f z) : Measurable (p48oTestExt ρ f) := by
  refine measurable_of_restrict_of_restrict_compl (measurableSet_ball (x := (0 : ℂ)) (ε := ρ)) ?_ ?_
  · have e : (ball (0 : ℂ) ρ).domRestrict (p48oTestExt ρ f) = fun z : ball (0 : ℂ) ρ => f z := by
      funext z
      simp [p48oTestExt, Set.domRestrict, z.2]
    rw [e]
    exact hf
  · have e : (ball (0 : ℂ) ρ)ᶜ.domRestrict (p48oTestExt ρ f) = fun _ => (0 : ℝ) := by
      funext z
      simp [p48oTestExt, Set.domRestrict, (Set.mem_compl_iff _ _).1 z.2]
    rw [e]
    exact measurable_const

lemma p48oTestExt_eq_of_mem {f : ℂ → ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) :
    p48oTestExt ρ f z = f z := by
  simp [p48oTestExt, hz]

/-- The pointwise truncation error `f(z) 1_{F(z)^c} u_*(z)`. -/
def p48oTruncIntegrand (S : P48OScaleData P ρ) (f : ℂ → ℝ) (ω : Ω) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (p48oTestExt ρ f z * (S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω)

lemma measurable_p48oTruncIntegrand (S : P48OScaleData P ρ) {f : ℂ → ℝ}
    (hf : Measurable fun z : ball (0 : ℂ) ρ => f z) :
    Measurable fun p : Ω × ℂ => p48oTruncIntegrand S f p.1 p.2 := by
  refine ENNReal.measurable_ofReal.comp
    (((measurable_p48oTestExt hf).comp measurable_snd).mul ?_)
  have hFc : MeasurableSet {p : Ω × ℂ | p.1 ∈ (S.F p.2)ᶜ} := S.measurableSet_F.compl
  have e : (fun p : Ω × ℂ => (S.F p.2)ᶜ.indicator (fun ω' => S.uStar ω' p.2) p.1) =
      {p : Ω × ℂ | p.1 ∈ (S.F p.2)ᶜ}.indicator (fun p => S.uStar p.1 p.2) := by
    funext p
    by_cases hp : p.1 ∈ (S.F p.2)ᶜ
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ {p : Ω × ℂ |
        p.1 ∈ (S.F p.2)ᶜ} from hp)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ {p : Ω × ℂ |
        p.1 ∈ (S.F p.2)ᶜ} from hp)]
  rw [e]
  exact S.measurable_uStar.indicator hFc

/-- The truncation error `∫⁻_D f 1_{F^c} u_*`. -/
def p48oTruncError (S : P48OScaleData P ρ) (D : Set ℂ) (f : ℂ → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ z in D, p48oTruncIntegrand S f ω z

/-- The event that the truncation error is at most `thr`. -/
def p48oSmallError (S : P48OScaleData P ρ) (D : Set ℂ) (f : ℂ → ℝ) (thr : ℝ) : Set Ω :=
  {ω | p48oTruncError S D f ω ≤ ENNReal.ofReal thr}

/-- The event that the untruncated density is integrable over `B_ρ(0)`. -/
def p48oIntegrableSet (S : P48OScaleData P ρ) : Set Ω :=
  {ω | ∫⁻ z in ball (0 : ℂ) ρ, ENNReal.ofReal (S.uStar ω z) < ⊤}

/-- The good event. -/
def p48oGood (S : P48OScaleData P ρ) (D : Set ℂ) (f : ℂ → ℝ) (thr : ℝ) : Set Ω :=
  p48oSmallError S D f thr ∩ p48oIntegrableSet S

/-- The local events of the record: `F(z) ∪ B`. -/
def p48oLocalEvent (S : P48OScaleData P ρ) (D : Set ℂ) (f : ℂ → ℝ) (thr : ℝ) (z : ℂ) :
    Set Ω :=
  S.F z ∪ p48oSmallError S D f thr

lemma measurable_p48oTruncError (S : P48OScaleData P ρ) (D : Set ℂ) {f : ℂ → ℝ}
    (hf : Measurable fun z : ball (0 : ℂ) ρ => f z) :
    Measurable (p48oTruncError S D f) :=
  (measurable_p48oTruncIntegrand S hf).lintegral_prod_right'

lemma measurableSet_p48oSmallError (S : P48OScaleData P ρ) (D : Set ℂ) {f : ℂ → ℝ}
    (hf : Measurable fun z : ball (0 : ℂ) ρ => f z) (thr : ℝ) :
    MeasurableSet (p48oSmallError S D f thr) :=
  measurableSet_le (measurable_p48oTruncError S D hf) measurable_const

lemma measurableSet_p48oIntegrableSet (S : P48OScaleData P ρ) :
    MeasurableSet (p48oIntegrableSet S) := by
  have hm : Measurable fun ω => ∫⁻ z in ball (0 : ℂ) ρ, ENNReal.ofReal (S.uStar ω z) :=
    (ENNReal.measurable_ofReal.comp S.measurable_uStar).lintegral_prod_right'
  exact measurableSet_lt hm measurable_const

lemma measurableSet_p48oGood (S : P48OScaleData P ρ) (D : Set ℂ) {f : ℂ → ℝ}
    (hf : Measurable fun z : ball (0 : ℂ) ρ => f z) (thr : ℝ) :
    MeasurableSet (p48oGood S D f thr) :=
  (measurableSet_p48oSmallError S D hf thr).inter (measurableSet_p48oIntegrableSet S)

/-! ### The localized observable record

The source's test functions are measurable on `B_ρ(0) ⊂ ℂ`. Since the c10 repair this is the
admissibility clause `Prop48TestPairAdmissible.test_measurable` (it previously ranged over
`Metric.ball (0 : ℕ) ρ` and was vacuous); `P48OTestMeasurable` names the same statement. -/

/-- The source's measurability of a test function: measurable on `B_ρ(0) ⊂ ℂ`. -/
def P48OTestMeasurable (ρ : ℝ) (f : ℂ → ℝ) : Prop :=
  Measurable fun z : ball (0 : ℂ) ρ => f z

lemma Prop48TestPairAdmissible.p48oTestMeasurable {ρ : ℝ} {D : Set ℂ} {f : ℂ → ℝ}
    (hadm : Prop48TestPairAdmissible ρ D f) : P48OTestMeasurable ρ f :=
  hadm.test_measurable

section Record

variable (S : P48OScaleData P ρ) {D : Set ℂ} {f : ℂ → ℝ}

lemma p48o_volume_lt_top_of_admissible (hadm : Prop48TestPairAdmissible ρ D f) :
    volume D < ⊤ :=
  (measure_mono hadm.domain_subset_ball).trans_lt measure_ball_lt_top

lemma p48o_abs_test_le (hadm : Prop48TestPairAdmissible ρ D f) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) ρ) : |f z| ≤ prop48TestSupNorm ρ f :=
  abs_le_prop48TestSupNorm hadm.test_bounded hz

lemma p48o_test_nonneg (hadm : Prop48TestPairAdmissible ρ D f) {z : ℂ} (hz : z ∈ D) :
    0 ≤ f z :=
  hadm.test_nonnegative z (hadm.domain_subset_ball hz)

/-- `f · g` is integrable on `D` for bounded measurable `g`. -/
lemma p48o_integrableOn_test_mul (hadm : Prop48TestPairAdmissible ρ D f)
    (hfm : P48OTestMeasurable ρ f) {g : ℂ → ℝ}
    (hg : Measurable g) {M : ℝ} (hgM : ∀ z, |g z| ≤ M) :
    IntegrableOn (fun z => f z * g z) D := by
  have hint : IntegrableOn (fun z => p48oTestExt ρ f z * g z) D := by
    refine IntegrableOn.of_bound (p48o_volume_lt_top_of_admissible hadm)
      (((measurable_p48oTestExt hfm).mul hg).aestronglyMeasurable)
      (prop48TestSupNorm ρ f * M) ?_
    refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_mul, p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
    exact mul_le_mul (p48o_abs_test_le hadm (hadm.domain_subset_ball hz)) (hgM z)
      (abs_nonneg _) ((abs_nonneg _).trans (p48o_abs_test_le hadm (hadm.domain_subset_ball hz)))
  refine hint.congr_fun (fun z hz => ?_) hadm.domain_borel
  simp only
  rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]

/-- `f · u_*(ω, ·)` is integrable on `D` on the integrability event. -/
lemma p48o_integrableOn_test_mul_uStar (hadm : Prop48TestPairAdmissible ρ D f)
    (hfm : P48OTestMeasurable ρ f) {ω : Ω} (hω : ω ∈ p48oIntegrableSet S) :
    IntegrableOn (fun z => f z * S.uStar ω z) D := by
  have hu : Measurable fun z => S.uStar ω z :=
    S.measurable_uStar.comp (measurable_const.prodMk measurable_id)
  have huint : IntegrableOn (fun z => S.uStar ω z) (ball (0 : ℂ) ρ) := by
    refine ⟨hu.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have e : (fun z => ‖S.uStar ω z‖ₑ) = fun z => ENNReal.ofReal (S.uStar ω z) := by
      funext z
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (S.uStar_nonneg ω z)]
    rw [e]
    exact hω
  have huD : IntegrableOn (fun z => S.uStar ω z) D := huint.mono_set hadm.domain_subset_ball
  have hdom : Integrable (fun z => prop48TestSupNorm ρ f * S.uStar ω z) (volume.restrict D) :=
    huD.const_mul _
  refine hdom.mono' ?_ ?_
  · have hext : Measurable fun z => p48oTestExt ρ f z * S.uStar ω z :=
      (measurable_p48oTestExt hfm).mul hu
    refine hext.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    simp only
    rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
  · refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (S.uStar_nonneg ω z)]
    exact mul_le_mul_of_nonneg_right (p48o_abs_test_le hadm (hadm.domain_subset_ball hz))
      (S.uStar_nonneg ω z)

/-- The joint indicator of the record's local events. -/
lemma p48o_measurable_localEvent_indicator (hfm : P48OTestMeasurable ρ f) (thr : ℝ) :
    Measurable fun p : Ω × ℂ =>
      (p48oLocalEvent S D f thr p.2).indicator (fun ω' => S.uStar ω' p.2) p.1 := by
  have hset : MeasurableSet {p : Ω × ℂ | p.1 ∈ p48oLocalEvent S D f thr p.2} := by
    have h2 : MeasurableSet {p : Ω × ℂ | p.1 ∈ p48oSmallError S D f thr} :=
      measurable_fst (measurableSet_p48oSmallError S D hfm thr)
    exact S.measurableSet_F.union h2
  have e : (fun p : Ω × ℂ =>
      (p48oLocalEvent S D f thr p.2).indicator (fun ω' => S.uStar ω' p.2) p.1) =
      {p : Ω × ℂ | p.1 ∈ p48oLocalEvent S D f thr p.2}.indicator
        (fun p => S.uStar p.1 p.2) := by
    funext p
    by_cases hp : p.1 ∈ p48oLocalEvent S D f thr p.2
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ {p : Ω × ℂ |
        p.1 ∈ p48oLocalEvent S D f thr p.2} from hp)]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show p ∉ {p : Ω × ℂ |
        p.1 ∈ p48oLocalEvent S D f thr p.2} from hp)]
  rw [e]
  exact S.measurable_uStar.indicator hset

lemma p48o_aemeasurable_fluct (hadm : Prop48TestPairAdmissible ρ D f)
    (hfm : P48OTestMeasurable ρ f) (thr : ℝ) :
    AEMeasurable (fun ω => ∫ z in D, f z *
      ((p48oLocalEvent S D f thr z).indicator (fun _ => S.uStar ω z) ω - S.m ω z)) P := by
  have hG : Measurable fun p : Ω × ℂ => p48oTestExt ρ f p.2 *
      ((p48oLocalEvent S D f thr p.2).indicator (fun ω' => S.uStar ω' p.2) p.1 - S.m p.1 p.2) :=
    ((measurable_p48oTestExt hfm).comp measurable_snd).mul
      ((p48o_measurable_localEvent_indicator S hfm thr).sub S.measurable_m)
  have hsm := hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict D)
  refine hsm.measurable.aemeasurable.congr (Eventually.of_forall fun ω => ?_)
  refine (setIntegral_congr_fun hadm.domain_borel fun z hz => ?_)
  simp only
  rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
  by_cases hmem : ω ∈ p48oLocalEvent S D f thr z
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

lemma p48o_condIntegral_le (hadm : Prop48TestPairAdmissible ρ D f)
    (hfm : P48OTestMeasurable ρ f) (ω : Ω) :
    (∫ z in D, f z * S.m ω z) ≤ S.A * ∫ z in D, f z := by
  have hm : Measurable fun z => S.m ω z :=
    S.measurable_m.comp (measurable_const.prodMk measurable_id)
  have h1 : IntegrableOn (fun z => f z * S.m ω z) D :=
    p48o_integrableOn_test_mul hadm hfm hm (M := S.A) fun z => by
      rw [abs_of_nonneg (S.m_nonneg ω z)]; exact S.m_le ω z
  have h2 : IntegrableOn (fun z => f z * S.A) D :=
    p48o_integrableOn_test_mul hadm hfm measurable_const (M := |S.A|) fun _ => le_rfl
  calc (∫ z in D, f z * S.m ω z) ≤ ∫ z in D, f z * S.A :=
        setIntegral_mono_on h1 h2 hadm.domain_borel fun z hz =>
          mul_le_mul_of_nonneg_left (S.m_le ω z) (p48o_test_nonneg hadm hz)
    _ = S.A * ∫ z in D, f z := by
        rw [integral_mul_const, mul_comm]

lemma p48o_integral_subtraction (hadm : Prop48TestPairAdmissible ρ D f)
    (hfm : P48OTestMeasurable ρ f) (thr : ℝ) {ω : Ω}
    (hω : ω ∈ p48oGood S D f thr) :
    (∫ z in D, f z *
      ((p48oLocalEvent S D f thr z).indicator (fun _ => S.uStar ω z) ω - S.m ω z)) =
      (∫ z in D, f z * (p48oLocalEvent S D f thr z).indicator (fun _ => S.uStar ω z) ω) -
      ∫ z in D, f z * S.m ω z := by
  have hind : ∀ z, (p48oLocalEvent S D f thr z).indicator (fun _ => S.uStar ω z) ω =
      S.uStar ω z := fun z =>
    Set.indicator_of_mem (show ω ∈ p48oLocalEvent S D f thr z from Or.inr hω.1) _
  have hm : Measurable fun z => S.m ω z :=
    S.measurable_m.comp (measurable_const.prodMk measurable_id)
  have h1 : IntegrableOn (fun z => f z *
      (p48oLocalEvent S D f thr z).indicator (fun _ => S.uStar ω z) ω) D := by
    simp only [hind]
    exact p48o_integrableOn_test_mul_uStar S hadm hfm hω.2
  have h2 : IntegrableOn (fun z => f z * S.m ω z) D :=
    p48o_integrableOn_test_mul hadm hfm hm (M := S.A) fun z => by
      rw [abs_of_nonneg (S.m_nonneg ω z)]; exact S.m_le ω z
  simp only [mul_sub]
  exact integral_sub h1 h2

/-- **The record of [18] Proposition 4.8 for one test pair**, with the per-point truncation event
in place of the uniform regularity event. -/
def p48oObservable (hadm : Prop48TestPairAdmissible ρ D f) (hfm : P48OTestMeasurable ρ f)
    (thr : ℝ) : Prop48LocalizedObservable P where
  domain := D
  measurableSet_domain := hadm.domain_borel
  test := f
  uStar := S.uStar
  localEvent := p48oLocalEvent S D f thr
  conditionalMean := S.m
  goodEvent := p48oGood S D f thr
  meanConstant := S.A
  aeMeasurable_fluctuation := p48o_aemeasurable_fluct S hadm hfm thr
  localEvent_of_good := fun _ hω _ _ => Or.inr hω.1
  conditionalIntegral_le := fun ω _ => p48o_condIntegral_le S hadm hfm ω
  integral_subtraction := fun _ hω => p48o_integral_subtraction S hadm hfm thr hω

end Record

/-! ### The two estimates -/

section Estimates

variable (S : P48OScaleData P ρ) {D : Set ℂ} {f : ℂ → ℝ}

/-- The source fluctuation `∫_D f (1_F u_* − m)` of [18] (4.28)–(4.29). -/
def p48oSourceFluct (S : P48OScaleData P ρ) (D : Set ℂ) (f : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ z in D, f z * ((S.F z).indicator (fun ω' => S.uStar ω' z) ω - S.m ω z)

lemma p48o_volume_le_pi (hadm : Prop48TestPairAdmissible ρ D f) (hρ : ρ ≤ 1) :
    volume D ≤ ENNReal.ofReal Real.pi := by
  calc volume D ≤ volume (ball (0 : ℂ) 1) :=
        measure_mono (hadm.domain_subset_ball.trans (ball_subset_ball hρ))
    _ = ENNReal.ofReal Real.pi := by
        rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul, ← NNReal.coe_real_pi,
          ENNReal.ofReal_coe_nnreal]

lemma p48o_measurable_sectionF (ω : Ω) :
    MeasurableSet {z : ℂ | ω ∈ S.F z} :=
  measurable_prodMk_left S.measurableSet_F

lemma p48o_measurable_indicatorF_section (ω : Ω) :
    Measurable fun z => (S.F z).indicator (fun ω' => S.uStar ω' z) ω := by
  have hu : Measurable fun z => S.uStar ω z :=
    S.measurable_uStar.comp (measurable_const.prodMk measurable_id)
  have e : (fun z => (S.F z).indicator (fun ω' => S.uStar ω' z) ω) =
      {z : ℂ | ω ∈ S.F z}.indicator (fun z => S.uStar ω z) := by
    funext z
    by_cases hz : ω ∈ S.F z
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ {z : ℂ | ω ∈ S.F z} from hz)]
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (show z ∉ {z : ℂ | ω ∈ S.F z} from hz)]
  rw [e]
  exact hu.indicator (p48o_measurable_sectionF S ω)

lemma p48o_measurable_indicatorFc_section (ω : Ω) :
    Measurable fun z => (S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω := by
  have hu : Measurable fun z => S.uStar ω z :=
    S.measurable_uStar.comp (measurable_const.prodMk measurable_id)
  have e : (fun z => (S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω) =
      {z : ℂ | ω ∈ S.F z}ᶜ.indicator (fun z => S.uStar ω z) := by
    funext z
    by_cases hz : ω ∈ (S.F z)ᶜ
    · rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem (show z ∈ {z : ℂ | ω ∈ S.F z}ᶜ from hz)]
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem (show z ∉ {z : ℂ | ω ∈ S.F z}ᶜ from hz)]
  rw [e]
  exact hu.indicator (p48o_measurable_sectionF S ω).compl

/-- A dominated part of `f · u_*(ω,·)` is integrable on `D`. -/
lemma p48o_integrableOn_dominated (hadm : Prop48TestPairAdmissible ρ D f)
    (hfm : P48OTestMeasurable ρ f) {ω : Ω} (hω : ω ∈ p48oIntegrableSet S)
    {g : ℂ → ℝ} (hg : Measurable g) (hg0 : ∀ z, 0 ≤ g z) (hgu : ∀ z, g z ≤ S.uStar ω z) :
    IntegrableOn (fun z => f z * g z) D := by
  have hdom := p48o_integrableOn_test_mul_uStar S hadm hfm hω
  refine hdom.mono' ?_ ?_
  · have hext : Measurable fun z => p48oTestExt ρ f z * g z :=
      (measurable_p48oTestExt hfm).mul hg
    refine hext.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    simp only
    rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
  · refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    have hf0 := p48o_test_nonneg hadm hz
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf0 (hg0 z))]
    exact mul_le_mul_of_nonneg_left (hgu z) hf0

/-- **The record fluctuation is the source fluctuation up to the truncation threshold.** -/
lemma p48o_fluct_sq_le_of_mem (hadm : Prop48TestPairAdmissible ρ D f)
    (hfm : P48OTestMeasurable ρ f) {thr : ℝ} (hthr : 0 ≤ thr) {ω : Ω}
    (hω : ω ∈ p48oIntegrableSet S) :
    (p48oObservable S hadm hfm thr).fluctuation ω ^ 2 ≤
      2 * p48oSourceFluct S D f ω ^ 2 + 2 * thr ^ 2 := by
  have hm : Measurable fun z => S.m ω z :=
    S.measurable_m.comp (measurable_const.prodMk measurable_id)
  have hfmI : IntegrableOn (fun z => f z * S.m ω z) D :=
    p48o_integrableOn_test_mul hadm hfm hm (M := S.A) fun z => by
      rw [abs_of_nonneg (S.m_nonneg ω z)]; exact S.m_le ω z
  change (∫ z in D, f z *
      ((p48oLocalEvent S D f thr z).indicator (fun _ => S.uStar ω z) ω - S.m ω z)) ^ 2 ≤ _
  by_cases hB : ω ∈ p48oSmallError S D f thr
  · -- on the small-error event every local event holds
    have hind : ∀ z, (p48oLocalEvent S D f thr z).indicator (fun _ => S.uStar ω z) ω =
        S.uStar ω z := fun z =>
      Set.indicator_of_mem (show ω ∈ p48oLocalEvent S D f thr z from Or.inr hB) _
    simp only [hind]
    set gF : ℂ → ℝ := fun z => (S.F z).indicator (fun ω' => S.uStar ω' z) ω
    set gFc : ℂ → ℝ := fun z => (S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω
    have hsplit : ∀ z, S.uStar ω z = gF z + gFc z := by
      intro z
      simp only [gF, gFc]
      by_cases hz : ω ∈ S.F z
      · rw [Set.indicator_of_mem hz, Set.indicator_of_notMem (show ω ∉ (S.F z)ᶜ from
          fun h => h hz), add_zero]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_mem (show ω ∈ (S.F z)ᶜ from hz),
          zero_add]
    have hgF0 : ∀ z, 0 ≤ gF z := fun z => Set.indicator_nonneg (fun _ _ => S.uStar_nonneg _ _) _
    have hgFc0 : ∀ z, 0 ≤ gFc z :=
      fun z => Set.indicator_nonneg (fun _ _ => S.uStar_nonneg _ _) _
    have hIF : IntegrableOn (fun z => f z * gF z) D :=
      p48o_integrableOn_dominated S hadm hfm hω (p48o_measurable_indicatorF_section S ω) hgF0
        fun z => by rw [hsplit z]; linarith [hgFc0 z]
    have hIFc : IntegrableOn (fun z => f z * gFc z) D :=
      p48o_integrableOn_dominated S hadm hfm hω (p48o_measurable_indicatorFc_section S ω) hgFc0
        fun z => by rw [hsplit z]; linarith [hgF0 z]
    set e : ℝ := ∫ z in D, f z * gFc z with he
    have hfluct : (∫ z in D, f z * (S.uStar ω z - S.m ω z)) = p48oSourceFluct S D f ω + e := by
      calc (∫ z in D, f z * (S.uStar ω z - S.m ω z))
          = ∫ z in D, ((f z * gF z - f z * S.m ω z) + f z * gFc z) := by
            congr 1
            funext z
            rw [hsplit z]
            ring
        _ = (∫ z in D, (f z * gF z - f z * S.m ω z)) + ∫ z in D, f z * gFc z :=
            integral_add (hIF.sub hfmI) hIFc
        _ = p48oSourceFluct S D f ω + e := by
            rw [he, p48oSourceFluct]
            congr 1
            congr 1
            funext z
            simp only [gF]
            ring
    have he0 : 0 ≤ e := setIntegral_nonneg hadm.domain_borel fun z hz =>
      mul_nonneg (p48o_test_nonneg hadm hz) (hgFc0 z)
    have hele : e ≤ thr := by
      have hlin : ENNReal.ofReal e = p48oTruncError S D f ω := by
        rw [he, ofReal_integral_eq_lintegral_ofReal hIFc
          ((ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz =>
            mul_nonneg (p48o_test_nonneg hadm hz) (hgFc0 z))), p48oTruncError]
        refine setLIntegral_congr_fun hadm.domain_borel fun z hz => ?_
        simp only [p48oTruncIntegrand, gFc]
        rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
      have h := hB
      simp only [p48oSmallError, Set.mem_ofPred_eq, ← hlin] at h
      exact (ENNReal.ofReal_le_ofReal_iff hthr).1 h
    rw [hfluct]
    nlinarith [sq_nonneg (p48oSourceFluct S D f ω - e)]
  · -- off the small-error event the record and source integrands coincide
    have hind : ∀ z, (p48oLocalEvent S D f thr z).indicator (fun _ => S.uStar ω z) ω =
        (S.F z).indicator (fun ω' => S.uStar ω' z) ω := by
      intro z
      by_cases hz : ω ∈ S.F z
      · rw [Set.indicator_of_mem (show ω ∈ p48oLocalEvent S D f thr z from Or.inl hz),
          Set.indicator_of_mem hz]
      · have hz' : ω ∉ p48oLocalEvent S D f thr z := fun h => h.elim hz hB
        rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]
    simp only [hind]
    change p48oSourceFluct S D f ω ^ 2 ≤ _
    nlinarith [sq_nonneg (p48oSourceFluct S D f ω), sq_nonneg thr]

/-- **Second moment of the record fluctuation.** -/
theorem p48o_lintegral_fluct_sq_le [IsProbabilityMeasure P]
    (hadm : Prop48TestPairAdmissible ρ D f) (hfm : P48OTestMeasurable ρ f)
    {thr : ℝ} (hthr : 0 ≤ thr) :
    ∫⁻ ω, ENNReal.ofReal ((p48oObservable S hadm hfm thr).fluctuation ω ^ 2) ∂P ≤
      2 * ∫⁻ ω, ENNReal.ofReal (p48oSourceFluct S D f ω ^ 2) ∂P +
        ENNReal.ofReal (2 * thr ^ 2) := by
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal ((p48oObservable S hadm hfm thr).fluctuation ω ^ 2) ≤
      2 * ENNReal.ofReal (p48oSourceFluct S D f ω ^ 2) + ENNReal.ofReal (2 * thr ^ 2) := by
    filter_upwards [S.ae_lintegral_lt_top] with ω hω
    have h := p48o_fluct_sq_le_of_mem S hadm hfm hthr (ω := ω) hω
    calc ENNReal.ofReal ((p48oObservable S hadm hfm thr).fluctuation ω ^ 2) ≤
          ENNReal.ofReal (2 * p48oSourceFluct S D f ω ^ 2 + 2 * thr ^ 2) :=
          ENNReal.ofReal_le_ofReal h
      _ = 2 * ENNReal.ofReal (p48oSourceFluct S D f ω ^ 2) + ENNReal.ofReal (2 * thr ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num)]
          norm_num
  calc ∫⁻ ω, ENNReal.ofReal ((p48oObservable S hadm hfm thr).fluctuation ω ^ 2) ∂P ≤
        ∫⁻ ω, (2 * ENNReal.ofReal (p48oSourceFluct S D f ω ^ 2) +
          ENNReal.ofReal (2 * thr ^ 2)) ∂P := lintegral_mono_ae hpt
    _ = 2 * ∫⁻ ω, ENNReal.ofReal (p48oSourceFluct S D f ω ^ 2) ∂P +
          ENNReal.ofReal (2 * thr ^ 2) := by
        rw [lintegral_add_right' _ aemeasurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (by norm_num)]

/-- **Markov bound for the small-error event** from pointwise truncation errors. -/
theorem p48o_smallError_compl_le [IsProbabilityMeasure P]
    (hadm : Prop48TestPairAdmissible ρ D f) (hfm : P48OTestMeasurable ρ f) (hρ : ρ ≤ 1)
    {thr c : ℝ} (hthr : 0 < thr) (hc : 0 ≤ c)
    (hH1 : ∀ z ∈ ball (0 : ℂ) ρ,
      ∫⁻ ω, ENNReal.ofReal ((S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω) ∂P ≤
        ENNReal.ofReal c) :
    P (p48oSmallError S D f thr)ᶜ ≤
      ENNReal.ofReal (prop48TestSupNorm ρ f * c * Real.pi / thr) := by
  set N : ℝ := prop48TestSupNorm ρ f with hN
  have hN0 : 0 ≤ N := by
    have h := abs_le_prop48TestSupNorm (z := 0) hadm.test_bounded
    by_cases hρ0 : 0 < ρ
    · exact (abs_nonneg _).trans (h (mem_ball_self hρ0))
    · rw [hN, prop48TestSupNorm]
      apply le_csSup (prop48TestSupNorm_bddAbove hadm.test_bounded)
      exact Set.mem_insert 0 _
  have hT : Measurable (p48oTruncError S D f) := measurable_p48oTruncError S D hfm
  have hsub : (p48oSmallError S D f thr)ᶜ ⊆ {ω | ENNReal.ofReal thr ≤ p48oTruncError S D f ω} := by
    intro ω hω
    simp only [p48oSmallError, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    exact hω.le
  have hmarkov := mul_meas_ge_le_lintegral₀ hT.aemeasurable (ENNReal.ofReal thr) (μ := P)
  have hint : ∫⁻ ω, p48oTruncError S D f ω ∂P ≤
      ENNReal.ofReal N * ENNReal.ofReal c * ENNReal.ofReal Real.pi := by
    have hswap : ∫⁻ ω, p48oTruncError S D f ω ∂P =
        ∫⁻ z in D, ∫⁻ ω, p48oTruncIntegrand S f ω z ∂P := by
      unfold p48oTruncError
      exact lintegral_lintegral_swap
        ((measurable_p48oTruncIntegrand S hfm).aemeasurable)
    rw [hswap]
    calc ∫⁻ z in D, ∫⁻ ω, p48oTruncIntegrand S f ω z ∂P ≤
          ∫⁻ _z in D, ENNReal.ofReal N * ENNReal.ofReal c := by
          refine setLIntegral_mono measurable_const fun z hz => ?_
          have hzb := hadm.domain_subset_ball hz
          calc ∫⁻ ω, p48oTruncIntegrand S f ω z ∂P ≤
                ∫⁻ ω, ENNReal.ofReal N *
                  ENNReal.ofReal ((S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω) ∂P := by
                refine lintegral_mono fun ω => ?_
                rw [p48oTruncIntegrand, ← ENNReal.ofReal_mul hN0]
                refine ENNReal.ofReal_le_ofReal ?_
                have hnn : 0 ≤ (S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω :=
                  Set.indicator_nonneg (fun _ _ => S.uStar_nonneg _ _) _
                rw [p48oTestExt_eq_of_mem hzb]
                exact mul_le_mul_of_nonneg_right
                  ((le_abs_self _).trans (p48o_abs_test_le hadm hzb)) hnn
            _ = ENNReal.ofReal N * ∫⁻ ω,
                  ENNReal.ofReal ((S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω) ∂P :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
            _ ≤ ENNReal.ofReal N * ENNReal.ofReal c := by gcongr; exact hH1 z hzb
      _ = ENNReal.ofReal N * ENNReal.ofReal c * volume D := by
          rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal N * ENNReal.ofReal c * ENNReal.ofReal Real.pi := by
          gcongr; exact p48o_volume_le_pi hadm hρ
  have hthr' : ENNReal.ofReal thr ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hthr
  calc P (p48oSmallError S D f thr)ᶜ ≤ P {ω | ENNReal.ofReal thr ≤ p48oTruncError S D f ω} :=
        measure_mono hsub
    _ ≤ (ENNReal.ofReal N * ENNReal.ofReal c * ENNReal.ofReal Real.pi) / ENNReal.ofReal thr := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hthr') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact hmarkov.trans hint
    _ = ENNReal.ofReal (N * c * Real.pi / thr) := by
        rw [← ENNReal.ofReal_mul hN0, ← ENNReal.ofReal_mul (mul_nonneg hN0 hc),
          ENNReal.ofReal_div_of_pos hthr]

end Estimates

/-! ### Fixed-scale bounds and the producers -/

/-- The two analytic inputs at one scale: pointwise truncation errors and the source second
moment ([18] (4.30)–(4.38), with the unconditional second-moment correction: no global-event indicator). -/
structure P48OScaleBounds (S : P48OScaleData P ρ) (ε α C₀ C₁ : ℝ) : Prop where
  trunc : ∀ z ∈ ball (0 : ℂ) ρ,
    ∫⁻ ω, ENNReal.ofReal ((S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω) ∂P ≤
      ENNReal.ofReal (C₁ * ε ^ (3 * α))
  secondMoment : ∀ (D : Set ℂ) (f : ℂ → ℝ), Prop48TestPairAdmissible ρ D f →
    ∫⁻ ω, ENNReal.ofReal (p48oSourceFluct S D f ω ^ 2) ∂P ≤
      ENNReal.ofReal (C₀ * ε ^ (3 * α) * prop48TestSupNorm ρ f ^ 2)

section Producer

variable {R : GMSA.WholePlaneRootedLQGLaw Ω}

lemma p48o_testSupNorm_nonneg {D : Set ℂ} {f : ℂ → ℝ} (hadm : Prop48TestPairAdmissible ρ D f) :
    0 ≤ prop48TestSupNorm ρ f := by
  rw [prop48TestSupNorm]
  apply le_csSup (prop48TestSupNorm_bddAbove hadm.test_bounded)
  exact Set.mem_insert 0 _

lemma p48o_test_eq_zero_of_norm_zero {D : Set ℂ} {f : ℂ → ℝ}
    (hadm : Prop48TestPairAdmissible ρ D f) (hN : prop48TestSupNorm ρ f = 0) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) ρ) : f z = 0 := by
  have h := p48o_abs_test_le hadm hz
  rw [hN] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

/-- The good event's complement for the concrete record. -/
theorem p48o_good_compl_le (S : P48OScaleData R.unrootedLaw ρ) {D : Set ℂ} {f : ℂ → ℝ}
    (hadm : Prop48TestPairAdmissible ρ D f) (hfm : P48OTestMeasurable ρ f) (hρ : ρ ≤ 1)
    {ε α C₁ : ℝ} (hε : 0 < ε) (hC₁ : 0 ≤ C₁)
    (htrunc : ∀ z ∈ ball (0 : ℂ) ρ,
      ∫⁻ ω, ENNReal.ofReal ((S.F z)ᶜ.indicator (fun ω' => S.uStar ω' z) ω) ∂(R.unrootedLaw) ≤
        ENNReal.ofReal (C₁ * ε ^ (3 * α))) :
    R.unrootedLaw (p48oGood S D f (ε ^ (2 * α) * prop48TestSupNorm ρ f))ᶜ ≤
      ENNReal.ofReal (Real.pi * C₁ * ε ^ α) := by
  have : IsProbabilityMeasure R.unrootedLaw := R.unrootedLaw_isProbability
  set N : ℝ := prop48TestSupNorm ρ f with hN
  have hN0 : 0 ≤ N := p48o_testSupNorm_nonneg hadm
  have hI : R.unrootedLaw (p48oIntegrableSet S)ᶜ = 0 := by
    have h := S.ae_lintegral_lt_top
    rw [ae_iff] at h
    exact h
  have hgood : (p48oGood S D f (ε ^ (2 * α) * N))ᶜ ⊆
      (p48oSmallError S D f (ε ^ (2 * α) * N))ᶜ ∪ (p48oIntegrableSet S)ᶜ := by
    intro ω hω
    simp only [p48oGood, Set.compl_inter, Set.mem_union] at hω
    exact hω
  have hpos : 0 ≤ Real.pi * C₁ * ε ^ α := by positivity
  calc R.unrootedLaw (p48oGood S D f (ε ^ (2 * α) * N))ᶜ ≤
        R.unrootedLaw (p48oSmallError S D f (ε ^ (2 * α) * N))ᶜ +
          R.unrootedLaw (p48oIntegrableSet S)ᶜ :=
        (measure_mono hgood).trans (measure_union_le _ _)
    _ = R.unrootedLaw (p48oSmallError S D f (ε ^ (2 * α) * N))ᶜ := by rw [hI, add_zero]
    _ ≤ ENNReal.ofReal (Real.pi * C₁ * ε ^ α) := by
        rcases eq_or_lt_of_le hN0 with hN' | hN'
        · -- zero test function: the truncation error vanishes
          have hempty : (p48oSmallError S D f (ε ^ (2 * α) * N))ᶜ = ∅ := by
            ext ω
            simp only [Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
            change p48oTruncError S D f ω ≤ _
            have h0 : p48oTruncError S D f ω = 0 := by
              unfold p48oTruncError
              refine (setLIntegral_congr_fun hadm.domain_borel fun z hz => ?_).trans
                (lintegral_zero)
              rw [p48oTruncIntegrand, p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz),
                p48o_test_eq_zero_of_norm_zero hadm hN'.symm (hadm.domain_subset_ball hz),
                zero_mul, ENNReal.ofReal_zero]
            rw [h0]
            exact zero_le
          rw [hempty, measure_empty]
          exact zero_le
        · have hthr : 0 < ε ^ (2 * α) * N := mul_pos (Real.rpow_pos_of_pos hε _) hN'
          have h := p48o_smallError_compl_le S hadm hfm hρ hthr
            (by positivity : (0 : ℝ) ≤ C₁ * ε ^ (3 * α)) htrunc
          refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
          rw [← hN]
          have hε2 : ε ^ (2 * α) ≠ 0 := (Real.rpow_pos_of_pos hε _).ne'
          have hsplit : ε ^ (3 * α) = ε ^ (2 * α) * ε ^ α := by
            rw [← Real.rpow_add hε]; ring_nf
          rw [hsplit]
          field_simp

lemma p48o_measurable_localizedIntegral (S : P48OScaleData P ρ) {D : Set ℂ} {f : ℂ → ℝ}
    (hadm : Prop48TestPairAdmissible ρ D f) (hfm : P48OTestMeasurable ρ f) :
    Measurable fun ω => ∫ z in D, f z * S.uStar ω z := by
  have hG : Measurable fun p : Ω × ℂ => p48oTestExt ρ f p.2 * S.uStar p.1 p.2 :=
    ((measurable_p48oTestExt hfm).comp measurable_snd).mul S.measurable_uStar
  have hsm := hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict D)
  have e : (fun ω => ∫ z in D, f z * S.uStar ω z) =
      fun ω => ∫ z in D, p48oTestExt ρ f z * S.uStar ω z := by
    funext ω
    refine setIntegral_congr_fun hadm.domain_borel fun z hz => ?_
    rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
  rw [e]
  exact hsm.measurable

lemma p48o_rpow_three_split {ε α : ℝ} (hε : 0 < ε) (N : ℝ) :
    (ε ^ α * N) ^ 2 * ε ^ α = ε ^ (3 * α) * N ^ 2 := by
  have h2 : (ε ^ α) ^ 2 = ε ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]; ring_nf
  have h3 : ε ^ (2 * α) * ε ^ α = ε ^ (3 * α) := by
    rw [← Real.rpow_add hε]; ring_nf
  rw [mul_pow, h2, ← h3]
  ring

end Producer

/-! ### All scales -/

/-- Concrete data and bounds at every scale: the exponent `α` is fixed before `ρ`; the mean bound
and rate constants depend on `ρ` only. -/
structure P48OAllScalesData (R : GMSA.WholePlaneRootedLQGLaw Ω) where
  α : ℝ
  α_pos : 0 < α
  A : ℝ → ℝ
  C₀ : ℝ → ℝ
  C₁ : ℝ → ℝ
  A_pos : ∀ ρ, ρ ∈ Ioo (0 : ℝ) 1 → 0 < A ρ
  C₀_nonneg : ∀ ρ, ρ ∈ Ioo (0 : ℝ) 1 → 0 ≤ C₀ ρ
  C₁_nonneg : ∀ ρ, ρ ∈ Ioo (0 : ℝ) 1 → 0 ≤ C₁ ρ
  data : ∀ ρ, ρ ∈ Ioo (0 : ℝ) 1 → ∀ ε, ε ∈ Ioo (0 : ℝ) 1 → P48OScaleData R.unrootedLaw ρ
  data_A : ∀ ρ (hρ : ρ ∈ Ioo (0 : ℝ) 1) ε (hε : ε ∈ Ioo (0 : ℝ) 1), (data ρ hρ ε hε).A = A ρ
  bounds : ∀ ρ (hρ : ρ ∈ Ioo (0 : ℝ) 1) ε (hε : ε ∈ Ioo (0 : ℝ) 1),
    P48OScaleBounds (data ρ hρ ε hε) ε α (C₀ ρ) (C₁ ρ)

end MatedCRTHarmonic.GMS4O
