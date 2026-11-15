import InteractingSLE.Spec.Sobolev.ThinRange
import InteractingSLE.Spec.Sec4.SpecialDetermination
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Aux. lemma 23: the joint law from conditional field laws off a thin hull (§4.2)

Packet PROVE-SEC4-B3. Specification, Aux. lemma 23 and its proof (`source/spec/p097-144.md`, L596–L622,
pp. 122–123): "If `u, v ∈ H^{-ε}_loc(ℍ)` have equal restrictions to `ℍ \ K`, their difference is supported on
`K ∩ ℍ`. Aux. lemma 12, applied after compact localization, gives `u − v = 0`. … Record distributions by a
countable determining family of smooth test pairings and use the local Sobolev norm to specify the Borel subset
`H^{-ε}_loc`. Restriction to the fixed open set `ℍ \ K` is a Borel injection between standard Borel spaces. …
Consequently two probability measures supported on `H^{-ε}_loc` with the same restricted distribution law have the
same full distribution law. … Conditional on a stopped history, the original specification gives the same Gaussian
law on `ℍ \ K_S` … The measurable uniqueness just proved identifies the entire conditional field laws. Integrating
over the common history law proves equality of the full stopped joint laws."

This file proves that measure-theoretic core, for an abstract recorded history `X` with values in a measurable space
`Γ` and a relatively closed thin set `A(γ)` (the hull):

* `injOn_offRecord`: restriction off a thin set, recorded by the countable test family `testFam` of PROVE-T11-SR,
  is injective on the Borel set `cutoffSet ε ζ` of distributions that are `H^{-ε}` after the cutoffs `ζ n`
  (Aux. lemma 12 through `eq_zero_of_cutoff_bound_of_dimH_lt`);
* `eq_of_integral_exp_ratTest`: two probability measures concentrated on `cutoffSet ε ζ` with the same characteristic
  functional at every rational combination of test-family members supported off `A` are equal (cylinder laws by
  characteristic functions and continuity, then Lusin–Souslin `measure_eq_of_map_eq_of_injOn`);
* `ae_integral_condDistrib_eq_off`: a conditional characteristic functional off `A`, given a finer history, is read on
  the regular conditional law of the field given the recorded history;
* `map_prod_eq_of_condCharFun_off`: **the core of Aux. lemma 23**: two couplings with the same history law, both
  locally `H^{-ε}`, whose conditional characteristic functionals off `A` are the same measurable function of the
  history, have the same joint law of field and history.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace InteractingSLE.Sec4

open LQGMetric TopologicalSpace InteractingSLE.Sobolev

variable {U : Opens ℂ}

/-! ### The countable family of rational combinations -/

/-- The rational combination `∑_{(i, q) ∈ F} q • φ_i` of members of the countable test family. -/
def ratTest (F : Finset (TestIdx U × ℚ)) : TestOn U := ∑ p ∈ F, (p.2 : ℝ) • testFam p.1

theorem disjoint_tsupport_ratTest {A : Set ℂ} {F : Finset (TestIdx U × ℚ)}
    (hF : ∀ p ∈ F, Disjoint (ratUnion p.1.1.1 : Set ℂ) A) : Disjoint (tsupport (ratTest F)) A := by
  unfold ratTest
  refine Finset.sum_induction _ (fun φ : TestOn U => Disjoint (tsupport φ) A) ?_ ?_ ?_
  · intro a b ha hb
    have h1 : tsupport ⇑(a + b) ⊆ tsupport ⇑a ∪ tsupport ⇑b := by
      rw [FunLike.coe_add]
      exact tsupport_add _ _
    exact Disjoint.mono_left h1 (disjoint_union_left.2 ⟨ha, hb⟩)
  · rw [FunLike.coe_zero, tsupport_zero]
    exact Set.empty_disjoint A
  · intro p hp
    have h1 : tsupport ⇑((p.2 : ℝ) • testFam p.1) ⊆ tsupport ⇑(testFam p.1) := by
      rw [FunLike.coe_smul]
      exact tsupport_smul_subset_right (fun _ => (p.2 : ℝ)) _
    exact Disjoint.mono_left (h1.trans (tsupport_testFam_subset p.1)) (hF p hp)

/-! ### The restriction record and its injectivity on `H^{-ε}` -/

open scoped Classical in
/-- The pairings with the members of the countable test family whose rational unions avoid `A` (the other
coordinates are `0`): the restriction of a distribution to `U \ A`, recorded countably. -/
def offRecord (A : Set ℂ) (T : DistOn U) : TestIdx U → ℝ :=
  fun i => if Disjoint (ratUnion i.1.1 : Set ℂ) A then T (testFam i) else 0

theorem offRecord_of_disjoint {A : Set ℂ} {T : DistOn U} {i : TestIdx U}
    (hi : Disjoint (ratUnion i.1.1 : Set ℂ) A) : offRecord A T i = T (testFam i) := by
  classical
  simp only [offRecord, hi, ↓reduceIte]

theorem offRecord_of_not_disjoint {A : Set ℂ} {T : DistOn U} {i : TestIdx U}
    (hi : ¬ Disjoint (ratUnion i.1.1 : Set ℂ) A) : offRecord A T i = 0 := by
  classical
  simp only [offRecord, hi, ↓reduceIte]

theorem measurable_offRecord (A : Set ℂ) : Measurable (offRecord (U := U) A) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hi : Disjoint (ratUnion i.1.1 : Set ℂ) A
  · simp only [offRecord_of_disjoint hi]
    exact LQGMetric.measurable_distOn_apply _
  · simp only [offRecord_of_not_disjoint hi]
    exact measurable_const

/-- The Borel set of distributions that are locally `H^{-ε}` through the cutoffs `ζ n`. -/
def cutoffSet (ε : ℝ) (ζ : ℕ → TestOn U) : Set (DistOn U) :=
  {T | ∀ n, negSobolevSq ε T (ζ n) < ⊤}

theorem measurableSet_cutoffSet (ε : ℝ) (ζ : ℕ → TestOn U) : MeasurableSet (cutoffSet ε ζ) := by
  have : cutoffSet ε ζ = ⋂ n, {T | negSobolevSq ε T (ζ n) < ⊤} := by
    ext T; simp [cutoffSet]
  rw [this]
  exact MeasurableSet.iInter fun n =>
    measurableSet_lt (measurable_negSobolevSq ε (ζ n)) measurable_const

/-- **Restriction off a thin set is injective on `H^{-ε}_loc`** (proof of Aux. lemma 23: "The restriction map
is thus injective on `H^{-ε}_loc(ℍ)`"). If `A` is relatively closed in `U` and satisfies (SR3), two distributions
in `cutoffSet ε ζ` (cutoffs `ζ n = 1` on the exhaustion `K_n(U)`) with the same off-`A` record are equal. -/
theorem injOn_offRecord {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {ζ : ℕ → TestOn U}
    (hζ : ∀ n, EqOn (ζ n) 1 (exhaustK U n)) {A : Set ℂ} (hAcl : closure A ∩ U ⊆ A)
    (hdim : ∀ K, IsCompact K → K ⊆ U → dimH (A ∩ K) < ENNReal.ofReal (2 - 2 * ε)) :
    InjOn (offRecord A) (cutoffSet ε ζ) := by
  intro T hT T' hT' hR
  have h0 : T - T' = 0 := by
    refine eq_zero_of_cutoff_bound_of_dimH_lt hε0 hε1 hAcl hdim (fun φ => ?_) ?_
    · obtain ⟨n, hn⟩ := exists_exhaustK_superset U φ.hasCompactSupport.isCompact φ.tsupport_subset
      exact ⟨ζ n, (hζ n).mono hn, negSobolevSq_sub_lt_top (hT n) (hT' n)⟩
    · refine eq_zero_off_of_testFam hAcl fun i hi => ?_
      have := congrFun hR i
      rw [offRecord_of_disjoint hi, offRecord_of_disjoint hi] at this
      rw [sub_apply, this, sub_self]
  exact sub_eq_zero.1 h0

open scoped Classical in
/-- The pairing of `T` with a rational combination of off-`A` members, as the inner product of the restricted
record with a rational vector. -/
theorem inner_offRecord_eq {A : Set ℂ} (S' : Finset (TestIdx U)) (q : S' → ℚ) (T : DistOn U) :
    inner ℝ (WithLp.toLp 2 (fun j : S' => offRecord A T j)) (WithLp.toLp 2 (fun j => (q j : ℝ))) =
      T (ratTest (((Finset.univ : Finset S').filter
        fun j : S' => Disjoint (ratUnion (j : TestIdx U).1.1 : Set ℂ) A).image
          fun j : S' => ((j : TestIdx U), q j))) := by
  rw [PiLp.inner_apply]
  unfold ratTest
  rw [Finset.sum_image (fun j _ k _ hjk => Subtype.ext (congrArg Prod.fst hjk)), map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : Disjoint (ratUnion (j : TestIdx U).1.1 : Set ℂ) A
  · rw [ite_eq_left hj, WithLp.ofLp_toLp, WithLp.ofLp_toLp, offRecord_of_disjoint hj, map_smul,
      smul_eq_mul, Real.inner_apply, mul_comm]
  · rw [ite_eq_right hj, WithLp.ofLp_toLp, offRecord_of_not_disjoint hj, inner_zero_left]

/-- **Measures on `H^{-ε}_loc` are determined by their characteristic functionals off a thin set** (proof of
Aux. lemma 23: "two probability measures supported on `H^{-ε}_loc` with the same restricted distribution law have
the same full distribution law"). Let `A` be relatively closed in `U` with (SR3). Two probability measures on
`𝒟'(U)` concentrated on `cutoffSet ε ζ`, with the same characteristic functional at every rational combination of
members of the countable test family supported off `A`, are equal. -/
theorem eq_of_integral_exp_ratTest {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {ζ : ℕ → TestOn U}
    (hζ : ∀ n, EqOn (ζ n) 1 (exhaustK U n)) {A : Set ℂ} (hAcl : closure A ∩ U ⊆ A)
    (hdim : ∀ K, IsCompact K → K ⊆ U → dimH (A ∩ K) < ENNReal.ofReal (2 - 2 * ε))
    {μ ν : Measure (DistOn U)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ (cutoffSet ε ζ)ᶜ = 0) (hν : ν (cutoffSet ε ζ)ᶜ = 0)
    (h : ∀ F : Finset (TestIdx U × ℚ), (∀ p ∈ F, Disjoint (ratUnion p.1.1.1 : Set ℂ) A) →
      ∫ T, Complex.exp (↑(T (ratTest F)) * Complex.I) ∂μ =
        ∫ T, Complex.exp (↑(T (ratTest F)) * Complex.I) ∂ν) :
    μ = ν := by
  classical
  refine measure_eq_of_map_eq_of_injOn (measurable_offRecord A) (measurableSet_cutoffSet ε ζ)
    (injOn_offRecord hε0 hε1 hζ hAcl hdim) hμ hν ?_
  have hR : Measurable (offRecord (U := U) A) := measurable_offRecord A
  refine ext_of_generate_finite (measurableCylinders fun _ : TestIdx U => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs => ?_) ?_
  · rw [mem_measurableCylinders] at hs
    obtain ⟨S', Sx, hSx, rfl⟩ := hs
    set pr : DistOn U → EuclideanSpace ℝ S' :=
      fun T => WithLp.toLp 2 (fun j : S' => offRecord A T j) with hprdef
    have hpr : Measurable pr := (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun j => (measurable_pi_apply (j : TestIdx U)).comp hR)
    set D : Set (EuclideanSpace ℝ S') :=
      (PiLp.homeomorph 2 fun _ : S' => ℝ) ⁻¹' (univ.pi fun _ => range ((↑) : ℚ → ℝ)) with hD
    have hDd : Dense D :=
      (dense_pi univ fun _ _ => Rat.denseRange_cast).preimage (PiLp.homeomorph 2 _).isOpenMap
    have hchar : charFun (μ.map pr) = charFun (ν.map pr) := by
      refine Continuous.ext_on hDd continuous_charFun continuous_charFun fun t ht => ?_
      have ht' : ∀ j, ∃ r : ℚ, (r : ℝ) = t.ofLp j := fun j => ht j (mem_univ j)
      choose q hq using ht'
      have htq : t = WithLp.toLp 2 (fun j => (q j : ℝ)) := by
        rw [← WithLp.toLp_ofLp (p := 2) t]
        congr 1
        funext j
        exact (hq j).symm
      rw [htq, charFun_apply, charFun_apply, integral_map hpr.aemeasurable (by fun_prop),
        integral_map hpr.aemeasurable (by fun_prop)]
      simp_rw [hprdef, inner_offRecord_eq S' q]
      refine h _ fun p hp => ?_
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
      exact (Finset.mem_filter.1 hj).2
    have heq := Measure.ext_of_charFun hchar
    have hmS : MeasurableSet {y : EuclideanSpace ℝ S' | y.ofLp ∈ Sx} :=
      (WithLp.measurable_ofLp 2 _) hSx
    have hset : offRecord A ⁻¹' cylinder S' Sx = pr ⁻¹' {y | y.ofLp ∈ Sx} := by
      ext T
      simp only [pr, cylinder, mem_preimage]
      rfl
    rw [Measure.map_apply hR (MeasurableSet.cylinder S' hSx),
      Measure.map_apply hR (MeasurableSet.cylinder S' hSx), hset, ← Measure.map_apply hpr hmS,
      ← Measure.map_apply hpr hmS, heq]
  · rw [Measure.map_apply hR MeasurableSet.univ, Measure.map_apply hR MeasurableSet.univ,
      preimage_univ, measure_univ, measure_univ]

/-! ### Conditional laws given the recorded history -/

section Curve

variable {Ω Γ : Type*} {mΓ : MeasurableSpace Γ} {J mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Complex-valued form of `Sobolev.condExp_eq_off_of_le`: an identity `E[f | 𝒥] = g(X)` on `{X ∈ B}` passes to
the conditional expectation given the recorded history `X` (`σ(X) ≤ 𝒥`). -/
theorem condExp_eq_off_of_le_complex {X : Ω → Γ} (hX : Measurable X)
    (hXJ : MeasurableSpace.comap X mΓ ≤ J) (hJ : J ≤ mΩ) {f : Ω → ℂ}
    {B : Set Γ} (hB : MeasurableSet B) {g : Γ → ℂ} (hg : Measurable g)
    (hJB : ∀ᵐ o ∂P, X o ∈ B → P[f | J] o = g (X o)) :
    ∀ᵐ o ∂P, X o ∈ B → P[f | MeasurableSpace.comap X mΓ] o = g (X o) := by
  set 𝓖 := MeasurableSpace.comap X mΓ
  have h𝓖 : 𝓖 ≤ mΩ := hX.comap_le
  have hs : MeasurableSet[𝓖] (X ⁻¹' B) := ⟨B, hB, rfl⟩
  have h1 : P[f | 𝓖] =ᵐ[P] P[P[f | J] | 𝓖] := (condExp_condExp_of_le hXJ hJ).symm
  have h2 : P[(X ⁻¹' B).indicator (P[f | J]) | 𝓖] =ᵐ[P] (X ⁻¹' B).indicator (P[P[f | J] | 𝓖]) :=
    condExp_indicator integrable_condExp hs
  have h3 : (X ⁻¹' B).indicator (P[f | J]) =ᵐ[P] (X ⁻¹' B).indicator (g ∘ X) := by
    filter_upwards [hJB] with o ho
    by_cases hb : X o ∈ B
    · rw [indicator_of_mem (show o ∈ X ⁻¹' B from hb), indicator_of_mem (show o ∈ X ⁻¹' B from hb),
        ho hb]; rfl
    · rw [indicator_of_notMem (show o ∉ X ⁻¹' B from hb),
        indicator_of_notMem (show o ∉ X ⁻¹' B from hb)]
  have hint : Integrable ((X ⁻¹' B).indicator (g ∘ X)) P :=
    (integrable_condExp.indicator (h𝓖 _ hs)).congr h3
  have hgX : StronglyMeasurable[𝓖] (g ∘ X) :=
    (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
  have h4 : P[(X ⁻¹' B).indicator (g ∘ X) | 𝓖] = (X ⁻¹' B).indicator (g ∘ X) :=
    condExp_of_stronglyMeasurable h𝓖 (hgX.indicator hs) hint
  have h5 : P[(X ⁻¹' B).indicator (P[f | J]) | 𝓖] =ᵐ[P] P[(X ⁻¹' B).indicator (g ∘ X) | 𝓖] :=
    condExp_congr_ae h3
  filter_upwards [h1, h2, h5] with o e1 e2 e5 hb
  have hb' : o ∈ X ⁻¹' B := hb
  have e6 : (X ⁻¹' B).indicator (P[P[f | J] | 𝓖]) o = P[P[f | J] | 𝓖] o := indicator_of_mem hb' _
  rw [e1, ← e6, ← e2, e5, h4, indicator_of_mem hb']
  rfl

/-- **The off-`A` characteristic functional, read on the curve-conditional law.** If, given a finer history
`𝒥 ⊇ σ(X)`, the conditional characteristic functional of the field at `φ` is `g(X)` on `{X ∈ B}`, then for
`law(X)`-almost every `γ ∈ B` the regular conditional law of the field given `X = γ` has characteristic functional
`g(γ)` at `φ`. -/
theorem ae_integral_condDistrib_eq_off {X : Ω → Γ} (hX : Measurable X)
    (hXJ : MeasurableSpace.comap X mΓ ≤ J) (hJ : J ≤ mΩ) {h : Ω → DistOn U} (hh : Measurable h)
    {φ : TestOn U} {B : Set Γ} (hB : MeasurableSet B) {g : Γ → ℂ} (hg : Measurable g)
    (hcf : ∀ᵐ o ∂P, X o ∈ B → P[fun o => Complex.exp (↑(h o φ) * Complex.I) | J] o = g (X o)) :
    ∀ᵐ γ ∂(P.map X), γ ∈ B →
      ∫ T, Complex.exp (↑(T φ) * Complex.I) ∂(condDistrib h X P γ) = g γ := by
  have hfm : Measurable fun T : DistOn U => Complex.exp (↑(T φ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (LQGMetric.measurable_distOn_apply φ)).mul_const _)
  have hint : Integrable (fun o => Complex.exp (↑(h o φ) * Complex.I)) P :=
    integrable_exp_mul_I ((LQGMetric.measurable_distOn_apply φ).comp hh)
  have h1 := condExp_ae_eq_integral_condDistrib hX hh.aemeasurable hfm.stronglyMeasurable hint
  have h2 := condExp_eq_off_of_le_complex hX hXJ hJ hB hg hcf
  have hF : Measurable fun γ => ∫ T, Complex.exp (↑(T φ) * Complex.I) ∂(condDistrib h X P γ) :=
    have hu : StronglyMeasurable (Function.uncurry fun (_ : Γ) (T : DistOn U) =>
        Complex.exp (↑(T φ) * Complex.I)) :=
      (hfm.comp measurable_snd).stronglyMeasurable
    (StronglyMeasurable.integral_kernel_prod_right (κ := condDistrib h X P) hu).measurable
  have hS : MeasurableSet {γ | γ ∈ B →
      ∫ T, Complex.exp (↑(T φ) * Complex.I) ∂(condDistrib h X P γ) = g γ} := by
    have : {γ | γ ∈ B → ∫ T, Complex.exp (↑(T φ) * Complex.I) ∂(condDistrib h X P γ) = g γ} =
        Bᶜ ∪ {γ | ∫ T, Complex.exp (↑(T φ) * Complex.I) ∂(condDistrib h X P γ) = g γ} := by
      ext γ
      simp only [mem_ofPred_eq, mem_union, mem_compl_iff, imp_iff_not_or]
    rw [this]
    exact hB.compl.union (measurableSet_eq_fun hF hg)
  rw [ae_map_iff hX.aemeasurable hS]
  filter_upwards [h1, h2] with o e1 e2 hb
  rw [← e1]
  exact e2 hb

/-- The regular conditional law of a locally `H^{-ε}` field ((SR1)) given a recorded history is concentrated on
`cutoffSet ε ζ` for almost every history. -/
theorem ae_condDistrib_compl_cutoffSet {ε : ℝ} {ζ : ℕ → TestOn U} {X : Ω → Γ} (hX : Measurable X)
    {h : Ω → DistOn U} (hh : Measurable h)
    (hSR1 : ∀ ζ' : TestOn U, ∫⁻ o, negSobolevSq ε (h o) ζ' ∂P < ⊤) :
    ∀ᵐ γ ∂(P.map X), condDistrib h X P γ (cutoffSet ε ζ)ᶜ = 0 := by
  have hS := measurableSet_cutoffSet ε ζ
  have hae : ∀ᵐ o ∂P, h o ∈ cutoffSet ε ζ :=
    ae_all_iff.2 fun n => ae_lt_top ((measurable_negSobolevSq ε (ζ n)).comp hh) (hSR1 (ζ n)).ne
  have h0 : P (h ⁻¹' (cutoffSet ε ζ)ᶜ) = 0 := by
    rw [← ae_iff.1 hae]
    rfl
  have hcomp : (P.map X ⊗ₘ condDistrib h X P) (univ ×ˢ (cutoffSet ε ζ)ᶜ) = 0 := by
    rw [compProd_map_condDistrib hX.aemeasurable hh.aemeasurable,
      Measure.map_apply (hX.prodMk hh) (MeasurableSet.univ.prod hS.compl)]
    have : (fun o => (X o, h o)) ⁻¹' (univ ×ˢ (cutoffSet ε ζ)ᶜ) = h ⁻¹' (cutoffSet ε ζ)ᶜ := by
      ext o; simp
    rw [this, h0]
  rw [Measure.compProd_apply_prod MeasurableSet.univ hS.compl, Measure.restrict_univ] at hcomp
  exact (lintegral_eq_zero_iff (Kernel.measurable_coe _ hS.compl)).1 hcomp

end Curve

/-! ### The joint law -/

theorem map_prod_swap_eq {Ω Γ : Type*} {mΓ : MeasurableSpace Γ} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {h : Ω → DistOn U} {X : Ω → Γ} (hh : Measurable h) (hX : Measurable X) :
    P.map (fun o => (h o, X o)) = (P.map (fun o => (X o, h o))).map Prod.swap := by
  rw [Measure.map_map measurable_swap (hX.prodMk hh)]
  rfl

/-- **The core of Aux. lemma 23** (`source/spec/p097-144.md` L617–L620, p. 123: "The measurable uniqueness
just proved identifies the entire conditional field laws. Integrating over the common history law proves equality
of the full stopped joint laws"). Two couplings `(hᵢ, Xᵢ)` of a field on `U` with a recorded history `Xᵢ` (values in
`Γ`), with:
* the same history law;
* in both couplings the field is locally `H^{-ε}` ((SR1));
* a finer retained history `𝒥ᵢ ⊇ σ(Xᵢ)` such that, for every test function `φ`, on the event that `supp φ` avoids
  the relatively closed set `A(Xᵢ)` (the hull), the conditional characteristic functional of the field at `φ` given
  `𝒥ᵢ` is the same measurable function `G φ` of the history in both couplings;
* (SR3) for `A(γ)` for almost every history.

Then the joint laws of field and history agree. No Gaussian form of `G` and no conditional law on `A` is used: the
restriction off `A` determines the law on `H^{-ε}_loc` (`eq_of_integral_exp_ratTest`). -/
theorem map_prod_eq_of_condCharFun_off {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {Γ : Type*} {mΓ : MeasurableSpace Γ} {A : Γ → Set ℂ}
    (hAcl : ∀ γ, closure (A γ) ∩ U ⊆ A γ)
    (hAm : ∀ K : Set ℂ, IsCompact K → MeasurableSet {γ | Disjoint K (A γ)})
    {G : TestOn U → Γ → ℂ} (hG : ∀ φ, Measurable (G φ))
    {Ω₁ : Type*} {J₁ m₁ : MeasurableSpace Ω₁} {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {h₁ : Ω₁ → DistOn U} {X₁ : Ω₁ → Γ} (hh₁ : Measurable h₁) (hX₁ : Measurable X₁)
    (hXJ₁ : MeasurableSpace.comap X₁ mΓ ≤ J₁) (hJ₁ : J₁ ≤ m₁)
    (hSR1₁ : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h₁ o) ζ ∂P₁ < ⊤)
    (hcf₁ : ∀ φ : TestOn U, ∀ᵐ o ∂P₁, Disjoint (tsupport φ) (A (X₁ o)) →
      P₁[fun o => Complex.exp (↑(h₁ o φ) * Complex.I) | J₁] o = G φ (X₁ o))
    {Ω₂ : Type*} {J₂ m₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn U} {X₂ : Ω₂ → Γ} (hh₂ : Measurable h₂) (hX₂ : Measurable X₂)
    (hXJ₂ : MeasurableSpace.comap X₂ mΓ ≤ J₂) (hJ₂ : J₂ ≤ m₂)
    (hSR1₂ : ∀ ζ : TestOn U, ∫⁻ o, negSobolevSq ε (h₂ o) ζ ∂P₂ < ⊤)
    (hcf₂ : ∀ φ : TestOn U, ∀ᵐ o ∂P₂, Disjoint (tsupport φ) (A (X₂ o)) →
      P₂[fun o => Complex.exp (↑(h₂ o φ) * Complex.I) | J₂] o = G φ (X₂ o))
    (hlaw : P₁.map X₁ = P₂.map X₂)
    (hSR3 : ∀ᵐ γ ∂(P₁.map X₁), ∀ K, IsCompact K → K ⊆ U →
      dimH (A γ ∩ K) < ENNReal.ofReal (2 - 2 * ε)) :
    P₁.map (fun o => (h₁ o, X₁ o)) = P₂.map (fun o => (h₂ o, X₂ o)) := by
  classical
  have hcut : ∀ k, ∃ ζ : TestOn U, EqOn ζ 1 (exhaustK U k) := fun k => by
    obtain ⟨ζ, -, h1⟩ := exists_cutoff_testOn (exhaustK U k).isCompact (exhaustK_subset U k)
    exact ⟨ζ, h1⟩
  choose ζ hζ using hcut
  have hc₁ : ∀ᵐ γ ∂(P₁.map X₁), condDistrib h₁ X₁ P₁ γ (cutoffSet ε ζ)ᶜ = 0 :=
    ae_condDistrib_compl_cutoffSet hX₁ hh₁ hSR1₁
  have hc₂ : ∀ᵐ γ ∂(P₁.map X₁), condDistrib h₂ X₂ P₂ γ (cutoffSet ε ζ)ᶜ = 0 := by
    rw [hlaw]; exact ae_condDistrib_compl_cutoffSet hX₂ hh₂ hSR1₂
  have hF : ∀ F : Finset (TestIdx U × ℚ), ∀ᵐ γ ∂(P₁.map X₁),
      (∀ p ∈ F, Disjoint (ratUnion p.1.1.1 : Set ℂ) (A γ)) →
        ∫ T, Complex.exp (↑(T (ratTest F)) * Complex.I) ∂(condDistrib h₂ X₂ P₂ γ) =
          ∫ T, Complex.exp (↑(T (ratTest F)) * Complex.I) ∂(condDistrib h₁ X₁ P₁ γ) := by
    intro F
    have hB := hAm (tsupport (ratTest F)) (ratTest F).hasCompactSupport
    have e₁ := ae_integral_condDistrib_eq_off hX₁ hXJ₁ hJ₁ hh₁ hB (hG _) (hcf₁ (ratTest F))
    have e₂ := ae_integral_condDistrib_eq_off hX₂ hXJ₂ hJ₂ hh₂ hB (hG _) (hcf₂ (ratTest F))
    rw [← hlaw] at e₂
    filter_upwards [e₁, e₂] with γ g1 g2 hd
    have hd' : γ ∈ {γ | Disjoint (tsupport (ratTest F)) (A γ)} := disjoint_tsupport_ratTest hd
    rw [g1 hd', g2 hd']
  have hker : condDistrib h₂ X₂ P₂ =ᵐ[P₁.map X₁] condDistrib h₁ X₁ P₁ := by
    filter_upwards [ae_all_iff.2 hF, hc₁, hc₂, hSR3] with γ hγF hγ1 hγ2 hγ3
    exact eq_of_integral_exp_ratTest hε0 hε1 hζ (hAcl γ) hγ3 hγ2 hγ1 hγF
  have hjoint := map_prod_eq_of_condDistrib_ae_eq hX₁.aemeasurable hh₁.aemeasurable
    hX₂.aemeasurable hh₂.aemeasurable hlaw.symm hker
  rw [map_prod_swap_eq hh₁ hX₁, map_prod_swap_eq hh₂ hX₂, hjoint]

end InteractingSLE.Sec4
