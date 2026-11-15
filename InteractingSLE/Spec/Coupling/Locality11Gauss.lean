import InteractingSLE.GFF.LocalSets.GermVersion
import InteractingSLE.GFF.LocalSets.MarkedAvoidance
import InteractingSLE.GFF.LocalSets.Prop38
import InteractingSLE.GFF.LocalSets.Prop39

/-!
# Theorem 1.1, locality: the Gaussian part (Astra (1.14) ⇒ Lemma 3.6 (i))

Packet PROVE-T11-LOC (Astra §1, "Arbitrary stopping times and locality", p. 7; specification Lemma 3.6). Two
deterministic statements about local sets and the Gaussian limit step of Astra's locality argument:

* `IsLocalSet.add_dist`, `IsLocalSet.congr_set`: a local set of `h` is a local set of `h + T` for a deterministic
  distribution `T` harmonic on `ℍ` (the harmonic part of the two-step model absorbs `T`), and locality only depends on
  the random set up to almost sure equality;
* `isAvoidanceLocal_of_setIntegral_lapTest` (**the locality criterion**): let `h` be a zero-boundary GFF on `ℍ` and `A` a
  hitting-measurable random set. Suppose that for every open `U ⊆ ℍ` there is a Borel version `G` of the projection onto
  `H(U)` such that, on the avoidance event `E_U = {A ∩ U = ∅}`, every Dirichlet pairing `(h, f)_∇ = h(−Δf/2π)`,
  `f ∈ C_c^∞(U)`, satisfies

    `E[e^{i (h, f)_∇} e^{i (h − G h)(Ψ)} 1_{E_U}] = E[e^{i (h, f)_∇}] · E[e^{i (h − G h)(Ψ)} 1_{E_U}]`   (Astra (1.14))

  for every test function `Ψ`. Then `A` satisfies the avoidance criterion (i) of Lemma 3.6.

Proof of the criterion. The projection `G h(Φ)` is the `L²` limit of Dirichlet pairings `(h, f_n)_∇`, `f_n ∈ C_c^∞(U)`
(`exists_tendsto_integral_sq_of_isMarkovDecomposition`), so the identity passes to `e^{i G h(Φ)}` (Astra: "Taking the
limit in (1.14)"); any other version of the projection agrees with `G h` almost surely
(`ae_eq_of_isMarkovDecomposition`). With the Markov independence of `G h` and `h − G h` this gives
`σ(G h) ⫫ σ(h − G h) ⊔ σ(E_U)` (`indep_comap_sup_of_setIntegral_exp`), hence `P[E_U | h] = P[E_U | h − G h]`
("conditionally on `Q_U h`, the event `E_U` is independent of `P_U h`. This is Lemma 3.6(i)").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped ENNReal

namespace InteractingSLE

namespace Coupling

open QuantumZipper LQGMetric LQGMetric.MarkovZB LocalSets

/-! ### Harmonic shifts and almost sure versions of local sets -/

section Shift

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem measurable_add_distOnConst (T : DistOn upperHalfPlaneOpens) :
    Measurable fun x : DistOn upperHalfPlaneOpens => x + T :=
  measurable_distOn_iff.2 fun φ => by
    simp only [add_apply]
    exact (measurable_distOn_apply φ).add_const _

omit mΩ in
/-- Translating a random distribution by a deterministic one does not change the σ-algebra it generates. -/
theorem comap_add_distOnConst (X : Ω → DistOn upperHalfPlaneOpens) (T : DistOn upperHalfPlaneOpens) :
    MeasurableSpace.comap (fun ω => X ω + T) inferInstance = MeasurableSpace.comap X inferInstance := by
  have e : (fun ω => X ω + T) = (fun x => x + T) ∘ X := rfl
  rw [e, ← MeasurableSpace.comap_comp]
  congr 1
  refine le_antisymm (measurable_add_distOnConst T).comap_le fun S hS => ?_
  refine ⟨(fun x => x + -T) ⁻¹' S, measurable_add_distOnConst (-T) hS, ?_⟩
  ext x
  simp

/-- The sum of two distributions harmonic on an open `U` is harmonic on `U`. -/
theorem IsHarmonicDistOn.add' {T₁ T₂ : DistOn upperHalfPlaneOpens} {U : Set ℂ} (hU : IsOpen U)
    (h₁ : IsHarmonicDistOn T₁ U) (h₂ : IsHarmonicDistOn T₂ U) : IsHarmonicDistOn (T₁ + T₂) U := by
  have h0 : IsHarmonicDistOn (0 : DistOn upperHalfPlaneOpens) U :=
    ⟨0, InnerProductSpace.harmonicOnNhd_const (0 : ℝ), fun φ _ => by simp⟩
  have := IsHarmonicDistOn.sub' hU h₁ (IsHarmonicDistOn.sub' hU h0 h₂)
  rwa [zero_sub, sub_neg_eq_add] at this

/-- **Local sets of `h` are local sets of `h + T`** for a deterministic distribution `T` harmonic on `ℍ`. -/
theorem IsLocalSet.add_dist {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : IsLocalSet A h P) {T : DistOn upperHalfPlaneOpens} (hT : IsHarmonicDistOn T H) :
    IsLocalSet A (fun ω => h ω + T) P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hAE, hsub, Ω', mΩ', P', hP', A', h₁, h₂, hA'm, hh₁m, hh₂m, hA'sub, hharm, hcond, hlaw⟩ :=
    hloc
  have hF : Measurable fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 + T) :=
    measurable_fst.prodMk ((measurable_add_distOnConst T).comp measurable_snd)
  have hsum : Measurable fun ω' => h₁ ω' + h₂ ω' :=
    measurable_distOn_iff.2 fun φ => by
      simp only [add_apply]
      exact ((measurable_distOn_apply φ).comp hh₁m).add ((measurable_distOn_apply φ).comp hh₂m)
  refine ⟨hF.comp_aemeasurable hAE, hsub, Ω', mΩ', P', hP', A', fun ω' => h₁ ω' + T, h₂, hA'm,
    (measurable_add_distOnConst T).comp hh₁m, hh₂m, hA'sub, ?_, ?_, ?_⟩
  · filter_upwards [hharm] with ω' hω'
    exact IsHarmonicDistOn.add' (hA'sub ω').2 hω' (IsHarmonicDistOn.mono hT sdiff_subset)
  · rw [comap_add_distOnConst]
    exact hcond
  · have e1 : (fun ω' => (A' ω', (h₁ ω' + T) + h₂ ω')) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 + T)) ∘
          fun ω' => (A' ω', h₁ ω' + h₂ ω') := by
      funext ω'
      simp only [Function.comp_apply, Prod.mk.injEq, true_and]
      abel
    have e2 : (fun ω => (A ω, h ω + T)) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 + T)) ∘ fun ω => (A ω, h ω) := rfl
    rw [e1, ← Measure.map_map hF (hA'm.prodMk hsum), hlaw, e2,
      AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hAE]

/-- **Locality depends on the random set only up to almost sure equality.** -/
theorem IsLocalSet.congr_set {A A' : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : IsLocalSet A h P) (hAA : A' =ᵐ[P] A) : IsLocalSet A' h P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hAE, hsub, Ω', mΩ', P', hP', A'', h₁, h₂, hA''m, hh₁m, hh₂m, hA''sub, hharm, hcond, hlaw⟩ :=
    hloc
  have hpair : (fun ω => (A' ω, h ω)) =ᵐ[P] fun ω => (A ω, h ω) := by
    filter_upwards [hAA] with ω hω
    rw [hω]
  refine ⟨hAE.congr hpair.symm, ?_, Ω', mΩ', P', hP', A'', h₁, h₂, hA''m, hh₁m, hh₂m, hA''sub, hharm, hcond,
    ?_⟩
  · filter_upwards [hsub, hAA] with ω h1 h2
    rwa [h2]
  · rw [hlaw]
    exact Measure.map_congr hpair.symm

end Shift

/-! ### The locality criterion -/

section Criterion

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Characteristic integrals pass to `L²` limits**: if `a n → b` in `L²`, then
`∫ e^{i a n} Z → ∫ e^{i b} Z` for every `Z` with `‖Z‖ ≤ 1`. -/
theorem tendsto_integral_cexp_mul_of_tendsto_integral_sq {a : ℕ → Ω → ℝ} {b : Ω → ℝ}
    (hmem : ∀ n, MemLp (fun ω => a n ω - b ω) 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂P) atTop (𝓝 0))
    {Z : Ω → ℂ} (hZ : ∀ ω, ‖Z ω‖ ≤ 1)
    (ha : ∀ n, AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (a n ω : ℂ)) * Z ω) P)
    (hb : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (b ω : ℂ)) * Z ω) P) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * (a n ω : ℂ)) * Z ω ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (Complex.I * (b ω : ℂ)) * Z ω ∂P)) := by
  have hbd : ∀ (c : Ω → ℝ) ω, ‖Complex.exp (Complex.I * (c ω : ℂ)) * Z ω‖ ≤ 1 := fun c ω => by
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]; exact hZ ω
  have hint : ∀ (c : Ω → ℝ), AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (c ω : ℂ)) * Z ω) P →
      Integrable (fun ω => Complex.exp (Complex.I * (c ω : ℂ)) * Z ω) P := fun c hc =>
    Integrable.of_bound hc 1 (Eventually.of_forall (hbd c))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
    (((Real.continuous_sqrt.tendsto 0).comp hlim).trans (by simp))
  rw [← integral_sub (hint _ (ha n)) (hint _ hb)]
  have e : (fun ω => Complex.exp (Complex.I * (a n ω : ℂ)) * Z ω -
      Complex.exp (Complex.I * (b ω : ℂ)) * Z ω) = fun ω =>
      (Complex.exp (Complex.I * (a n ω : ℂ)) - Complex.exp (Complex.I * (b ω : ℂ))) * Z ω := by
    funext ω; ring
  rw [e]
  exact Real.le_sqrt_of_sq_le (norm_integral_exp_sub_sq_le hZ (hmem n))

omit [IsProbabilityMeasure P] in
theorem setIntegral_eq_integral_indicator_mul {E : Set Ω} (hE : MeasurableSet E) (F Z : Ω → ℂ) :
    ∫ ω in E, F ω * Z ω ∂P = ∫ ω, F ω * E.indicator Z ω ∂P := by
  rw [← integral_indicator hE]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases hω : ω ∈ E
  · simp [indicator_of_mem hω]
  · simp [indicator_of_notMem hω]

/-- **The locality criterion** (Astra (1.14) and its limit, p. 7; Lemma 3.6 (i)). Let `h` be a zero-boundary GFF on
`ℍ` and `A` a hitting-measurable random set. If for every open `U ⊆ ℍ` some Borel version `G` of the projection onto
`H(U)` satisfies, on `{A ∩ U = ∅}`, the product identity (1.14) for every Dirichlet pairing `h(lapTest U f)`,
`f ∈ C_c^∞(U)`, and every character `e^{i T(Ψ)}` of the complementary projection `h − G h`, then `A` satisfies the
avoidance criterion (i) of Lemma 3.6. -/
theorem isAvoidanceLocal_of_setIntegral_lapTest {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hA : Measurable[mΩ, hittingSigma] A)
    (hid : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → ∃ G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens,
      Measurable G ∧ GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P ∧
      ∀ (f : zsSub (U : Set ℂ)) (Ψ : TestOn upperHalfPlaneOpens),
        ∫ ω in {ω | Disjoint (A ω) U}, Complex.exp (Complex.I * (h ω (lapTest U f) : ℂ)) *
            Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
          (∫ ω, Complex.exp (Complex.I * (h ω (lapTest U f) : ℂ)) ∂P) *
            ∫ ω in {ω | Disjoint (A ω) U}, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P) :
    IsAvoidanceLocal A h P := by
  intro U G' hUH hG' hd'
  obtain ⟨G, hG, hd, hidU⟩ := hid U hUH
  have hU : U ≤ upperHalfPlaneOpens := hUH
  have hhm := hh.measurable
  set E : Set Ω := {ω | Disjoint (A ω) (U : Set ℂ)} with hEdef
  have hEm : MeasurableSet E := hA (measurableSet_avoid U.isOpen hUH)
  -- the two versions of the projection agree
  have hGG : (fun ω => G' (h ω)) =ᵐ[P] fun ω => G (h ω) := ae_eq_of_isMarkovDecomposition hU hd' hd
  have hQQ : (fun ω => markovCompl G' (h ω)) =ᵐ[P] fun ω => markovCompl G (h ω) := by
    filter_upwards [hGG] with ω hω
    simp only [markovCompl, hω]
  have hXm : Measurable fun ω => G' (h ω) := hG'.comp hhm
  have hQm : Measurable fun ω => markovCompl G' (h ω) := (measurable_markovCompl hG').comp hhm
  have hcexp : ∀ c : Ω → ℝ, Measurable c → Measurable fun ω => Complex.exp (Complex.I * (c ω : ℂ)) :=
    fun c hc => GFF.measurable_exp_I_mul hc
  -- Step 1: (1.14) for the projection itself
  have hstep : ∀ (Φ Ψ : TestOn upperHalfPlaneOpens),
      ∫ ω in E, Complex.exp (Complex.I * (G' (h ω) Φ : ℂ)) *
          (fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ)))
            (markovCompl G' (h ω)) ∂P =
        (∫ ω, Complex.exp (Complex.I * (G' (h ω) Φ : ℂ)) ∂P) *
          ∫ ω in E, (fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ)))
            (markovCompl G' (h ω)) ∂P := by
    intro Φ Ψ
    set Y : DistOn upperHalfPlaneOpens → ℂ := fun T => Complex.exp (Complex.I * (T Ψ : ℂ)) with hYdef
    have hY : Measurable Y := GFF.measurable_exp_I_mul (measurable_distOn_apply Ψ)
    have hYb : ∀ x, ‖Y x‖ ≤ 1 := fun x => (Complex.norm_exp_I_mul_ofReal _).le
    obtain ⟨f, -, hf⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd' Φ
    set a : ℕ → Ω → ℝ := fun n ω => h ω (lapTest U (f n)) with ha_def
    set b : Ω → ℝ := fun ω => G' (h ω) Φ with hb_def
    have ham : ∀ n, Measurable (a n) := fun n => (measurable_distOn_apply _).comp hhm
    have hbm : Measurable b := (measurable_distOn_apply Φ).comp hXm
    have hmem : ∀ n, MemLp (fun ω => a n ω - b ω) 2 P := fun n => by
      have h1 := (memLp_markov_sub_lapTest hU hd' Φ (f n)).neg
      convert h1 using 1
      funext ω
      simp only [Pi.neg_apply, a, b, neg_sub]
    have hlim : Tendsto (fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂P) atTop (𝓝 0) := by
      refine hf.congr fun n => integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [a, b]
      ring
    set Z : Ω → ℂ := E.indicator fun ω => Y (markovCompl G' (h ω)) with hZdef
    have hZm : Measurable Z := (hY.comp hQm).indicator hEm
    have hZb : ∀ ω, ‖Z ω‖ ≤ 1 := fun ω => by
      by_cases hω : ω ∈ E
      · rw [hZdef, indicator_of_mem hω]; exact hYb _
      · rw [hZdef, indicator_of_notMem hω, norm_zero]; exact zero_le_one
    have h1 := tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim hZb
      (fun n => ((hcexp _ (ham n)).mul hZm).aestronglyMeasurable)
      ((hcexp _ hbm).mul hZm).aestronglyMeasurable
    have h2 := tendsto_integral_cexp_mul_of_tendsto_integral_sq hmem hlim (Z := fun _ => 1)
      (fun _ => le_of_eq norm_one)
      (fun n => ((hcexp _ (ham n)).mul measurable_const).aestronglyMeasurable)
      ((hcexp _ hbm).mul measurable_const).aestronglyMeasurable
    simp only [mul_one] at h2
    have hYQ : ∫ ω in E, Y (markovCompl G' (h ω)) ∂P = ∫ ω in E, Y (markovCompl G (h ω)) ∂P :=
      integral_congr_ae (ae_restrict_of_ae (hQQ.mono fun ω hω => by simp only [hω]))
    have heq : ∀ n, ∫ ω, Complex.exp (Complex.I * (a n ω : ℂ)) * Z ω ∂P =
        (∫ ω, Complex.exp (Complex.I * (a n ω : ℂ)) ∂P) * ∫ ω in E, Y (markovCompl G' (h ω)) ∂P := by
      intro n
      rw [← setIntegral_eq_integral_indicator_mul hEm, hYQ]
      rw [show (fun ω => Y (markovCompl G (h ω))) =
        fun ω => Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) from rfl, ← hidU (f n) Ψ]
      exact integral_congr_ae (ae_restrict_of_ae (hQQ.mono fun ω hω => by simp only [a, Y, hω]))
    rw [setIntegral_eq_integral_indicator_mul hEm]
    refine tendsto_nhds_unique h1 ?_
    simp_rw [heq]
    exact h2.mul_const _
  -- Step 2: `σ(G h) ⫫ σ(h − G h) ⊔ σ(E)`
  have hcexpX : ∀ Φ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => Complex.exp (Complex.I * (G' (h ω) Φ : ℂ)) := fun Φ =>
    hcexp _ ((measurable_distOn_apply Φ).comp hXm)
  have hcexpQ : ∀ Ψ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => Complex.exp (Complex.I * (markovCompl G' (h ω) Ψ : ℂ)) := fun Ψ =>
    hcexp _ ((measurable_distOn_apply Ψ).comp hQm)
  have hintb : ∀ F : Ω → ℂ, Measurable F → (∀ ω, ‖F ω‖ ≤ 1) → Integrable F P := fun F hF hFb =>
    Integrable.of_bound hF.aestronglyMeasurable 1 (Eventually.of_forall hFb)
  have hnorm1 : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ ≤ 1 := fun x =>
    (Complex.norm_exp_I_mul_ofReal x).le
  have huniv : ∀ Φ Ψ : TestOn upperHalfPlaneOpens,
      ∫ ω, Complex.exp (Complex.I * (G' (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G' (h ω) Ψ : ℂ)) ∂P =
        (∫ ω, Complex.exp (Complex.I * (G' (h ω) Φ : ℂ)) ∂P) *
          ∫ ω, Complex.exp (Complex.I * (markovCompl G' (h ω) Ψ : ℂ)) ∂P := fun Φ Ψ =>
    hd'.indepFun.integral_fun_comp_mul_comp (f := fun T : DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * (T Φ : ℂ)))
      (g := fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ)))
      hXm.aemeasurable hQm.aemeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply Φ)).aestronglyMeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply Ψ)).aestronglyMeasurable
  have h𝓜 : MeasurableSpace.generateFrom {E} ≤ mΩ := MeasurableSpace.generateFrom_singleton_le hEm
  have hindep := indep_comap_sup_of_setIntegral_exp (𝓜 := MeasurableSpace.generateFrom {E}) hXm hQm h𝓜
      fun Φ Ψ m hm => by
    have hE' := hstep Φ Ψ
    rcases measurableSet_generateFrom_singleton_iff.1 hm with rfl | rfl | rfl | rfl
    · simp
    · exact hE'
    · have hi1 := hintb (fun ω => Complex.exp (Complex.I * (G' (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G' (h ω) Ψ : ℂ))) ((hcexpX Φ).mul (hcexpQ Ψ))
          fun ω => by
        rw [norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_exp_I_mul_ofReal, one_mul]
      have hi2 := hintb _ (hcexpQ Ψ) fun ω => hnorm1 _
      rw [setIntegral_compl hEm hi1, setIntegral_compl hEm hi2, huniv Φ Ψ, hE', mul_sub]
    · simp only [Measure.restrict_univ]
      exact huniv Φ Ψ
  -- Step 3: the conditional probability of `E` given `h` is a function of `h − G h`
  have hXle := hXm.comap_le
  have hQle := hQm.comap_le
  have hci : CondIndepEv (MeasurableSpace.comap (fun ω => markovCompl G' (h ω)) inferInstance)
      (MeasurableSpace.comap (fun ω => G' (h ω)) inferInstance) (MeasurableSpace.generateFrom {E}) P := by
    refine LQGMetric.condIndepEv_of_condExp_sup_eq hQle hXle h𝓜 fun a ha => ?_
    have hfa : StronglyMeasurable[MeasurableSpace.comap (fun ω => G' (h ω)) inferInstance]
        (a.indicator fun _ => (1 : ℝ)) := stronglyMeasurable_const.indicator ha
    have hind1 : Indep (MeasurableSpace.comap (fun ω => G' (h ω)) inferInstance)
        (MeasurableSpace.generateFrom {E} ⊔ MeasurableSpace.comap (fun ω => markovCompl G' (h ω)) inferInstance) P := by
      rw [sup_comm]; exact hindep
    have hind2 : Indep (MeasurableSpace.comap (fun ω => G' (h ω)) inferInstance)
        (MeasurableSpace.comap (fun ω => markovCompl G' (h ω)) inferInstance) P :=
      indep_of_indep_of_le_right hindep le_sup_left
    have e1 := condExp_indep_eq (m₁ := MeasurableSpace.comap (fun ω => G' (h ω)) inferInstance)
      (m₂ := MeasurableSpace.generateFrom {E} ⊔ MeasurableSpace.comap (fun ω => markovCompl G' (h ω)) inferInstance)
      hXle (sup_le h𝓜 hQle) hfa hind1
    have e2 := condExp_indep_eq (m₁ := MeasurableSpace.comap (fun ω => G' (h ω)) inferInstance)
      (m₂ := MeasurableSpace.comap (fun ω => markovCompl G' (h ω)) inferInstance)
      hXle hQle hfa hind2
    exact e1.trans e2.symm
  have key := LQGMetric.condExp_sup_eq_of_condIndepEv hQle hXle h𝓜 hci
    (b := E) (MeasurableSpace.measurableSet_generateFrom rfl)
  rw [← comap_eq_sup_markov h hG'] at key
  obtain ⟨g, hg, hgeq⟩ :=
    (stronglyMeasurable_condExp (m := MeasurableSpace.comap
      (fun ω => markovCompl G' (h ω)) inferInstance) (μ := P)
      (f := E.indicator fun _ => (1 : ℝ))).exists_eq_measurable_comp
  refine ⟨g, hg.measurable, key.trans ?_⟩
  rw [hgeq]
  rfl

end Criterion

end Coupling

end InteractingSLE
