import InteractingSLE.GFF.LocalSets.Projection
import InteractingSLE.GFF.LocalSets.IndepCharFun

/-!
# Lemma 3.6, (iv) ⇒ (ii): the marked avoidance factorization

Source: specification p. 54–55 (`source/spec/p049-096.md#lem-3.6-proof`, L116–L137): for a local set
`A` of a zero-boundary GFF `h` on `ℍ` and a deterministic open `U ⊆ ℍ`, with `X = P_U h`,
`Y = h − P_U h` and `E = {A ∩ U = ∅}`,
`E[f(X) g(A, Y) 1_E] = μ_U(f) E[g(A, Y) 1_E]` (3.6), and the same on `Eᶜ`; hence `X` is independent
of `(Y, 1_E, A 1_E)`, which is (ii).

## Route

1. *Two-step model* (`integral_exp_lapTest_model`): in a two-step model `(A', h₁, h₂)` of the local
   set, on `{A' ∩ U = ∅}` the harmonic `h₁` annihilates the Dirichlet pairings `(·, f)_∇`,
   `f ∈ C_c^∞(U)`, and the conditional characteristic function of `h₂` given `(A', h₁)` is the
   zero-boundary one on `ℍ \ A' ⊇ U`; its Gram vectors on `C_c^∞(U)` do not depend on the domain.
2. *Transfer* along the law of `(A, h)` and the `L²` approximation of `P_U h` by Dirichlet pairings
   (`InteractingSLE.LocalSets.exists_tendsto_integral_sq_of_isMarkovDecomposition`) give
   `E[e^{iX(Φ)+iY(Ψ)} k(A) 1_E] = e^{-‖covVec U Φ‖²/2} E[e^{iY(Ψ)} k(A) 1_E]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB

/-! ### Elementary lemmas -/

section Elementary

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Pull-out property of the conditional expectation under an integral, for a bounded
`m`-measurable complex factor. -/
theorem integral_mul_condExp_of_bdd [IsFiniteMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {W F : Ω → ℂ} (hW : StronglyMeasurable[m] W) {C : ℝ} (hWb : ∀ ω, ‖W ω‖ ≤ C)
    (hF : Integrable F P) :
    ∫ ω, W ω * F ω ∂P = ∫ ω, W ω * (P[F | m]) ω ∂P := by
  have hWF : Integrable (fun ω => W ω * F ω) P :=
    hF.bdd_mul (hW.mono hm).aestronglyMeasurable (Eventually.of_forall hWb)
  have hpull := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hW
    (by simpa [ContinuousLinearMap.mul_apply'] using hWF) hF
  rw [← integral_condExp hm (f := fun ω => W ω * F ω)]
  refine integral_congr_ae ?_
  filter_upwards [hpull] with ω hω
  simpa [ContinuousLinearMap.mul_apply'] using hω

/-- `(E|f|)² ≤ E f²` on a probability space. -/
theorem sq_integral_abs_le [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ ω, |f ω| ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  have habs : MemLp (fun ω => |f ω|) 2 P := hf.abs
  have h := variance_nonneg (fun ω => |f ω|) P
  rw [variance_eq_sub habs] at h
  have e : (fun ω => |f ω|) ^ 2 = fun ω => f ω ^ 2 := by
    funext ω; simp [sq_abs]
  rw [e] at h
  linarith

/-- `‖∫ (e^{ia} − e^{ib}) W‖² ≤ E (a − b)²` for `‖W‖ ≤ 1`. -/
theorem norm_integral_exp_sub_sq_le [IsProbabilityMeasure P] {a b : Ω → ℝ} {W : Ω → ℂ}
    (hWb : ∀ ω, ‖W ω‖ ≤ 1) (hab : MemLp (fun ω => a ω - b ω) 2 P) :
    ‖∫ ω, (Complex.exp (Complex.I * (a ω : ℂ)) - Complex.exp (Complex.I * (b ω : ℂ))) * W ω ∂P‖
        ^ 2 ≤ ∫ ω, (a ω - b ω) ^ 2 ∂P := by
  have hpt : ∀ ω, ‖(Complex.exp (Complex.I * (a ω : ℂ)) - Complex.exp (Complex.I * (b ω : ℂ))) *
      W ω‖ ≤ |a ω - b ω| := by
    intro ω
    rw [norm_mul]
    have h1 : ‖Complex.exp (Complex.I * (a ω : ℂ)) - Complex.exp (Complex.I * (b ω : ℂ))‖ ≤
        |a ω - b ω| := by
      have e : Complex.exp (Complex.I * (a ω : ℂ)) - Complex.exp (Complex.I * (b ω : ℂ)) =
          Complex.exp (Complex.I * (b ω : ℂ)) *
            (Complex.exp (Complex.I * ((a ω - b ω : ℝ) : ℂ)) - 1) := by
        rw [mul_sub, ← Complex.exp_add, mul_one]
        congr 2
        push_cast
        ring
      rw [e, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
      simpa [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := a ω - b ω)
    calc _ ≤ |a ω - b ω| * 1 := mul_le_mul h1 (hWb ω) (norm_nonneg _) (abs_nonneg _)
      _ = |a ω - b ω| := mul_one _
  have hint : ‖∫ ω, (Complex.exp (Complex.I * (a ω : ℂ)) - Complex.exp (Complex.I * (b ω : ℂ))) *
      W ω ∂P‖ ≤ ∫ ω, |a ω - b ω| ∂P :=
    norm_integral_le_of_norm_le (hab.integrable one_le_two).abs (Eventually.of_forall hpt)
  calc _ ≤ (∫ ω, |a ω - b ω| ∂P) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hint 2
    _ ≤ _ := sq_integral_abs_le hab

end Elementary

/-! ### Linearity of gradient features -/

lemma gradFeat_sub_of_mem {D : Set ℂ} {f g : ℂ → ℝ} (hf : f ∈ zeroSpace D)
    (hg : g ∈ zeroSpace D) : gradFeat D (f - g) = gradFeat D f - gradFeat D g := by
  have hV := isDNSpace_zeroSpace D
  have hg' : (-1 : ℝ) • g ∈ zeroSpace D := (zsSub D).smul_mem (-1) hg
  rw [sub_eq_add_neg, show -g = (-1 : ℝ) • g by simp, gradFeat_add hV hf hg',
    gradFeat_smul hV (-1) hg]
  simp [sub_eq_add_neg]

/-! ### The two-step model -/

section Model

variable {Ω' : Type*} [mΩ' : MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

omit mΩ' in
/-- The σ-algebra `σ(A', h₁)` of the first step of a two-step model. -/
@[instance_reducible]
def twoStepSigma (A' : Ω' → Set ℂ) (h₁ : Ω' → DistOn upperHalfPlaneOpens) :
    MeasurableSpace Ω' :=
  MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance

/-- The variance of `lapTest f − lapTest f' + Ψ` on an open `V ⊇ U`. -/
theorem zeroGFFTestCov_lapTest_sub_add {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) {V : Set ℂ}
    (hV : IsOpen V) (hVH : V ⊆ H) (hUV : (U : Set ℂ) ⊆ V) (Ψ : TestOn upperHalfPlaneOpens)
    (f f' : zsSub (U : Set ℂ)) :
    zeroGFFTestCov V ⇑(lapTest U f - lapTest U f' + Ψ) ⇑(lapTest U f - lapTest U f' + Ψ) =
      ‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
        2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫ + zeroGFFTestCov V Ψ Ψ := by
  have hfU : f.1 - f'.1 ∈ zeroSpace U := (zsSub (U : Set ℂ)).sub_mem f.2 f'.2
  have hfV : ∀ g : zsSub (U : Set ℂ), g.1 ∈ zeroSpace V := fun g =>
    ⟨g.2.1, g.2.2.1, g.2.2.2.trans hUV⟩
  have hcov : covVec V ⇑(lapTest U f - lapTest U f' + Ψ) = gradFeat V (f.1 - f'.1) + covVec V Ψ := by
    rw [covVec_add hV hVH, covVec_sub hV hVH, covVec_lapTest hU hV hVH hUV,
      covVec_lapTest hU hV hVH hUV, gradFeat_sub_of_mem (hfV f) (hfV f')]
  rw [zeroGFFTestCov_eq_inner_covVec hV hVH, zeroGFFTestCov_eq_inner_covVec hV hVH Ψ Ψ, hcov,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, norm_add_sq_real,
    norm_gradFeat_eq hUV hfU, inner_gradFeat_covVec_eq U.isOpen hV hVH hUV hfU,
    gradFeat_sub_of_mem f.2 f'.2]

/-- **The two-step model on the avoidance event.** In a two-step model `(A', h₁, h₂)`, on
`{A' ∩ U = ∅}` the harmonic part annihilates the Dirichlet pairings of `C_c^∞(U)` and the residual
field is a zero-boundary GFF on `ℍ \ A' ⊇ U` given `(A', h₁)`; so for
`χ = (·, f)_∇ − (·, f')_∇ + Ψ` the weighted characteristic function factors through the
domain-independent Dirichlet part. -/
theorem integral_exp_lapTest_model {A' : Ω' → Set ℂ} {h₁ h₂ : Ω' → DistOn upperHalfPlaneOpens}
    (hA' : Measurable[mΩ', hittingSigma] A') (hh₁ : Measurable h₁) (hh₂ : Measurable h₂)
    (hrel : ∀ ω, A' ω ⊆ H ∧ IsOpen (H \ A' ω))
    (hharm : ∀ᵐ ω ∂P', IsHarmonicDistOn (h₁ ω) (H \ A' ω))
    (hcond : IsCondZeroBoundaryGFF P' (MeasurableSpace.comap A' hittingSigma ⊔
      MeasurableSpace.comap h₁ inferInstance) (fun ω => H \ A' ω) h₂)
    {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens) {k : Set ℂ → ℂ}
    (hk : Measurable[hittingSigma] k) (hkb : ∀ S, ‖k S‖ ≤ 1) (Ψ : TestOn upperHalfPlaneOpens)
    (f f' : zsSub (U : Set ℂ)) :
    ∫ ω, {ω | Disjoint (A' ω) U}.indicator (fun ω => k (A' ω)) ω *
        Complex.exp (Complex.I * ((h₁ ω + h₂ ω) (lapTest U f - lapTest U f' + Ψ) : ℂ)) ∂P' =
      ((Real.exp (-(1 / 2) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
          2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫)) : ℝ) : ℂ) *
        ∫ ω, {ω | Disjoint (A' ω) U}.indicator (fun ω => k (A' ω)) ω *
          Complex.exp (Complex.I * (h₁ ω Ψ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A' ω) Ψ Ψ) : ℝ) : ℂ) ∂P' := by
  set E' := {ω | Disjoint (A' ω) (U : Set ℂ)} with hE'
  set χ := lapTest U f - lapTest U f' + Ψ with hχ
  change IsCondZeroBoundaryGFF P' (twoStepSigma A' h₁) (fun ω => H \ A' ω) h₂ at hcond
  have h𝒢le : twoStepSigma A' h₁ ≤ mΩ' := sup_le hA'.comap_le hh₁.comap_le
  have hE'm : MeasurableSet[twoStepSigma A' h₁] E' :=
    (le_sup_left : _ ≤ twoStepSigma A' h₁) _ ⟨_, measurableSet_avoid U.isOpen hU, rfl⟩
  set W : Ω' → ℂ := fun ω => E'.indicator (fun ω => k (A' ω)) ω *
    Complex.exp (Complex.I * (h₁ ω Ψ : ℂ)) with hWdef
  have hWm : StronglyMeasurable[twoStepSigma A' h₁] W := by
    have h1 : Measurable[twoStepSigma A' h₁] fun ω => k (A' ω) :=
      hk.comp (Measurable.of_comap_le le_sup_left)
    have h2 : Measurable[twoStepSigma A' h₁] fun ω => h₁ ω Ψ :=
      (measurable_distOn_apply Ψ).comp (Measurable.of_comap_le le_sup_right)
    exact ((h1.indicator hE'm).mul (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp h2)))).stronglyMeasurable
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := by
    intro ω
    simp only [hWdef, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    by_cases hω : ω ∈ E'
    · rw [Set.indicator_of_mem hω]; exact hkb _
    · rw [Set.indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hstep1 : ∫ ω, E'.indicator (fun ω => k (A' ω)) ω *
      Complex.exp (Complex.I * ((h₁ ω + h₂ ω) χ : ℂ)) ∂P' =
      ∫ ω, W ω * Complex.exp (Complex.I * (h₂ ω χ : ℂ)) ∂P' := by
    refine integral_congr_ae ?_
    filter_upwards [hharm] with ω hω
    by_cases hω' : ω ∈ E'
    · have hUV : (U : Set ℂ) ⊆ H \ A' ω := fun z hz =>
        ⟨hU hz, fun hzA => Set.disjoint_left.1 hω' hzA hz⟩
      have h0 := IsHarmonicDistOn.apply_lapTest_eq_zero (hrel ω).2 hω hU hUV f
      have h0' := IsHarmonicDistOn.apply_lapTest_eq_zero (hrel ω).2 hω hU hUV f'
      have e : (h₁ ω + h₂ ω) χ = h₁ ω Ψ + h₂ ω χ := by
        rw [add_apply, hχ, map_add (h₁ ω), map_sub (h₁ ω), h0, h0']
        ring
      simp only [hWdef, e]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
    · simp [hWdef, Set.indicator_of_notMem hω']
  have hF : Integrable (fun ω => Complex.exp (Complex.I * (h₂ ω χ : ℂ))) P' :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply χ).comp hh₂)
  rw [hstep1, integral_mul_condExp_of_bdd h𝒢le hWm hWb hF]
  have hcχ := hcond χ
  rw [integral_congr_ae (hcχ.mono fun ω hω => by
    show W ω * (P'[fun ω => Complex.exp (Complex.I * (h₂ ω χ : ℂ))|twoStepSigma A' h₁]) ω = _
    rw [hω]), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  by_cases hω' : ω ∈ E'
  · have hUV : (U : Set ℂ) ⊆ H \ A' ω := fun z hz =>
      ⟨hU hz, fun hzA => Set.disjoint_left.1 hω' hzA hz⟩
    simp only [hWdef]
    rw [zeroGFFTestCov_lapTest_sub_add hU (hrel ω).2 sdiff_subset hUV]
    rw [show -(1 / 2 : ℝ) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
        2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫ + zeroGFFTestCov (H \ A' ω) Ψ Ψ) =
        -(1 / 2) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
          2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫) +
        -(1 / 2) * zeroGFFTestCov (H \ A' ω) Ψ Ψ by ring, Real.exp_add]
    push_cast
    ring
  · simp [hWdef, Set.indicator_of_notMem hω']

end Model

/-! ### Transfer to the coupling -/

section Transfer

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The weighted characteristic function of `(h, f)_∇ − (h, f')_∇ + h(Ψ)` on the avoidance event
factors as a Dirichlet-energy term times a constant independent of `f, f'`. -/
theorem exists_const_integral_exp_lapTest {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : IsLocalSet A h P) {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    {k : Set ℂ → ℂ} (hk : Measurable[hittingSigma] k) (hkb : ∀ S, ‖k S‖ ≤ 1)
    (Ψ : TestOn upperHalfPlaneOpens) :
    ∃ J : ℂ, ∀ f f' : zsSub (U : Set ℂ),
      ∫ ω, {ω | Disjoint (A ω) U}.indicator (fun ω => k (A ω)) ω *
          Complex.exp (Complex.I * (h ω (lapTest U f - lapTest U f' + Ψ) : ℂ)) ∂P =
        ((Real.exp (-(1 / 2) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
          2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫)) : ℝ) : ℂ) * J := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hAh, -, Ω', mΩ', P', hP', A', h₁, h₂, hA'm, hh₁m, hh₂m, hrel, hharm, hcond, hlaw⟩ :=
    hloc
  refine ⟨∫ ω, {ω | Disjoint (A' ω) U}.indicator (fun ω => k (A' ω)) ω *
    Complex.exp (Complex.I * (h₁ ω Ψ : ℂ)) *
    ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A' ω) Ψ Ψ) : ℝ) : ℂ) ∂P', fun f f' => ?_⟩
  rw [← integral_exp_lapTest_model hA'm hh₁m hh₂m hrel hharm hcond hU hk hkb Ψ f f']
  set χ := lapTest U f - lapTest U f' + Ψ
  let F : Set ℂ × DistOn upperHalfPlaneOpens → ℂ := fun p =>
    {S : Set ℂ | Disjoint S U}.indicator k p.1 * Complex.exp (Complex.I * (p.2 χ : ℂ))
  have hFm : Measurable F :=
    ((hk.indicator (measurableSet_avoid U.isOpen hU)).comp measurable_fst).mul
      (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_distOn_apply χ).comp measurable_snd))))
  have hZ' : AEMeasurable (fun ω => (A' ω, h₁ ω + h₂ ω)) P' :=
    (hA'm.prodMk (measurable_distOn_iff.2 fun φ =>
      ((measurable_distOn_apply φ).comp hh₁m).add ((measurable_distOn_apply φ).comp hh₂m))).aemeasurable
  have e1 : ∫ ω, F (A ω, h ω) ∂P = ∫ ω, F (A' ω, h₁ ω + h₂ ω) ∂P' := by
    rw [← integral_map hAh hFm.aestronglyMeasurable, ← hlaw,
      integral_map hZ' hFm.aestronglyMeasurable]
  have hF1 : ∀ ω, F (A ω, h ω) = {ω | Disjoint (A ω) U}.indicator (fun ω => k (A ω)) ω *
      Complex.exp (Complex.I * (h ω χ : ℂ)) := fun ω => by
    simp only [F]
    by_cases hω : Disjoint (A ω) (U : Set ℂ)
    · rw [Set.indicator_of_mem (show A ω ∈ {S : Set ℂ | Disjoint S U} from hω),
        Set.indicator_of_mem (show ω ∈ {ω | Disjoint (A ω) U} from hω)]
    · rw [Set.indicator_of_notMem (show A ω ∉ {S : Set ℂ | Disjoint S U} from hω),
        Set.indicator_of_notMem (show ω ∉ {ω | Disjoint (A ω) U} from hω)]
  have hF2 : ∀ ω, F (A' ω, h₁ ω + h₂ ω) = {ω | Disjoint (A' ω) U}.indicator
      (fun ω => k (A' ω)) ω * Complex.exp (Complex.I * ((h₁ ω + h₂ ω) χ : ℂ)) := fun ω => by
    simp only [F]
    by_cases hω : Disjoint (A' ω) (U : Set ℂ)
    · rw [Set.indicator_of_mem (show A' ω ∈ {S : Set ℂ | Disjoint S U} from hω),
        Set.indicator_of_mem (show ω ∈ {ω | Disjoint (A' ω) U} from hω)]
    · rw [Set.indicator_of_notMem (show A' ω ∉ {S : Set ℂ | Disjoint S U} from hω),
        Set.indicator_of_notMem (show ω ∉ {ω | Disjoint (A' ω) U} from hω)]
  simp_rw [← hF1, ← hF2]
  exact e1

/-- The Dirichlet-energy exponent at the limit: `‖a − c‖² + 2⟪a − c, c⟫ = ‖a‖² − ‖c‖²`. -/
lemma norm_sub_sq_add_two_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a c : E) : ‖a - c‖ ^ 2 + 2 * ⟪a - c, c⟫ = ‖a‖ ^ 2 - ‖c‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_sub_left, real_inner_self_eq_norm_sq]
  ring

/-- **The avoidance identity (3.6), characteristic-function form, before normalization.** For the
Markov decomposition `h = X + Y`, `X = G h`, on `U ⊆ ℍ`:
`E[1_E k(A) e^{i(X(Φ) + Y(Ψ))}] = e^{−(‖c_Φ − c_Ψ‖² + 2⟪c_Φ − c_Ψ, c_Ψ⟫)/2} J` with `J` independent
of `Φ`. -/
theorem exists_const_integral_exp_markov {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) (hloc : IsLocalSet A h P) {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    {k : Set ℂ → ℂ} (hk : Measurable[hittingSigma] k) (hkb : ∀ S, ‖k S‖ ≤ 1)
    (hAm : Measurable[mΩ, hittingSigma] A) (Ψ : TestOn upperHalfPlaneOpens) :
    ∃ J : ℂ, ∀ Φ : TestOn upperHalfPlaneOpens,
      ∫ ω, {ω | Disjoint (A ω) U}.indicator (fun ω => k (A ω)) ω *
          Complex.exp (Complex.I * ((G (h ω) Φ + markovCompl G (h ω) Ψ : ℝ) : ℂ)) ∂P =
        ((Real.exp (-(1 / 2) * (‖covVec U Φ - covVec U Ψ‖ ^ 2 +
          2 * ⟪covVec U Φ - covVec U Ψ, covVec U Ψ⟫)) : ℝ) : ℂ) * J := by
  obtain ⟨J, hJ⟩ := exists_const_integral_exp_lapTest hloc hU hk hkb Ψ
  refine ⟨J, fun Φ => ?_⟩
  obtain ⟨f, hf, hf2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd Φ
  obtain ⟨f', hf', hf2'⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd Ψ
  set W : Ω → ℂ := fun ω => {ω | Disjoint (A ω) U}.indicator (fun ω => k (A ω)) ω with hWdef
  have hWm : Measurable W :=
    (hk.comp hAm).indicator (hAm (measurableSet_avoid U.isOpen hU))
  have hWb : ∀ ω, ‖W ω‖ ≤ 1 := by
    intro ω
    simp only [hWdef]
    by_cases hω : ω ∈ {ω | Disjoint (A ω) (U : Set ℂ)}
    · rw [Set.indicator_of_mem hω]; exact hkb _
    · rw [Set.indicator_of_notMem hω, norm_zero]; exact zero_le_one
  set b : Ω → ℝ := fun ω => G (h ω) Φ + markovCompl G (h ω) Ψ with hbdef
  set a : ℕ → Ω → ℝ := fun n ω => h ω (lapTest U (f n) - lapTest U (f' n) + Ψ) with hadef
  set L : ℕ → ℂ := fun n => ∫ ω, W ω * Complex.exp (Complex.I * (a n ω : ℂ)) ∂P with hLdef
  -- the limit of the right-hand sides
  have hlim1 : Tendsto L atTop (𝓝 (((Real.exp (-(1 / 2) * (‖covVec U Φ - covVec U Ψ‖ ^ 2 +
      2 * ⟪covVec U Φ - covVec U Ψ, covVec U Ψ⟫)) : ℝ) : ℂ) * J)) := by
    have e : L = fun n => ((Real.exp (-(1 / 2) * (‖gradFeat U (f n).1 - gradFeat U (f' n).1‖ ^ 2 +
        2 * ⟪gradFeat U (f n).1 - gradFeat U (f' n).1, covVec U Ψ⟫)) : ℝ) : ℂ) * J :=
      funext fun n => hJ (f n) (f' n)
    rw [e]
    have hconv : Tendsto (fun n => gradFeat (U : Set ℂ) (f n).1 - gradFeat U (f' n).1) atTop
        (𝓝 (covVec U Φ - covVec U Ψ)) := hf.sub hf'
    refine Tendsto.mul_const J (Complex.continuous_ofReal.continuousAt.tendsto.comp ?_)
    refine Real.continuous_exp.continuousAt.tendsto.comp (Tendsto.const_mul _ ?_)
    exact ((continuous_norm.tendsto _).comp hconv).pow 2 |>.add
      (Tendsto.const_mul _ (hconv.inner tendsto_const_nhds))
  -- the left-hand sides converge to the target
  have hZ : ∀ n, MemLp (fun ω => a n ω - b ω) 2 P := by
    intro n
    have e : (fun ω => a n ω - b ω) = fun ω => (G (h ω) Ψ - h ω (lapTest U (f' n))) -
        (G (h ω) Φ - h ω (lapTest U (f n))) := by
      funext ω
      simp only [hadef, hbdef, markovCompl, map_add, map_sub, sub_apply]
      ring
    rw [e]
    exact (memLp_markov_sub_lapTest hU hd Ψ (f' n)).sub (memLp_markov_sub_lapTest hU hd Φ (f n))
  have hbound : ∀ n, ‖L n - ∫ ω, W ω * Complex.exp (Complex.I * (b ω : ℂ)) ∂P‖ ^ 2 ≤
      2 * ∫ ω, (G (h ω) Ψ - h ω (lapTest U (f' n))) ^ 2 ∂P +
        2 * ∫ ω, (G (h ω) Φ - h ω (lapTest U (f n))) ^ 2 ∂P := by
    intro n
    have hint : ∀ c : Ω → ℝ, Measurable c →
        Integrable (fun ω => W ω * Complex.exp (Complex.I * (c ω : ℂ))) P := fun c hc =>
      (GFF.integrable_exp_I_mul hc).bdd_mul hWm.aestronglyMeasurable
        (Eventually.of_forall hWb)
    have ham : Measurable (a n) := (measurable_distOn_apply _).comp hhm
    have hbm : Measurable b :=
      ((measurable_distOn_apply Φ).comp (hG.comp hhm)).add
        ((measurable_distOn_apply Ψ).comp ((measurable_markovCompl hG).comp hhm))
    rw [hLdef, ← integral_sub (hint _ ham) (hint _ hbm)]
    have e : (fun ω => W ω * Complex.exp (Complex.I * (a n ω : ℂ)) -
        W ω * Complex.exp (Complex.I * (b ω : ℂ))) = fun ω =>
        (Complex.exp (Complex.I * (a n ω : ℂ)) - Complex.exp (Complex.I * (b ω : ℂ))) * W ω := by
      funext ω; ring
    rw [e]
    refine (norm_integral_exp_sub_sq_le hWb (hZ n)).trans ?_
    have e2 : (fun ω => (a n ω - b ω) ^ 2) = fun ω => ((G (h ω) Ψ - h ω (lapTest U (f' n))) -
        (G (h ω) Φ - h ω (lapTest U (f n)))) ^ 2 := by
      funext ω
      simp only [hadef, hbdef, markovCompl, map_add, map_sub, sub_apply]
      ring_nf
    rw [e2]
    have i1 := (memLp_markov_sub_lapTest hU hd Ψ (f' n)).integrable_sq
    have i2 := (memLp_markov_sub_lapTest hU hd Φ (f n)).integrable_sq
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
    refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
      ((i1.const_mul 2).add (i2.const_mul 2)) (Eventually.of_forall fun ω => ?_)
    nlinarith [sq_nonneg ((G (h ω) Ψ - h ω (lapTest U (f' n))) +
      (G (h ω) Φ - h ω (lapTest U (f n))))]
  have hlim2 : Tendsto L atTop (𝓝 (∫ ω, W ω * Complex.exp (Complex.I * (b ω : ℂ)) ∂P)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsum : Tendsto (fun n => 2 * ∫ ω, (G (h ω) Ψ - h ω (lapTest U (f' n))) ^ 2 ∂P +
        2 * ∫ ω, (G (h ω) Φ - h ω (lapTest U (f n))) ^ 2 ∂P) atTop (𝓝 0) := by
      simpa using (hf2'.const_mul 2).add (hf2.const_mul 2)
    have hsq : Tendsto (fun n => Real.sqrt (2 * ∫ ω, (G (h ω) Ψ - h ω (lapTest U (f' n))) ^ 2 ∂P +
        2 * ∫ ω, (G (h ω) Φ - h ω (lapTest U (f n))) ^ 2 ∂P)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hsum
      rw [Real.sqrt_zero] at this
      exact this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsq
    exact Real.le_sqrt_of_sq_le (hbound n)
  have := tendsto_nhds_unique hlim2 hlim1
  simpa [hWdef, hbdef] using this

/-- The characteristic function of the Markov projection: `E e^{i h_U(Φ)} = e^{−‖covVec U Φ‖²/2}`. -/
theorem integral_exp_markov {h hU' : Ω → DistOn upperHalfPlaneOpens} {U : Opens ℂ}
    (hU : U ≤ upperHalfPlaneOpens) (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h hU' P)
    (Φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, Complex.exp (Complex.I * (hU' ω Φ : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * ‖covVec U Φ‖ ^ 2) : ℝ) : ℂ) := by
  have hm : AEMeasurable (fun ω => hU' ω Φ) P :=
    ((measurable_distOn_apply Φ).comp hd.isZBGFFExtOn.measurable).aemeasurable
  rw [GFF.integral_exp_I_mul_of_hasGaussianLaw (hd.isZBGFFExtOn.gaussian.hasGaussianLaw_eval Φ)
    (hd.isZBGFFExtOn.centered Φ), variance_of_integral_eq_zero hm (hd.isZBGFFExtOn.centered Φ),
    integral_sq_of_isZBGFFExtOn hU hd.isZBGFFExtOn Φ]

/-- **The avoidance identity (3.6), characteristic-function form.** For a local set `A` of a
zero-boundary GFF `h` on `ℍ`, the Markov decomposition `h = X + Y` on `U ⊆ ℍ` and a bounded
measurable `k`, `E[1_E k(A) e^{iX(Φ)} e^{iY(Ψ)}] = E[e^{iX(Φ)}] · E[1_E k(A) e^{iY(Ψ)}]`. -/
theorem integral_indicator_exp_markov {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) (hAm : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    {k : Set ℂ → ℂ} (hk : Measurable[hittingSigma] k) (hkb : ∀ S, ‖k S‖ ≤ 1)
    (Φ Ψ : TestOn upperHalfPlaneOpens) :
    ∫ ω, {ω | Disjoint (A ω) U}.indicator (fun ω => k (A ω)) ω *
        (Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))) ∂P =
      (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
        ∫ ω, {ω | Disjoint (A ω) U}.indicator (fun ω => k (A ω)) ω *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P := by
  obtain ⟨J, hJ⟩ := exists_const_integral_exp_markov hhm hloc hU hG hd hk hkb hAm Ψ
  have hΦ := hJ Φ
  have h0 := hJ 0
  have hcov0 : covVec (U : Set ℂ) ⇑(0 : TestOn upperHalfPlaneOpens) = 0 :=
    covVec_zero _ U.isOpen hU
  simp only [map_zero, zero_add, hcov0] at h0
  rw [norm_sub_sq_add_two_inner] at hΦ h0
  have e : ∀ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
      Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) =
      Complex.exp (Complex.I * ((G (h ω) Φ + markovCompl G (h ω) Ψ : ℝ) : ℂ)) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [hΦ, h0, integral_exp_markov hU hd Φ]
  rw [show -(1 / 2 : ℝ) * (‖covVec U Φ‖ ^ 2 - ‖covVec U Ψ‖ ^ 2) =
    -(1 / 2) * ‖covVec U Φ‖ ^ 2 + -(1 / 2) * (‖(0 : GradSpace U)‖ ^ 2 - ‖covVec U Ψ‖ ^ 2) by
      simp; ring, Real.exp_add]
  push_cast
  ring

end Transfer

/-! ### Extension to the marked σ-algebra and the conditional independence -/

section Marked

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integrable_exp_mul_exp {a b : Ω → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Integrable (fun ω => Complex.exp (Complex.I * (a ω : ℂ)) *
      Complex.exp (Complex.I * (b ω : ℂ))) P :=
  (GFF.integrable_exp_I_mul hb).bdd_mul (GFF.measurable_exp_I_mul ha).aestronglyMeasurable
    (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal (a ω)).le)

omit mΩ [IsProbabilityMeasure P] in
/-- The marked σ-algebra is generated by the π-system of the events `E ∩ {A ∈ B}` and their
complements. -/
theorem markedSigma_eq_generateFrom (A : Ω → Set ℂ) (U : Set ℂ) :
    markedSigma A U = MeasurableSpace.generateFrom
      {s | ∃ B : Set (Set ℂ), MeasurableSet[hittingSigma] B ∧
        (s = {ω | Disjoint (A ω) U} ∩ A ⁻¹' B ∨ s = ({ω | Disjoint (A ω) U} ∩ A ⁻¹' B)ᶜ)} := by
  refine le_antisymm (sup_le ?_ ?_) (MeasurableSpace.generateFrom_le ?_)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ rfl
    refine MeasurableSpace.measurableSet_generateFrom ⟨univ, MeasurableSet.univ, Or.inl ?_⟩
    rw [preimage_univ, inter_univ]
  · rintro _ ⟨B, hB, rfl⟩
    by_cases h0 : (∅ : Set ℂ) ∈ B
    · refine MeasurableSpace.measurableSet_generateFrom ⟨Bᶜ, hB.compl, Or.inr ?_⟩
      ext ω
      simp only [mem_preimage, mem_compl_iff, mem_inter_iff, mem_ofPred_eq, not_and, not_not]
      by_cases hω : Disjoint (A ω) U
      · simp [markedSet, hω]
      · have : markedSet U (A ω) = ∅ := by ext z; simp [markedSet, hω]
        simp [this, h0, hω]
    · refine MeasurableSpace.measurableSet_generateFrom ⟨B, hB, Or.inl ?_⟩
      ext ω
      simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq]
      by_cases hω : Disjoint (A ω) U
      · simp [markedSet, hω]
      · have : markedSet U (A ω) = ∅ := by ext z; simp [markedSet, hω]
        simp [this, h0, hω]
  · have hE : MeasurableSet[markedSigma A U] {ω | Disjoint (A ω) U} :=
      measurableSet_avoid_markedSigma A U
    have hEB : ∀ B : Set (Set ℂ), MeasurableSet[hittingSigma] B →
        MeasurableSet[markedSigma A U] ({ω | Disjoint (A ω) U} ∩ A ⁻¹' B) := by
      intro B hB
      have h1 : MeasurableSet[markedSigma A U] ((fun ω => markedSet U (A ω)) ⁻¹' B) :=
        (le_sup_right : _ ≤ markedSigma A U) _ ⟨B, hB, rfl⟩
      have e : {ω | Disjoint (A ω) U} ∩ A ⁻¹' B =
          {ω | Disjoint (A ω) U} ∩ (fun ω => markedSet U (A ω)) ⁻¹' B := by
        ext ω
        simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
        constructor
        · rintro ⟨hω, hB⟩
          refine ⟨hω, ?_⟩
          have : markedSet U (A ω) = A ω := by ext z; simp [markedSet, hω]
          rwa [this]
        · rintro ⟨hω, hB⟩
          refine ⟨hω, ?_⟩
          have : markedSet U (A ω) = A ω := by ext z; simp [markedSet, hω]
          rwa [← this]
      rw [e]
      exact hE.inter h1
    rintro _ ⟨B, hB, rfl | rfl⟩
    · exact hEB B hB
    · exact (hEB B hB).compl

omit mΩ [IsProbabilityMeasure P] in
theorem isPiSystem_marked (A : Ω → Set ℂ) (U : Set ℂ) :
    IsPiSystem {s | ∃ B : Set (Set ℂ), MeasurableSet[hittingSigma] B ∧
      (s = {ω | Disjoint (A ω) U} ∩ A ⁻¹' B ∨ s = ({ω | Disjoint (A ω) U} ∩ A ⁻¹' B)ᶜ)} := by
  rintro _ ⟨B, hB, rfl | rfl⟩ _ ⟨B', hB', rfl | rfl⟩ -
  · refine ⟨B ∩ B', hB.inter hB', Or.inl ?_⟩
    ext ω; simp only [mem_inter_iff, mem_preimage]; tauto
  · refine ⟨B ∩ B'ᶜ, hB.inter hB'.compl, Or.inl ?_⟩
    ext ω; simp only [mem_inter_iff, mem_preimage, mem_compl_iff]; tauto
  · refine ⟨B' ∩ Bᶜ, hB'.inter hB.compl, Or.inl ?_⟩
    ext ω; simp only [mem_inter_iff, mem_preimage, mem_compl_iff]; tauto
  · refine ⟨B ∪ B', hB.union hB', Or.inr ?_⟩
    ext ω; simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_union]; tauto

/-- **The marked factorization on every marked event.** For a local set `A` of a zero-boundary
GFF `h` on `ℍ` and the Markov decomposition `h = X + Y` on `U ⊆ ℍ`, for every event `m` of the
pair `(1_E, Ã)`: `∫_m e^{iX(Φ)} e^{iY(Ψ)} = E[e^{iX(Φ)}] · ∫_m e^{iY(Ψ)}`. -/
theorem setIntegral_exp_markov_marked {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) (hAm : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    {U : Opens ℂ} (hU : U ≤ upperHalfPlaneOpens)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (Φ Ψ : TestOn upperHalfPlaneOpens) (m : Set Ω) (hm : MeasurableSet[markedSigma A U] m) :
    ∫ ω in m, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
      (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
        ∫ ω in m, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P := by
  have hle := markedSigma_le hAm U.isOpen hU
  have hXm : Measurable fun ω => G (h ω) Φ := (measurable_distOn_apply Φ).comp (hG.comp hhm)
  have hYm : Measurable fun ω => markovCompl G (h ω) Ψ :=
    (measurable_distOn_apply Ψ).comp ((measurable_markovCompl hG).comp hhm)
  have hF := integrable_exp_mul_exp (P := P) hXm hYm
  have hg := GFF.integrable_exp_I_mul (P := P) hYm
  set c := ∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P
  -- the identity on the whole space (independence of `X` and `Y`)
  have huniv : ∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
      Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
      c * ∫ ω, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P := by
    have hind := hd.indepFun
    have := hind.integral_fun_comp_mul_comp (f := fun T : DistOn upperHalfPlaneOpens =>
        Complex.exp (Complex.I * (T Φ : ℂ)))
      (g := fun T : DistOn upperHalfPlaneOpens => Complex.exp (Complex.I * (T Ψ : ℂ)))
      (hG.comp hhm).aemeasurable ((measurable_markovCompl hG).comp hhm).aemeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply Φ)).aestronglyMeasurable
      (GFF.measurable_exp_I_mul (measurable_distOn_apply Ψ)).aestronglyMeasurable
    simpa [markovCompl] using this
  -- the π–λ induction
  refine MeasurableSpace.induction_on_inter (m := markedSigma A U)
    (C := fun s _ => ∫ ω in s, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
      c * ∫ ω in s, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P)
    (markedSigma_eq_generateFrom A U) (isPiSystem_marked A U) (by simp) ?_ ?_ ?_ m hm
  · -- basic sets
    have hbasic : ∀ B : Set (Set ℂ), MeasurableSet[hittingSigma] B →
        ∫ ω in {ω | Disjoint (A ω) U} ∩ A ⁻¹' B, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
        c * ∫ ω in {ω | Disjoint (A ω) U} ∩ A ⁻¹' B,
          Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P := by
      intro B hB
      have hs : MeasurableSet ({ω | Disjoint (A ω) U} ∩ A ⁻¹' B) :=
        (hAm (measurableSet_avoid U.isOpen hU)).inter (hAm hB)
      set k : Set ℂ → ℂ := B.indicator fun _ => 1
      have hk : Measurable[hittingSigma] k := measurable_const.indicator hB
      have hkb : ∀ S, ‖k S‖ ≤ 1 := fun S => by
        by_cases hS : S ∈ B <;> simp [k, hS]
      have hind : ∀ (F : Ω → ℂ), ({ω | Disjoint (A ω) U} ∩ A ⁻¹' B).indicator F =
          fun ω => {ω | Disjoint (A ω) U}.indicator (fun ω => k (A ω)) ω * F ω := by
        intro F; funext ω
        by_cases h1 : Disjoint (A ω) (U : Set ℂ) <;> by_cases h2 : A ω ∈ B <;>
          simp [k, h1, h2, Set.indicator, mem_inter_iff]
      rw [← integral_indicator hs, ← integral_indicator hs, hind, hind]
      exact integral_indicator_exp_markov hhm hAm hloc hU hG hd hk hkb Φ Ψ
    rintro _ ⟨B, hB, rfl | rfl⟩
    · exact hbasic B hB
    · have hs : MeasurableSet ({ω | Disjoint (A ω) U} ∩ A ⁻¹' B) :=
        (hAm (measurableSet_avoid U.isOpen hU)).inter (hAm hB)
      rw [setIntegral_compl hs hF, setIntegral_compl hs hg, huniv, hbasic B hB, mul_sub]
  · -- complements
    intro t ht hC
    rw [setIntegral_compl (hle t ht) hF, setIntegral_compl (hle t ht) hg, huniv, hC, mul_sub]
  · -- disjoint unions
    intro f hdisj hfm hC
    have hfm' : ∀ i, MeasurableSet (f i) := fun i => hle _ (hfm i)
    have h1 := hasSum_integral_iUnion hfm' hdisj hF.integrableOn
    have h2 := (hasSum_integral_iUnion hfm' hdisj hg.integrableOn).mul_left c
    simp_rw [hC] at h1
    exact h1.unique h2

/-- **Lemma 3.6, (iv) ⇒ (ii).** A local set of a zero-boundary GFF on `ℍ` satisfies the marked
avoidance criterion (ii): for every open `U ⊆ ℍ` and every Borel version `G` of the projection
onto `H(U)`, given `h − G h`, the pair `(S, Ã)` is conditionally independent of `G h`. -/
theorem IsLocalSet.isMarkedAvoidanceLocal {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hhm : Measurable h) (hAm : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P) :
    IsMarkedAvoidanceLocal A h P := by
  intro U G hUH hG hd
  have hU : U ≤ upperHalfPlaneOpens := hUH
  have hXm : Measurable fun ω => G (h ω) := hG.comp hhm
  have hYm : Measurable fun ω => markovCompl G (h ω) := (measurable_markovCompl hG).comp hhm
  have hMle := markedSigma_le hAm U.isOpen hUH
  have hind := indep_comap_sup_of_setIntegral_exp hXm hYm hMle
    (setIntegral_exp_markov_marked hhm hAm hloc hU hG hd)
  have hXle := hXm.comap_le
  have hYle := hYm.comap_le
  refine (LQGMetric.condIndepEv_of_condExp_sup_eq hYle hXle hMle fun a ha => ?_).symm
  have hfa : StronglyMeasurable[MeasurableSpace.comap (fun ω => G (h ω)) inferInstance]
      (a.indicator fun _ => (1 : ℝ)) :=
    (stronglyMeasurable_const.indicator ha)
  have hind1 : Indep (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance)
      (markedSigma A U ⊔ MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P := by
    rw [sup_comm]; exact hind
  have hind2 : Indep (MeasurableSpace.comap (fun ω => G (h ω)) inferInstance)
      (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P :=
    indep_of_indep_of_le_right hind le_sup_left
  have e1 := condExp_indep_eq (m₁ := MeasurableSpace.comap (fun ω => G (h ω)) inferInstance)
    (m₂ := markedSigma A U ⊔ MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
    hXle (sup_le hMle hYle) hfa hind1
  have e2 := condExp_indep_eq (m₁ := MeasurableSpace.comap (fun ω => G (h ω)) inferInstance)
    (m₂ := MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance)
    hXle hYle hfa hind2
  exact e1.trans e2.symm

end Marked

end LocalSets
end InteractingSLE
