/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.MarkedAvoidance

/-!
# A retained-range Gaussian kernel makes the conditioning information local

Packet PROVE-WHOLEFIELD8 (specification Aux. lemma 16, last sentence, `source/spec/p049-096.md#aux-16`, p. 90: "In
particular, the stopped range, together with its driving history, is a local exploration"; Aux. lemma 56, p. 249).

Let `h` be a zero-boundary GFF on `ℍ`, `U ⊆ ℍ` a deterministic open set, `X = P_U h` (a Borel version `G` of the
projection onto `H(U)`) and `Y = h − X`. Suppose that, given a σ-algebra `𝒦`, the conditional law of the whole field
is Gaussian with a mean `M` harmonic on a random open set `V ⊇ U` and the zero-boundary Green covariance of `V`:

  `E[e^{i(h,χ)} | 𝒦] = exp(i M(χ) − ½ G_V(χ, χ))`  for every test `χ`.

Then `X` is independent of `Y` together with `𝒦` (`setIntegral_exp_markov_of_kernel`). The proof is the one of
Lemma 3.6, (iv) ⇒ (ii) (`LocalSets.integral_exp_lapTest_model`, `LocalSets.exists_const_integral_exp_markov`), with the
two-step model replaced by the kernel: the mean annihilates the Dirichlet pairings of `C_c^∞(U)` and the Gram vectors of
`C_c^∞(U)` do not depend on the domain `V ⊇ U`.

The identity passes to the join of an increasing sequence of such σ-algebras and to every σ-algebra whose events are
almost surely equal to events of that join (`setIntegral_exp_markov_of_iSup`); the conditional independence follows
(`condIndepEv_of_kernels`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE

namespace WholeField

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB LocalSets

section Kernel

variable {Ω : Type*} {𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {U : Opens ℂ} {V : Ω → Set ℂ}
  {M : Ω → DistOn upperHalfPlaneOpens}

/-- The Gaussian kernel value `exp(i M(χ) − ½ G_V(χ, χ))`. -/
def rangeKerCF (M : DistOn upperHalfPlaneOpens) (V : Set ℂ) (χ : TestOn upperHalfPlaneOpens) : ℂ :=
  Complex.exp (Complex.I * (M χ : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov V χ χ : ℝ) : ℂ))

/-- **The kernel on the Dirichlet pairings of `C_c^∞(U)`.** For `χ = (·, f)_∇ − (·, f')_∇ + Ψ` the weighted
characteristic function factors as a Dirichlet-energy term times a constant independent of `f, f'`. -/
theorem exists_const_integral_exp_lapTest_of_kernel (h𝒦 : 𝒦 ≤ mΩ) (hU : U ≤ upperHalfPlaneOpens)
    (hV : ∀ᵐ ω ∂P, IsOpen (V ω) ∧ V ω ⊆ H ∧ (U : Set ℂ) ⊆ V ω ∧ IsHarmonicDistOn (M ω) (V ω))
    (hker : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      (P[fun ω' => Complex.exp (Complex.I * (h ω' χ : ℂ)) | 𝒦]) ω = rangeKerCF (M ω) (V ω) χ)
    (hhm : Measurable h) {W : Ω → ℂ} (hWm : StronglyMeasurable[𝒦] W) (hWb : ∀ ω, ‖W ω‖ ≤ 1)
    (Ψ : TestOn upperHalfPlaneOpens) :
    ∃ J : ℂ, ∀ f f' : zsSub (U : Set ℂ),
      ∫ ω, W ω * Complex.exp (Complex.I * (h ω (lapTest U f - lapTest U f' + Ψ) : ℂ)) ∂P =
        ((Real.exp (-(1 / 2) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
          2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫)) : ℝ) : ℂ) * J := by
  refine ⟨∫ ω, W ω * rangeKerCF (M ω) (V ω) Ψ ∂P, fun f f' => ?_⟩
  set χ := lapTest U f - lapTest U f' + Ψ with hχ
  have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω χ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply χ).comp hhm)
  rw [integral_mul_condExp_of_bdd h𝒦 hWm hWb hF, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hker χ, hV] with ω hω hVω
  obtain ⟨hVo, hVH, hUV, hMω⟩ := hVω
  rw [hω]
  have h0 := IsHarmonicDistOn.apply_lapTest_eq_zero hVo hMω hU hUV f
  have h0' := IsHarmonicDistOn.apply_lapTest_eq_zero hVo hMω hU hUV f'
  have eM : M ω χ = M ω Ψ := by
    rw [hχ, map_add (M ω), map_sub (M ω), h0, h0']
    ring
  have eV := zeroGFFTestCov_lapTest_sub_add hU hVo hVH hUV Ψ f f'
  simp only [rangeKerCF]
  rw [eM, eV]
  rw [show Complex.I * (M ω Ψ : ℂ) - (((1 / 2 : ℝ) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
      2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫ + zeroGFFTestCov (V ω) Ψ Ψ) : ℝ) : ℂ) =
      ((-(1 / 2) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
        2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫) : ℝ) : ℂ) +
      (Complex.I * (M ω Ψ : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov (V ω) Ψ Ψ : ℝ) : ℂ)) by
    push_cast; ring, Complex.exp_add, Complex.ofReal_exp]
  ring

/-- **The kernel identity transferred to the Markov projection.** For the Markov decomposition `h = X + Y`, `X = G h`,
on `U ⊆ ℍ`: `E[W e^{i(X(Φ) + Y(Ψ))}] = e^{−(‖c_Φ − c_Ψ‖² + 2⟪c_Φ − c_Ψ, c_Ψ⟫)/2} J` with `J` independent of `Φ`
(the limit argument of `LocalSets.exists_const_integral_exp_markov`, with a general bounded `𝒦`-measurable weight). -/
theorem exists_const_integral_exp_markov_of_kernel (h𝒦 : 𝒦 ≤ mΩ) (hU : U ≤ upperHalfPlaneOpens)
    (hV : ∀ᵐ ω ∂P, IsOpen (V ω) ∧ V ω ⊆ H ∧ (U : Set ℂ) ⊆ V ω ∧ IsHarmonicDistOn (M ω) (V ω))
    (hker : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      (P[fun ω' => Complex.exp (Complex.I * (h ω' χ : ℂ)) | 𝒦]) ω = rangeKerCF (M ω) (V ω) χ)
    (hhm : Measurable h) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    {W : Ω → ℂ} (hWm : StronglyMeasurable[𝒦] W) (hWb : ∀ ω, ‖W ω‖ ≤ 1) (Ψ : TestOn upperHalfPlaneOpens) :
    ∃ J : ℂ, ∀ Φ : TestOn upperHalfPlaneOpens,
      ∫ ω, W ω * Complex.exp (Complex.I * ((G (h ω) Φ + markovCompl G (h ω) Ψ : ℝ) : ℂ)) ∂P =
        ((Real.exp (-(1 / 2) * (‖covVec U Φ - covVec U Ψ‖ ^ 2 +
          2 * ⟪covVec U Φ - covVec U Ψ, covVec U Ψ⟫)) : ℝ) : ℂ) * J := by
  obtain ⟨J, hJ⟩ := exists_const_integral_exp_lapTest_of_kernel h𝒦 hU hV hker hhm hWm hWb Ψ
  refine ⟨J, fun Φ => ?_⟩
  obtain ⟨f, hf, hf2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd Φ
  obtain ⟨f', hf', hf2'⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd Ψ
  have hWm' : Measurable W := (hWm.mono h𝒦).measurable
  set b : Ω → ℝ := fun ω => G (h ω) Φ + markovCompl G (h ω) Ψ with hbdef
  set a : ℕ → Ω → ℝ := fun n ω => h ω (lapTest U (f n) - lapTest U (f' n) + Ψ) with hadef
  set L : ℕ → ℂ := fun n => ∫ ω, W ω * Complex.exp (Complex.I * (a n ω : ℂ)) ∂P with hLdef
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
      (GFF.integrable_exp_I_mul hc).bdd_mul hWm'.aestronglyMeasurable (Eventually.of_forall hWb)
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
  exact tendsto_nhds_unique hlim2 hlim1

/-- **The factorization (3.6) given the kernel.** For a bounded `𝒦`-measurable weight `W`:
`E[W e^{iX(Φ)} e^{iY(Ψ)}] = E[e^{iX(Φ)}] · E[W e^{iY(Ψ)}]`. -/
theorem integral_mul_exp_markov_of_kernel (h𝒦 : 𝒦 ≤ mΩ) (hU : U ≤ upperHalfPlaneOpens)
    (hV : ∀ᵐ ω ∂P, IsOpen (V ω) ∧ V ω ⊆ H ∧ (U : Set ℂ) ⊆ V ω ∧ IsHarmonicDistOn (M ω) (V ω))
    (hker : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      (P[fun ω' => Complex.exp (Complex.I * (h ω' χ : ℂ)) | 𝒦]) ω = rangeKerCF (M ω) (V ω) χ)
    (hhm : Measurable h) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    {W : Ω → ℂ} (hWm : StronglyMeasurable[𝒦] W) (hWb : ∀ ω, ‖W ω‖ ≤ 1) (Φ Ψ : TestOn upperHalfPlaneOpens) :
    ∫ ω, W ω * (Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))) ∂P =
      (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
        ∫ ω, W ω * Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P := by
  obtain ⟨J, hJ⟩ := exists_const_integral_exp_markov_of_kernel h𝒦 hU hV hker hhm hG hd hWm hWb Ψ
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

/-- **The factorization on every event of `𝒦`**: `∫_m e^{iX(Φ)} e^{iY(Ψ)} = E[e^{iX(Φ)}] · ∫_m e^{iY(Ψ)}`. -/
theorem setIntegral_exp_markov_of_kernel (h𝒦 : 𝒦 ≤ mΩ) (hU : U ≤ upperHalfPlaneOpens)
    (hV : ∀ᵐ ω ∂P, IsOpen (V ω) ∧ V ω ⊆ H ∧ (U : Set ℂ) ⊆ V ω ∧ IsHarmonicDistOn (M ω) (V ω))
    (hker : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      (P[fun ω' => Complex.exp (Complex.I * (h ω' χ : ℂ)) | 𝒦]) ω = rangeKerCF (M ω) (V ω) χ)
    (hhm : Measurable h) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (Φ Ψ : TestOn upperHalfPlaneOpens) (m : Set Ω) (hm : MeasurableSet[𝒦] m) :
    ∫ ω in m, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P =
      (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
        ∫ ω in m, Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P := by
  have hm' : MeasurableSet m := h𝒦 _ hm
  have hW : StronglyMeasurable[𝒦] (m.indicator fun _ => (1 : ℂ)) :=
    stronglyMeasurable_const.indicator hm
  have hWb : ∀ ω, ‖m.indicator (fun _ => (1 : ℂ)) ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ m <;> simp [hω]
  have key := integral_mul_exp_markov_of_kernel h𝒦 hU hV hker hhm hG hd hW hWb Φ Ψ
  have e : ∀ F : Ω → ℂ, (fun ω => m.indicator (fun _ => (1 : ℂ)) ω * F ω) = m.indicator F := fun F => by
    funext ω; by_cases hω : ω ∈ m <;> simp [hω]
  rw [e, e, integral_indicator hm', integral_indicator hm'] at key
  exact key

end Kernel

section Join

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → DistOn upperHalfPlaneOpens}

/-- The factorization identity of two random distributions on an event `m`. -/
def FactorsOn (P : Measure Ω) (X Y : Ω → DistOn upperHalfPlaneOpens) (m : Set Ω) : Prop :=
  ∀ Φ Ψ : TestOn upperHalfPlaneOpens,
    ∫ ω in m, Complex.exp (Complex.I * (X ω Φ : ℂ)) * Complex.exp (Complex.I * (Y ω Ψ : ℂ)) ∂P =
      (∫ ω, Complex.exp (Complex.I * (X ω Φ : ℂ)) ∂P) * ∫ ω in m, Complex.exp (Complex.I * (Y ω Ψ : ℂ)) ∂P

omit [IsProbabilityMeasure P] in
/-- The factorization identity only depends on the event up to a null set. -/
theorem FactorsOn.congr_ae {m m' : Set Ω} (hm : FactorsOn P X Y m) (hmm' : m =ᵐ[P] m') :
    FactorsOn P X Y m' := by
  intro Φ Ψ
  rw [← setIntegral_congr_set hmm', ← setIntegral_congr_set hmm']
  exact hm Φ Ψ

/-- **The factorization identity passes to the join of an increasing sequence of σ-algebras** (π–λ: the union of the
σ-algebras is a π-system generating the join; complements use the identity on the whole space, disjoint unions the
countable additivity of the integrals). -/
theorem factorsOn_iSup (hXm : Measurable X) (hYm : Measurable Y) {𝒦 : ℕ → MeasurableSpace Ω}
    (hmono : Monotone 𝒦) (h𝒦 : ∀ n, 𝒦 n ≤ mΩ) (hid : ∀ n m, MeasurableSet[𝒦 n] m → FactorsOn P X Y m)
    (m : Set Ω) (hm : MeasurableSet[⨆ n, 𝒦 n] m) : FactorsOn P X Y m := by
  intro Φ Ψ
  have hXΦ : Measurable fun ω => X ω Φ := (measurable_distOn_apply Φ).comp hXm
  have hYΨ : Measurable fun ω => Y ω Ψ := (measurable_distOn_apply Ψ).comp hYm
  have hF := integrable_exp_mul_exp (P := P) hXΦ hYΨ
  have hg := GFF.integrable_exp_I_mul (P := P) hYΨ
  set c := ∫ ω, Complex.exp (Complex.I * (X ω Φ : ℂ)) ∂P
  have hle : (⨆ n, 𝒦 n) ≤ mΩ := iSup_le h𝒦
  have huniv := hid 0 univ MeasurableSet.univ Φ Ψ
  simp only [Measure.restrict_univ] at huniv
  refine MeasurableSpace.induction_on_inter (m := ⨆ n, 𝒦 n)
    (C := fun s _ => ∫ ω in s, Complex.exp (Complex.I * (X ω Φ : ℂ)) *
        Complex.exp (Complex.I * (Y ω Ψ : ℂ)) ∂P =
      c * ∫ ω in s, Complex.exp (Complex.I * (Y ω Ψ : ℂ)) ∂P)
    (MeasurableSpace.generateFrom_iUnion_measurableSet 𝒦).symm
    (isPiSystem_iUnion_of_monotone _ (fun n => @MeasurableSpace.isPiSystem_measurableSet Ω (𝒦 n))
      fun _ _ hnm _ hs => hmono hnm _ hs) (by simp) ?_ ?_ ?_ m hm
  · intro s hs
    obtain ⟨n, hn⟩ := mem_iUnion.1 hs
    exact hid n s hn Φ Ψ
  · intro t ht hC
    rw [setIntegral_compl (hle t ht) hF, setIntegral_compl (hle t ht) hg, huniv, hC, mul_sub]
  · intro f hdisj hfm hC
    have hfm' : ∀ i, MeasurableSet (f i) := fun i => hle _ (hfm i)
    have h1 := hasSum_integral_iUnion hfm' hdisj hF.integrableOn
    have h2 := (hasSum_integral_iUnion hfm' hdisj hg.integrableOn).mul_left c
    simp_rw [hC] at h1
    exact h1.unique h2

end Join

section Cond

variable {Ω : Type*} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {X Y : Ω → DistOn upperHalfPlaneOpens}

/-- **From the factorization to the conditional independence.** If `X` and `Y` are measurable and the factorization
identity holds on every event of a σ-algebra `𝓜 ≤ mΩ`, then given `Y` the σ-algebra `𝓜` is conditionally independent
of `X` (the last step of `LocalSets.IsLocalSet.isMarkedAvoidanceLocal`). -/
theorem condIndepEv_of_factorsOn (hXm : Measurable X) (hYm : Measurable Y)
    (h𝓜 : 𝓜 ≤ mΩ) (hid : ∀ m, MeasurableSet[𝓜] m → FactorsOn P X Y m) :
    CondIndepEv (MeasurableSpace.comap Y inferInstance) 𝓜 (MeasurableSpace.comap X inferInstance) P := by
  have hind := indep_comap_sup_of_setIntegral_exp hXm hYm h𝓜 fun Φ Ψ m hm => hid m hm Φ Ψ
  have hXle := hXm.comap_le
  have hYle := hYm.comap_le
  refine (LQGMetric.condIndepEv_of_condExp_sup_eq hYle hXle h𝓜 fun a ha => ?_).symm
  have hfa : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (a.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator ha
  have hind1 : Indep (MeasurableSpace.comap X inferInstance)
      (𝓜 ⊔ MeasurableSpace.comap Y inferInstance) P := by
    rw [sup_comm]; exact hind
  have hind2 : Indep (MeasurableSpace.comap X inferInstance) (MeasurableSpace.comap Y inferInstance) P :=
    indep_of_indep_of_le_right hind le_sup_left
  have e1 := condExp_indep_eq (m₁ := MeasurableSpace.comap X inferInstance)
    (m₂ := 𝓜 ⊔ MeasurableSpace.comap Y inferInstance) hXle (sup_le h𝓜 hYle) hfa hind1
  have e2 := condExp_indep_eq (m₁ := MeasurableSpace.comap X inferInstance)
    (m₂ := MeasurableSpace.comap Y inferInstance) hXle hYle hfa hind2
  exact e1.trans e2.symm

end Cond

end WholeField

end InteractingSLE
