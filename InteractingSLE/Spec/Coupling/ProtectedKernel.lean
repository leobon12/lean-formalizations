import InteractingSLE.Spec.Coupling.StopFamily
import InteractingSLE.GFF.LocalSets.SubdomainCov
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The protected Gaussian kernels `Q_T^U` (Theorem 1.1, obligation 2)

Packet PROVE-T11-KER (Theorem 1.1 by Astra §1, ruling R35; obligation 2 of
`planning/handoffs/PROVE-T11-L312.md` §4). Astra, after (1.7): "Let `Q_t^U` denote the Gaussian probability kernel
on distributions on `U` with mean `m_t|_U` and covariance `G_t|_{U×U}`." For a stop `T` with `U ∩ K_T = ∅` this is
the law of `(𝔥_T + h̃⁰ ∘ f_T)|_U`, `h̃⁰` a zero-boundary GFF on `ℍ`; by conformal covariance of the Green function
(`loewnerGreenEnergy_eq_zeroGFFTestCov`) it is the law of `𝔥_T + h^{ℍ∖K_T}` restricted to `U`, with `h^{ℍ∖K_T}` a
zero-boundary GFF on `ℍ ∖ K_T`.

## Construction (own route; no conformal transport of test functions)

* `zbLaw D` : a chosen law of a zero-boundary GFF on an open `D ⊆ ℍ` (on `𝒟'(D)`; existence from the whole-plane
  GFF and SupercriticalConformalCovariance's Markov decomposition, as in `GFF.exists_markovMap`);
* `gaussLaw V D c` : the law of `h|_V + c`, `h ~ zbLaw D`, a probability measure on `𝒟'(V)` for every `V, D, c`;
  its characteristic functional is `exp(i c(ψ) − ‖ψ‖²_{H⁻¹(D)}/2)` (`integral_cexp_gaussLaw`), and its
  finite-dimensional marginals are Mathlib's `multivariateGaussian` (`map_toLp_gaussLaw`);
* `measurable_gaussLaw` : `ω ↦ gaussLaw V (D ω) (c ω)` is a measurable kernel as soon as the pairings `c ω (φ_j)`
  and the covariances `‖·‖_{H⁻¹(D ω)}` of the countable generating family `φ_j = distGen V j` are measurable
  (cylinder sets form a generating π-system and `measurable_multivariateGaussian`);
* `exists_kernel_ae_eq_gaussLaw` : the same with almost-everywhere measurable data, after a modification on a null
  set;
* `exists_protectedKernel` (below) : the kernel of the evolution.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal RealInnerProductSpace

namespace InteractingSLE

namespace Coupling

open LQGMetric GFF

/-! ### The law of a zero-boundary GFF on `D` -/

section ZBLaw

/-- A zero-boundary GFF on an open `D ⊆ ℍ` exists, as a probability law on `𝒟'(D)`. -/
theorem exists_zbLaw {D : TopologicalSpace.Opens ℂ} (hD : (D : Set ℂ) ⊆ H) :
    ∃ μ : Measure (DistOn D), IsProbabilityMeasure μ ∧ IsZeroBoundaryGFF D id μ := by
  obtain ⟨Ω₀, _, P₀, w, hP₀, hh⟩ := GFFExist.exists_wholePlaneGFF
  have hDa : ZBAdmissible D := zbAdmissible_of_subset_H hD
  obtain ⟨hzD, -, -, hzDm, hzDae, -⟩ := exists_markovMap_of_wholePlane hh (le_refl D) hDa
  have hX := SupercriticalConformalCovariance.Markov.isZeroBoundaryGFF_restrict_of_version hh hDa
    hzDm hzDae
  set X : Ω₀ → DistOn D := fun ω => restrictTo D (hzD ω) with hXdef
  have hXm : Measurable X := hX.measurable
  refine ⟨P₀.map X, inferInstance, ?_⟩
  refine ⟨measurable_id, ?_⟩
  refine
    { measurable := fun φ => measurable_distOn_apply φ
      gaussian := ⟨fun I => ?_⟩
      centered := fun φ => ?_
      covariance_eq := fun φ ψ => ?_ }
  · have hI := hX.process.gaussian.hasGaussianLaw I
    have hm : Measurable fun g : DistOn D => I.restrict fun φ => (id g : DistOn D) φ :=
      measurable_pi_iff.2 fun φ => measurable_distOn_apply φ.1
    refine ⟨hm.aemeasurable, ?_⟩
    rw [Measure.map_map hm hXm]
    exact hI.isGaussian_map
  · show ∫ g, g φ ∂(P₀.map X) = 0
    rw [integral_map hXm.aemeasurable (measurable_distOn_apply φ).aestronglyMeasurable]
    exact hX.process.centered φ
  · show cov[fun g : DistOn D => g φ, fun g : DistOn D => g ψ; P₀.map X] = _
    rw [covariance_map (measurable_distOn_apply φ).aestronglyMeasurable
      (measurable_distOn_apply ψ).aestronglyMeasurable hXm.aemeasurable]
    exact hX.process.covariance_eq φ ψ

open Classical in
/-- A chosen law of a zero-boundary GFF on `D` (the Dirac mass at `0` if there is none). -/
def zbLaw (D : TopologicalSpace.Opens ℂ) : Measure (DistOn D) :=
  if h : ∃ μ : Measure (DistOn D), IsProbabilityMeasure μ ∧ IsZeroBoundaryGFF D id μ then h.choose
  else Measure.dirac 0

instance isProbabilityMeasure_zbLaw (D : TopologicalSpace.Opens ℂ) :
    IsProbabilityMeasure (zbLaw D) := by
  rw [zbLaw]
  split_ifs with h
  · exact h.choose_spec.1
  · infer_instance

theorem isZeroBoundaryGFF_zbLaw {D : TopologicalSpace.Opens ℂ} (hD : (D : Set ℂ) ⊆ H) :
    IsZeroBoundaryGFF D id (zbLaw D) := by
  have h := exists_zbLaw hD
  simp only [zbLaw, h, ↓reduceDIte]
  exact h.choose_spec.2

end ZBLaw

/-! ### Gaussian laws on `𝒟'(V)` -/

section GaussLaw

variable {V D : TopologicalSpace.Opens ℂ}

/-- The law of `h|_V + c` for `h` a zero-boundary GFF on `D`: the Gaussian law on `𝒟'(V)` with mean `c` and
covariance `‖·‖²_{H⁻¹(D)}` (meaningful for `V ≤ D ⊆ ℍ`). -/
def gaussLaw (V D : TopologicalSpace.Opens ℂ) (c : DistOn V) : Measure (DistOn V) :=
  (zbLaw D).map fun g => restrictDist V g + c

theorem measurable_add_const_restrictDist (V : TopologicalSpace.Opens ℂ) {D : TopologicalSpace.Opens ℂ}
    (c : DistOn V) : Measurable fun g : DistOn D => restrictDist V g + c :=
  measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp (measurable_restrictDist V)).add_const (c φ)

instance isProbabilityMeasure_gaussLaw (V D : TopologicalSpace.Opens ℂ) (c : DistOn V) :
    IsProbabilityMeasure (gaussLaw V D c) := by
  rw [gaussLaw]; infer_instance

/-- **The characteristic functional of `gaussLaw`**: `∫ exp(i g(ψ)) = exp(i c(ψ) − ‖ψ‖²_{H⁻¹(D)}/2)`. -/
theorem integral_cexp_gaussLaw (hVD : V ≤ D) (hD : (D : Set ℂ) ⊆ H) (c : DistOn V) (ψ : TestOn V) :
    ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂gaussLaw V D c =
      Complex.exp (Complex.I * (c ψ : ℂ) - (zeroGFFTestCov (D : Set ℂ) ψ ψ : ℂ) / 2) := by
  have hZ := isZeroBoundaryGFF_zbLaw hD
  set φ : TestOn D := testIncl V D ψ with hφ
  have hφψ : (φ : ℂ → ℝ) = ψ := coe_testIncl hVD ψ
  have hm : Measurable fun g : DistOn D => g φ := measurable_distOn_apply φ
  rw [gaussLaw, integral_map (measurable_add_const_restrictDist V c).aemeasurable
    (measurable_exp_I_mul (measurable_distOn_apply ψ)).aestronglyMeasurable]
  have hsplit : ∀ g : DistOn D, Complex.exp (Complex.I * ((restrictDist V g + c) ψ : ℂ)) =
      Complex.exp (Complex.I * (c ψ : ℂ)) * Complex.exp (Complex.I * (g φ : ℂ)) := by
    intro g
    rw [← Complex.exp_add]
    congr 1
    show Complex.I * ((g φ + c ψ : ℝ) : ℂ) = _
    push_cast
    ring
  simp_rw [hsplit]
  rw [integral_const_mul]
  have hG : HasGaussianLaw (fun g : DistOn D => g φ) (zbLaw D) :=
    hZ.process.gaussian.hasGaussianLaw_eval φ
  have hc0 : ∫ g, (fun g : DistOn D => g φ) g ∂zbLaw D = 0 := hZ.process.centered φ
  rw [integral_exp_I_mul_of_hasGaussianLaw hG hc0]
  have hvar : Var[fun g : DistOn D => g φ; zbLaw D] = zeroGFFTestCov (D : Set ℂ) ψ ψ := by
    rw [← covariance_self hm.aemeasurable]
    have := hZ.process.covariance_eq φ φ
    simp only [id] at this
    rw [this, hφψ]
  rw [hvar, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end GaussLaw

/-! ### Finite-dimensional marginals -/

section Marginals

variable {V D : TopologicalSpace.Opens ℂ}

open LocalSets Thm11Asm Matrix in
/-- `covVec D` is linear on finite combinations of test functions on `ℍ`. -/
theorem covVec_sum_smul (hD : (D : Set ℂ) ⊆ H) {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (χ : ι → TestOn upperHalfPlaneOpens) :
    covVec (D : Set ℂ) ⇑(∑ i ∈ s, t i • χ i) = ∑ i ∈ s, t i • covVec (D : Set ℂ) (χ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using covVec_zero (D : Set ℂ) D.isOpen hD
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, covVec_add D.isOpen hD,
      covVec_smul D.isOpen hD, ih]

open LocalSets Thm11Asm Matrix in
/-- **The quadratic form of the covariance matrix**: `‖Σ tᵢ χᵢ‖²_{H⁻¹(D)} = t ⬝ Σ t` with
`Σᵢⱼ = ⟨χᵢ, χⱼ⟩_{H⁻¹(D)}`, the Gram matrix of the vectors `covVec D χᵢ`. -/
theorem zeroGFFTestCov_sum_smul (hD : (D : Set ℂ) ⊆ H) {ι : Type*} [Fintype ι] (t : ι → ℝ)
    (χ : ι → TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov (D : Set ℂ) ⇑(∑ i, t i • χ i) ⇑(∑ i, t i • χ i) =
      t ⬝ᵥ (Matrix.of fun i j => zeroGFFTestCov (D : Set ℂ) (χ i) (χ j)) *ᵥ t := by
  have hG : (Matrix.of fun i j => zeroGFFTestCov (D : Set ℂ) (χ i) (χ j)) =
      Matrix.gram ℝ fun i => covVec (D : Set ℂ) (χ i) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.gram_apply]
    exact zeroGFFTestCov_eq_inner_covVec D.isOpen hD (χ i) (χ j)
  rw [hG, zeroGFFTestCov_eq_inner_covVec D.isOpen hD, covVec_sum_smul hD,
    ← Matrix.star_dotProduct_gram_mulVec]
  rfl

open LocalSets Thm11Asm Matrix in
theorem posSemidef_zeroGFFTestCov (hD : (D : Set ℂ) ⊆ H) {ι : Type*} [Fintype ι]
    (χ : ι → TestOn upperHalfPlaneOpens) :
    (Matrix.of fun i j => zeroGFFTestCov (D : Set ℂ) (χ i) (χ j)).PosSemidef := by
  have hG : (Matrix.of fun i j => zeroGFFTestCov (D : Set ℂ) (χ i) (χ j)) =
      Matrix.gram ℝ fun i => covVec (D : Set ℂ) (χ i) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.gram_apply]
    exact zeroGFFTestCov_eq_inner_covVec D.isOpen hD (χ i) (χ j)
  rw [hG]
  exact Matrix.posSemidef_gram ℝ _

/-- The pairing of `T` with `Σ tᵢ ψᵢ` is the Euclidean inner product of `(T ψᵢ)ᵢ` with `t`. -/
theorem inner_toLp_pairings {ι : Type*} [Fintype ι] (ψ : ι → TestOn V) (T : DistOn V)
    (t : EuclideanSpace ℝ ι) :
    ⟪WithLp.toLp 2 (fun i => T (ψ i)), t⟫ = T (∑ i, t.ofLp i • ψ i) := by
  rw [PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, WithLp.ofLp_toLp, real_inner_eq_re_inner]
  simp

open Matrix in
/-- **Finite-dimensional marginals of `gaussLaw`**: the law of `(g(ψᵢ))ᵢ` is the multivariate Gaussian with mean
`(c(ψᵢ))ᵢ` and covariance matrix `(⟨ψᵢ, ψⱼ⟩_{H⁻¹(D)})ᵢⱼ`. -/
theorem map_toLp_gaussLaw (hVD : V ≤ D) (hD : (D : Set ℂ) ⊆ H) (c : DistOn V) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (ψ : ι → TestOn V) :
    (gaussLaw V D c).map (fun g => WithLp.toLp 2 (fun i => g (ψ i))) =
      multivariateGaussian (WithLp.toLp 2 fun i => c (ψ i))
        (Matrix.of fun i j => zeroGFFTestCov (D : Set ℂ) (ψ i) (ψ j)) := by
  have hVH : V ≤ upperHalfPlaneOpens := fun z hz => hD (hVD hz)
  set χ : ι → TestOn upperHalfPlaneOpens := fun i => testIncl V upperHalfPlaneOpens (ψ i) with hχ
  have hχψ : ∀ i, (χ i : ℂ → ℝ) = ψ i := fun i => coe_testIncl hVH (ψ i)
  have hS : (Matrix.of fun i j => zeroGFFTestCov (D : Set ℂ) (ψ i) (ψ j)) =
      Matrix.of fun i j => zeroGFFTestCov (D : Set ℂ) (χ i) (χ j) := by
    ext i j; simp only [Matrix.of_apply, hχψ]
  have hpsd := posSemidef_zeroGFFTestCov hD χ
  rw [← hS] at hpsd
  have hpr : Measurable fun g : DistOn V => WithLp.toLp 2 (fun i => g (ψ i)) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => measurable_distOn_apply (ψ i))
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian hpsd, charFun_apply,
    integral_map hpr.aemeasurable (by fun_prop)]
  simp_rw [inner_toLp_pairings]
  have h1 := integral_cexp_gaussLaw hVD hD c (∑ i, t.ofLp i • ψ i)
  have h2 : ∀ g : DistOn V, Complex.exp (↑(g (∑ i, t.ofLp i • ψ i)) * Complex.I) =
      Complex.exp (Complex.I * (g (∑ i, t.ofLp i • ψ i) : ℂ)) := fun g => by rw [mul_comm]
  simp_rw [h2]
  rw [h1]
  congr 1
  have hcf : (∑ i, t.ofLp i • χ i : TestOn upperHalfPlaneOpens) =
      testIncl V upperHalfPlaneOpens (∑ i, t.ofLp i • ψ i) := by
    rw [map_sum]; simp only [map_smul, hχ]
  have hq : zeroGFFTestCov (D : Set ℂ) ⇑(∑ i, t.ofLp i • ψ i) ⇑(∑ i, t.ofLp i • ψ i) =
      t.ofLp ⬝ᵥ (Matrix.of fun i j => zeroGFFTestCov (D : Set ℂ) (ψ i) (ψ j)) *ᵥ t.ofLp := by
    rw [hS, ← zeroGFFTestCov_sum_smul hD, hcf, coe_testIncl hVH]
  have hm : c (∑ i, t.ofLp i • ψ i) = ⟪t, WithLp.toLp 2 fun i => c (ψ i)⟫ := by
    rw [real_inner_comm, inner_toLp_pairings]
  rw [hq, hm]
  ring

end Marginals

/-! ### Measurable families of Gaussian laws -/

section Kernel

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The pairings with the countable generating family `distGen V`. -/
def genPairs (V : TopologicalSpace.Opens ℂ) (T : DistOn V) : ℕ × ℕ → ℝ := fun j => T (distGen V j)

theorem measurable_genPairs (V : TopologicalSpace.Opens ℂ) : Measurable (genPairs V) :=
  measurable_pi_iff.2 fun _ => measurable_distOn_apply _

/-- The preimages of measurable cylinders under `genPairs V`: a generating π-system of `𝒟'(V)`. -/
def genCylinders (V : TopologicalSpace.Opens ℂ) : Set (Set (DistOn V)) :=
  Set.preimage (genPairs V) '' measurableCylinders fun _ : ℕ × ℕ => ℝ

theorem distOn_eq_generateFrom_genCylinders (V : TopologicalSpace.Opens ℂ) :
    (inferInstance : MeasurableSpace (DistOn V)) = MeasurableSpace.generateFrom (genCylinders V) := by
  rw [genCylinders, ← MeasurableSpace.comap_generateFrom, generateFrom_measurableCylinders]
  exact distOn_measurableSpace_eq_comap V

theorem isPiSystem_genCylinders (V : TopologicalSpace.Opens ℂ) : IsPiSystem (genCylinders V) := by
  have h := isPiSystem_measurableCylinders (α := fun _ : ℕ × ℕ => ℝ) |>.comap (genPairs V)
  convert h using 1
  ext s
  simp only [genCylinders, mem_image, mem_ofPred_eq]

/-- **A measurable family of Gaussian laws.** If the mean pairings `c ω (φ_j)` and the covariances
`⟨φ_i, φ_j⟩_{H⁻¹(D ω)}` of the generating family `φ_j = distGen V j` are measurable in `ω`, then
`ω ↦ gaussLaw V (D ω) (c ω)` is measurable (a kernel). -/
theorem measurable_gaussLaw (V : TopologicalSpace.Opens ℂ) {D : Ω → TopologicalSpace.Opens ℂ}
    {c : Ω → DistOn V} (hD : ∀ ω, V ≤ D ω ∧ (D ω : Set ℂ) ⊆ H)
    (hc : ∀ j, Measurable fun ω => c ω (distGen V j))
    (hcov : ∀ i j, Measurable fun ω => zeroGFFTestCov (D ω : Set ℂ) (distGen V i) (distGen V j)) :
    Measurable fun ω => gaussLaw V (D ω) (c ω) := by
  classical
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (distOn_eq_generateFrom_genCylinders V) (isPiSystem_genCylinders V) ?_
  rintro _ ⟨C, hC, rfl⟩
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, Sx, hSx, rfl⟩ := hC
  set pr : DistOn V → EuclideanSpace ℝ s := fun T => WithLp.toLp 2 (fun i : s => T (distGen V i))
    with hprdef
  have hpr : Measurable pr := (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.2 fun i => measurable_distOn_apply _)
  have hmS : MeasurableSet {y : EuclideanSpace ℝ s | y.ofLp ∈ Sx} :=
    (WithLp.measurable_ofLp 2 _) hSx
  have hset : genPairs V ⁻¹' cylinder s Sx = pr ⁻¹' {y | y.ofLp ∈ Sx} := by
    ext T
    simp only [pr, cylinder, mem_preimage, mem_ofPred_eq]
    rfl
  have hval : ∀ ω, gaussLaw V (D ω) (c ω) (genPairs V ⁻¹' cylinder s Sx) =
      multivariateGaussian (WithLp.toLp 2 fun i : s => c ω (distGen V i))
        (Matrix.of fun i j : s => zeroGFFTestCov (D ω : Set ℂ) (distGen V i) (distGen V j))
        {y | y.ofLp ∈ Sx} := by
    intro ω
    rw [hset, ← Measure.map_apply hpr hmS, map_toLp_gaussLaw (hD ω).1 (hD ω).2]
  simp_rw [hval]
  have hm : Measurable fun ω => WithLp.toLp 2 fun i : s => c ω (distGen V i) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun i => hc i)
  have hS : Measurable fun ω =>
      (Matrix.of fun i j : s => zeroGFFTestCov (D ω : Set ℂ) (distGen V i) (distGen V j)) :=
    measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => hcov i j
  exact (Measure.measurable_coe hmS).comp (measurable_multivariateGaussian.comp (hm.prodMk hS))

/-- **A kernel of Gaussian laws from almost everywhere measurable data** (modification on a null set). -/
theorem exists_kernel_ae_eq_gaussLaw (P : Measure Ω) (V : TopologicalSpace.Opens ℂ)
    (hVH : (V : Set ℂ) ⊆ H) {D : Ω → TopologicalSpace.Opens ℂ} {c : Ω → DistOn V}
    (hD : ∀ᵐ ω ∂P, V ≤ D ω ∧ (D ω : Set ℂ) ⊆ H)
    (hc : ∀ j, AEMeasurable (fun ω => c ω (distGen V j)) P)
    (hcov : ∀ i j, AEMeasurable
      (fun ω => zeroGFFTestCov (D ω : Set ℂ) (distGen V i) (distGen V j)) P) :
    ∃ Q : ProbabilityTheory.Kernel Ω (DistOn V), IsMarkovKernel Q ∧
      ∀ᵐ ω ∂P, Q ω = gaussLaw V (D ω) (c ω) := by
  classical
  set good : Ω → Prop := fun ω => (V ≤ D ω ∧ (D ω : Set ℂ) ⊆ H) ∧
    (∀ j, c ω (distGen V j) = (hc j).mk _ ω) ∧
    ∀ i j, zeroGFFTestCov (D ω : Set ℂ) (distGen V i) (distGen V j) = (hcov i j).mk _ ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hD, ae_all_iff.2 fun j => (hc j).ae_eq_mk,
      ae_all_iff.2 fun i => ae_all_iff.2 fun j => (hcov i j).ae_eq_mk] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  set G : Set Ω := (toMeasurable P {ω | ¬ good ω})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGg : ∀ ω ∈ G, good ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simp only [hGdef, mem_compl_iff, not_not, ofPred_mem_eq, measure_toMeasurable]
    exact ae_iff.1 hae
  have hVH' : V ≤ upperHalfPlaneOpens := hVH
  set D' : Ω → TopologicalSpace.Opens ℂ := fun ω => if ω ∈ G then D ω else upperHalfPlaneOpens
  set c' : Ω → DistOn V := fun ω => if ω ∈ G then c ω else 0
  have hD' : ∀ ω, V ≤ D' ω ∧ (D' ω : Set ℂ) ⊆ H := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [D', hω, ↓reduceIte]; exact (hGg ω hω).1
    · simp only [D', hω, ↓reduceIte]; exact ⟨hVH', subset_rfl⟩
  have hc' : ∀ j, Measurable fun ω => c' ω (distGen V j) := fun j => by
    have : (fun ω => c' ω (distGen V j)) = G.piecewise ((hc j).mk _) fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [c', hω, ↓reduceIte, Set.piecewise]; exact (hGg ω hω).2.1 j
      · simp only [c', hω, ↓reduceIte, Set.piecewise]; rfl
    rw [this]
    exact (hc j).measurable_mk.piecewise hGm measurable_const
  have hcov' : ∀ i j, Measurable fun ω =>
      zeroGFFTestCov (D' ω : Set ℂ) (distGen V i) (distGen V j) := fun i j => by
    have : (fun ω => zeroGFFTestCov (D' ω : Set ℂ) (distGen V i) (distGen V j)) =
        G.piecewise ((hcov i j).mk _) fun _ =>
          zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) (distGen V i) (distGen V j) := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [D', hω, ↓reduceIte, Set.piecewise]; exact (hGg ω hω).2.2 i j
      · simp only [D', hω, ↓reduceIte, Set.piecewise]
    rw [this]
    exact (hcov i j).measurable_mk.piecewise hGm measurable_const
  refine ⟨⟨fun ω => gaussLaw V (D' ω) (c' ω), measurable_gaussLaw V hD' hc' hcov'⟩,
    ⟨fun ω => isProbabilityMeasure_gaussLaw _ _ _⟩, ?_⟩
  filter_upwards [hGae] with ω hω
  simp only [ProbabilityTheory.Kernel.coe_mk, D', c', hω, ↓reduceIte]

end Kernel

/-! ### Finite measures on `𝒟'(V)` are determined by their characteristic functionals -/

section Ext

variable {V : TopologicalSpace.Opens ℂ}

/-- Two finite measures on `𝒟'(V)` with the same characteristic functional `ψ ↦ ∫ exp(i g(ψ))` are equal
(the finite-dimensional laws on the generating cylinders agree by `Measure.ext_of_charFun`, using the linearity
of `g`). The product version with an extra coordinate is `Sobolev.measure_eq_of_setIntegral_exp`; this light copy
keeps Theorem 1.1 off the Sobolev import chain. -/
theorem ext_of_integral_cexp {μ ν : Measure (DistOn V)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ ψ : TestOn V, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂μ =
      ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂ν) : μ = ν := by
  classical
  have huniv : μ univ = ν univ := by
    have h0 := h 0
    simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, integral_const,
      Complex.real_smul, mul_one] at h0
    have h0' : μ.real univ = ν.real univ := by exact_mod_cast h0
    rw [Measure.real, Measure.real] at h0'
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h0'
  refine ext_of_generate_finite (genCylinders V) (distOn_eq_generateFrom_genCylinders V)
    (isPiSystem_genCylinders V) ?_ huniv
  rintro _ ⟨C, hC, rfl⟩
  rw [mem_measurableCylinders] at hC
  obtain ⟨s, Sx, hSx, rfl⟩ := hC
  set pr : DistOn V → EuclideanSpace ℝ s := fun T => WithLp.toLp 2 (fun i : s => T (distGen V i))
    with hprdef
  have hpr : Measurable pr := (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.2 fun i => measurable_distOn_apply _)
  have hmS : MeasurableSet {y : EuclideanSpace ℝ s | y.ofLp ∈ Sx} :=
    (WithLp.measurable_ofLp 2 _) hSx
  have hset : genPairs V ⁻¹' cylinder s Sx = pr ⁻¹' {y | y.ofLp ∈ Sx} := by
    ext T
    simp only [pr, cylinder, mem_preimage, mem_ofPred_eq]
    rfl
  have hchar : charFun (μ.map pr) = charFun (ν.map pr) := by
    funext t
    rw [charFun_apply, charFun_apply, integral_map hpr.aemeasurable (by fun_prop),
      integral_map hpr.aemeasurable (by fun_prop)]
    simp_rw [hprdef, inner_toLp_pairings, mul_comm _ Complex.I]
    exact h _
  rw [hset, ← Measure.map_apply hpr hmS, ← Measure.map_apply hpr hmS, Measure.ext_of_charFun hchar]

/-- The integral of a bounded measurable function against `(P|_A) ⊗ Q` restricted to the second coordinate. -/
theorem compProd_prod_eq_of_setIntegral_cexp {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {Q₁ Q₂ : ProbabilityTheory.Kernel Ω (DistOn V)} [IsMarkovKernel Q₁]
    [IsMarkovKernel Q₂] {A : Set Ω} (hA : MeasurableSet A)
    (h : ∀ ψ : TestOn V, ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(Q₁ ω) ∂P =
      ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(Q₂ ω) ∂P) {B : Set (DistOn V)}
    (hB : MeasurableSet B) : (P ⊗ₘ Q₁) (A ×ˢ B) = (P ⊗ₘ Q₂) (A ×ˢ B) := by
  set m : ProbabilityTheory.Kernel Ω (DistOn V) → Measure (DistOn V) :=
    fun Q => ((P ⊗ₘ Q).restrict (A ×ˢ univ)).map Prod.snd with hm
  have hval : ∀ (Q : ProbabilityTheory.Kernel Ω (DistOn V)), m Q B = (P ⊗ₘ Q) (A ×ˢ B) := by
    intro Q
    rw [hm, Measure.map_apply measurable_snd hB, Measure.restrict_apply (measurable_snd hB)]
    congr 1
    ext p
    simp [and_comm]
  have hfin : ∀ (Q : ProbabilityTheory.Kernel Ω (DistOn V)) [IsMarkovKernel Q], IsFiniteMeasure (m Q) :=
    fun Q _ => by rw [hm]; infer_instance
  have hcf : ∀ (Q : ProbabilityTheory.Kernel Ω (DistOn V)) [IsMarkovKernel Q] (ψ : TestOn V),
      ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(m Q) =
        ∫ ω in A, ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(Q ω) ∂P := by
    intro Q _ ψ
    have hmeas : Measurable fun g : DistOn V => Complex.exp (Complex.I * (g ψ : ℂ)) :=
      measurable_exp_I_mul (measurable_distOn_apply ψ)
    rw [hm, integral_map measurable_snd.aemeasurable hmeas.aestronglyMeasurable,
      Measure.setIntegral_compProd hA MeasurableSet.univ]
    · simp only [Measure.restrict_univ]
    · exact (Integrable.of_bound (hmeas.comp measurable_snd).aestronglyMeasurable 1
        (Eventually.of_forall fun p => (Complex.norm_exp_I_mul_ofReal _).le)).integrableOn
  have := hfin Q₁
  have := hfin Q₂
  have heq : m Q₁ = m Q₂ := ext_of_integral_cexp fun ψ => by rw [hcf Q₁, hcf Q₂]; exact h ψ
  rw [← hval Q₁, ← hval Q₂, heq]

end Ext

/-! ### The domain and the mean of the protected kernel -/

section Pointwise

open Ito

variable {w : ℝ≥0 → ℝ} {t : ℝ≥0} {V : TopologicalSpace.Opens ℂ}

/-- `ℍ ∖ K_t` for the driver `w` clamped at `t` (the interior is taken only to have an open set for every
driver; for a driver continuous on `[0, t]` the set is already open, `coe_hullDom`). -/
def hullDom (w : ℝ≥0 → ℝ) (t : ℝ≥0) : TopologicalSpace.Opens ℂ :=
  ⟨interior (H \ fwdHull (clampDrv (rpath w) t) t), isOpen_interior⟩

theorem coe_hullDom (hw : ContinuousOn (rpath w) (Icc 0 (t : ℝ))) :
    (hullDom w t : Set ℂ) = H \ fwdHull (clampDrv (rpath w) t) t :=
  (FwdHolo.isOpen_compl_fwdHull (continuous_clampDrv t.coe_nonneg hw) t.coe_nonneg).interior_eq

theorem hullDom_subset_H (w : ℝ≥0 → ℝ) (t : ℝ≥0) : (hullDom w t : Set ℂ) ⊆ H :=
  interior_subset.trans sdiff_subset

/-- A point of `ℍ` outside the raw hull `K_t` lies in `hullDom w t`. -/
theorem mem_hullDom (hw : ContinuousOn (rpath w) (Icc 0 (t : ℝ))) {z : ℂ} (hz : z ∈ H)
    (hzK : z ∉ fwdHull (rpath w) t) : z ∈ hullDom w t := by
  have h := exists_isForwardSol_of_mem t.coe_nonneg ⟨hz, hzK⟩
  rw [← SetLike.mem_coe, coe_hullDom hw]
  exact mem_diff_fwdHull_clampDrv t.coe_nonneg hw hz h

theorem le_hullDom (hw : ContinuousOn (rpath w) (Icc 0 (t : ℝ))) (hVH : (V : Set ℂ) ⊆ H)
    (hdis : Disjoint (V : Set ℂ) (fwdHull (rpath w) t)) : V ≤ hullDom w t := fun _ hz =>
  mem_hullDom hw (hVH hz) fun h => hdis.ne_of_mem hz h rfl

/-- **The covariance of the protected kernel is the Loewner Green energy**: for `ψ` supported in `V ⊆ ℍ ∖ K_t`,
`‖ψ‖²_{H⁻¹(ℍ∖K_t)} = E_t(ψ)` (`loewnerGreenEnergy_eq_zeroGFFTestCov` for the clamped driver). -/
theorem zeroGFFTestCov_hullDom (hw : ContinuousOn (rpath w) (Icc 0 (t : ℝ))) (hw0 : w 0 = 0)
    (hVH : (V : Set ℂ) ⊆ H) (hdis : Disjoint (V : Set ℂ) (fwdHull (rpath w) t)) (ψ : TestOn V) :
    zeroGFFTestCov (hullDom w t : Set ℂ) ψ ψ = loewnerGreenEnergy (rpath w) t ψ := by
  have hc := continuous_clampDrv t.coe_nonneg hw
  have hc0 : clampDrv (rpath w) t 0 = 0 := by simp [clampDrv, rpath, hw0]
  have hVH' : V ≤ upperHalfPlaneOpens := hVH
  set χ : TestOn upperHalfPlaneOpens := testIncl V upperHalfPlaneOpens ψ with hχ
  have hχψ : (χ : ℂ → ℝ) = ψ := coe_testIncl hVH' ψ
  have hdis' : Disjoint (tsupport χ) (fwdHull (clampDrv (rpath w) t) t) := by
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have hzV : z ∈ (V : Set ℂ) := by rw [hχψ] at hz; exact ψ.tsupport_subset hz
    have := le_hullDom hw hVH hdis hzV
    rw [← SetLike.mem_coe, coe_hullDom hw] at this
    exact this.2 hzK
  have h := loewnerGreenEnergy_eq_zeroGFFTestCov hc hc0 t.coe_nonneg χ hdis'
  have hE : loewnerGreenEnergy (clampDrv (rpath w) t) t χ = loewnerGreenEnergy (rpath w) t χ := by
    simp only [loewnerGreenEnergy, fwdMap_clampDrv_of_le le_rfl]
  rw [← hχψ, ← hE, h, coe_hullDom hw]
  rfl

/-- `logDerivFwd` at time `t` only uses the driver on `[0, t]`. -/
theorem logDerivFwd_clampDrv (w : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    logDerivFwd (clampDrv w T) T z = logDerivFwd w T z := by
  simp only [logDerivFwd]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le hT] at hs
  simp only [fwdMap_clampDrv_of_le hs.2]

theorem couplingMean_clampDrv (κ : ℝ) (w : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (u : ℂ → ℝ) :
    couplingMean κ (clampDrv w T) T u = couplingMean κ w T u := by
  funext z
  simp only [couplingMean, fwdMap_clampDrv_of_le le_rfl, logDerivFwd_clampDrv w hT]

/-- The coupling mean is continuous off the hull. -/
theorem continuousOn_couplingMean (κ : ℝ) (hw : ContinuousOn (rpath w) (Icc 0 (t : ℝ))) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) :
    ContinuousOn (couplingMean κ (rpath w) t u) (hullDom w t) := by
  have hc := continuous_clampDrv t.coe_nonneg hw
  rw [← couplingMean_clampDrv κ (rpath w) t.coe_nonneg u]
  intro z hz
  rw [SetLike.mem_coe, ← SetLike.mem_coe, coe_hullDom hw] at hz
  have hf := (FwdHolo.hasDerivAt_fwdMap hc t.coe_nonneg hz).continuousAt
  have hpos : 0 < (fwdMap (clampDrv (rpath w) t) t z).im :=
    im_fwdMap_pos hc t.coe_nonneg hz ⟨t.coe_nonneg, le_rfl⟩
  have hu' : ContinuousAt u (fwdMap (clampDrv (rpath w) t) t z) := (hu _ hpos).1.continuousAt
  have hl := Complex.continuous_im.continuousAt.comp (continuousAt_logDerivFwd hc t.coe_nonneg hz)
  exact ((hu'.comp hf).sub (continuousAt_const.mul hl)).continuousWithinAt

/-- The mean of the protected kernel: `ψ ↦ ∫ 𝔥_t ψ` on `𝒟(V)`. -/
def meanDist (κ : ℝ) (w : ℝ≥0 → ℝ) (t : ℝ≥0) (u : ℂ → ℝ) (V : TopologicalSpace.Opens ℂ) : DistOn V :=
  Distribution.ofFun V (couplingMean κ (rpath w) t u) volume ⊤

theorem meanDist_apply (κ : ℝ) (hw : ContinuousOn (rpath w) (Icc 0 (t : ℝ))) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hVH : (V : Set ℂ) ⊆ H)
    (hdis : Disjoint (V : Set ℂ) (fwdHull (rpath w) t)) (ψ : TestOn V) :
    meanDist κ w t u V ψ = ∫ z, couplingMean κ (rpath w) t u z * ψ z := by
  have hint : LocallyIntegrableOn (couplingMean κ (rpath w) t u) (V : Set ℂ) volume :=
    ((continuousOn_couplingMean κ hw hu).mono (le_hullDom hw hVH hdis)).locallyIntegrableOn
      V.isOpen.measurableSet
  rw [meanDist, Distribution.ofFun_apply hint]
  simp only [smul_eq_mul, mul_comm]

end Pointwise

/-! ### Recovering the mean and the variance from the characteristic function -/

section Extract

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- If `ω ↦ exp(iθ M − θ² E/2)` is almost everywhere strongly measurable for every `θ`, then so are `M` and `E`:
`E = −2 log |·|` at `θ = 1`, and `M = (n+1) arg(exp(iM/(n+1)))` for large `n`. -/
theorem aemeasurable_of_aestronglyMeasurable_cexp {M E : Ω → ℝ}
    (h : ∀ θ : ℝ, AEStronglyMeasurable
      (fun ω => Complex.exp (Complex.I * θ * (M ω : ℂ) - θ ^ 2 * (E ω : ℂ) / 2)) P) :
    AEMeasurable M P ∧ AEMeasurable E P := by
  have hsplit : ∀ (θ : ℝ) (ω : Ω), Complex.exp (Complex.I * θ * (M ω : ℂ) - θ ^ 2 * (E ω : ℂ) / 2) =
      Complex.exp (((-(θ ^ 2 * E ω / 2)) : ℝ) : ℂ) * Complex.exp (((θ * M ω : ℝ) : ℂ) * Complex.I) := by
    intro θ ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hE : AEMeasurable E P := by
    refine (((h 1).norm.aemeasurable.log).const_mul (-2)).congr (Eventually.of_forall fun ω => ?_)
    simp only [hsplit 1 ω, norm_mul, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.log_exp]
    ring
  refine ⟨?_, hE⟩
  set θ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hθ
  have hθpos : ∀ n, 0 < θ n := fun n => by positivity
  have hmeas : ∀ n : ℕ, AEMeasurable (fun ω => ((n : ℝ) + 1) * Complex.arg
      (Complex.exp (Complex.I * (θ n : ℝ) * (M ω : ℂ) - (θ n) ^ 2 * (E ω : ℂ) / 2) *
        Complex.exp (((θ n ^ 2 * E ω / 2 : ℝ)) : ℂ))) P := by
    intro n
    have h1 := (h (θ n)).aemeasurable
    have h2 : AEMeasurable (fun ω => Complex.exp (((θ n ^ 2 * E ω / 2 : ℝ)) : ℂ)) P :=
      Complex.measurable_exp.comp_aemeasurable
        (Complex.measurable_ofReal.comp_aemeasurable ((hE.const_mul _).div_const _))
    exact ((Complex.measurable_arg.comp_aemeasurable (h1.mul h2))).const_mul _
  refine aemeasurable_of_tendsto_metrizable_ae atTop hmeas (Eventually.of_forall fun ω => ?_)
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (|M ω| / Real.pi)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hprod : Complex.exp (Complex.I * (θ n : ℝ) * (M ω : ℂ) - (θ n) ^ 2 * (E ω : ℂ) / 2) *
      Complex.exp (((θ n ^ 2 * E ω / 2 : ℝ)) : ℂ) = Complex.exp (((θ n * M ω : ℝ) : ℂ) * Complex.I) := by
    rw [hsplit (θ n) ω, mul_comm, ← mul_assoc, ← Complex.exp_add]
    have : (((θ n ^ 2 * E ω / 2 : ℝ)) : ℂ) + ((-(θ n ^ 2 * E ω / 2) : ℝ) : ℂ) = 0 := by push_cast; ring
    rw [this, Complex.exp_zero, one_mul]
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsmall : |θ n * M ω| < Real.pi := by
    rw [abs_mul, abs_of_pos (hθpos n), hθ]
    rw [div_lt_iff₀ Real.pi_pos] at hN
    have hN' : (N : ℝ) ≤ n := by exact_mod_cast hn
    show 1 / ((n : ℝ) + 1) * |M ω| < Real.pi
    rw [one_div, inv_mul_lt_iff₀ hn1]
    nlinarith [Real.pi_pos]
  have hmem : θ n * M ω ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    refine ⟨by linarith [neg_abs_le (θ n * M ω)], by linarith [le_abs_self (θ n * M ω)]⟩
  rw [hprod, Complex.arg_exp_mul_I, toIocMod_eq_self _ |>.2 hmem, hθ]
  field_simp

end Extract

/-! ### The protected kernel of the evolution -/

section Protected

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- A test function on `V ⊆ ℍ`, as a test function on `ℍ`. -/
abbrev toTestH (V : TopologicalSpace.Opens ℂ) (ψ : TestOn V) : TestOn upperHalfPlaneOpens :=
  testIncl V upperHalfPlaneOpens ψ

theorem coe_toTestH {V : TopologicalSpace.Opens ℂ} (hVH : (V : Set ℂ) ⊆ H) (ψ : TestOn V) :
    (toTestH V ψ : ℂ → ℝ) = ψ :=
  coe_testIncl (show V ≤ upperHalfPlaneOpens from hVH) ψ

section Main

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
include hE hκ hu

/-- The tested mean and the Green energy at a protected stop are almost everywhere measurable. -/
theorem aemeasurable_mean_energy_of_stoppingTime {s : Ω → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s ω : WithTop ℝ≥0))
    (ψ : TestOn upperHalfPlaneOpens)
    (hsψ : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω))) :
    AEMeasurable (fun ω => ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (s ω) (u ω (s ω)) z * ψ z)
        P ∧
      AEMeasurable (fun ω => loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (s ω) ψ) P :=
  aemeasurable_of_aestronglyMeasurable_cexp fun θ =>
    aestronglyMeasurable_cfAt_of_stoppingTime hE hκ u hu ψ hs hsψ θ

/-- **The protected Gaussian kernel `Q_s^V`** (Astra §1, after (1.7)). For a stopping time `s` of the usual
augmentation and an open `V ⊆ ℍ` with `s < ζ` and `V ∩ K_s = ∅` almost surely, there is a Markov kernel
`Q : Ω → 𝒟'(V)` whose characteristic functional is, almost surely, `ψ ↦ exp(i (𝔥_s, ψ) − E_s(ψ)/2)` for every
test function `ψ` on `V`: the law of `(𝔥_s + h̃⁰ ∘ f_s)|_V` given the history. -/
theorem exists_protectedKernel {s : Ω → ℝ≥0}
    (hs : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (s ω : WithTop ℝ≥0))
    {V : TopologicalSpace.Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    (hsV : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (V : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω))) :
    ∃ Q : ProbabilityTheory.Kernel Ω (DistOn V), IsMarkovKernel Q ∧
      ∀ᵐ ω ∂P, ∀ ψ : TestOn V,
        ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(Q ω) = cfAt κ W u ψ 1 s ω := by
  -- the good event
  have hgood : ∀ᵐ ω ∂P, ((s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (V : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω))) ∧
      ContinuousOn (rpath (W · ω)) (Icc 0 (s ω : ℝ)) ∧ W 0 ω = 0 := by
    filter_upwards [hsV, hE.2.2.2.2] with ω h hp
    exact ⟨h, continuousOn_rpath hp.2.2.2.1 h.1, hp.1⟩
  -- test functions supported in `V` are protected
  have hsψ : ∀ ψ : TestOn V, ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport (toTestH V ψ)) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω)) := fun ψ => by
    filter_upwards [hsV] with ω h
    refine ⟨h.1, h.2.mono_left ?_⟩
    rw [coe_toTestH hVH]
    exact ψ.tsupport_subset
  set D : Ω → TopologicalSpace.Opens ℂ := fun ω => hullDom (W · ω) (s ω) with hD
  set c : Ω → DistOn V := fun ω => meanDist κ (W · ω) (s ω) (u ω (s ω)) V with hc
  -- pointwise identities on the good event
  have hDV : ∀ᵐ ω ∂P, V ≤ D ω ∧ (D ω : Set ℂ) ⊆ H := by
    filter_upwards [hgood] with ω hω
    exact ⟨le_hullDom hω.2.1 hVH hω.1.2, hullDom_subset_H _ _⟩
  have hcψ : ∀ ψ : TestOn V, ∀ᵐ ω ∂P, c ω ψ =
      ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (s ω) (u ω (s ω)) z * (toTestH V ψ) z := by
    intro ψ
    filter_upwards [hgood] with ω hω
    rw [coe_toTestH hVH]
    exact meanDist_apply κ hω.2.1 (hu ω (s ω)).1 hVH hω.1.2 ψ
  have hEψ : ∀ ψ : TestOn V, ∀ᵐ ω ∂P, zeroGFFTestCov (D ω : Set ℂ) ψ ψ =
      loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (s ω) (toTestH V ψ) := by
    intro ψ
    filter_upwards [hgood] with ω hω
    rw [coe_toTestH hVH]
    exact zeroGFFTestCov_hullDom hω.2.1 hω.2.2 hVH hω.1.2 ψ
  -- measurability of the data
  have hcm : ∀ j, AEMeasurable (fun ω => c ω (distGen V j)) P := fun j =>
    (aemeasurable_mean_energy_of_stoppingTime hE hκ u hu hs _ (hsψ (distGen V j))).1.congr
      ((hcψ (distGen V j)).mono fun _ h => h.symm)
  have hEm : ∀ ψ : TestOn V, AEMeasurable (fun ω => zeroGFFTestCov (D ω : Set ℂ) ψ ψ) P := fun ψ =>
    (aemeasurable_mean_energy_of_stoppingTime hE hκ u hu hs _ (hsψ ψ)).2.congr
      ((hEψ ψ).mono fun _ h => h.symm)
  have hpol : ∀ (ω : Ω), (D ω : Set ℂ) ⊆ H → ∀ a b : TestOn V, V ≤ D ω →
      zeroGFFTestCov (D ω : Set ℂ) a b = (zeroGFFTestCov (D ω : Set ℂ) ⇑(a + b) ⇑(a + b) -
        zeroGFFTestCov (D ω : Set ℂ) a a - zeroGFFTestCov (D ω : Set ℂ) b b) / 2 := by
    intro ω hDH a b _
    have e : ∀ φ ψ : TestOn V, zeroGFFTestCov (D ω : Set ℂ) φ ψ =
        ⟪Thm11Asm.covVec (D ω : Set ℂ) (toTestH V φ), Thm11Asm.covVec (D ω : Set ℂ) (toTestH V ψ)⟫ := by
      intro φ ψ
      rw [← LocalSets.zeroGFFTestCov_eq_inner_covVec (D ω).isOpen hDH, coe_toTestH hVH,
        coe_toTestH hVH]
    rw [e, e, e, e, show toTestH V (a + b) = toTestH V a + toTestH V b from map_add _ a b,
      LocalSets.covVec_add (D ω).isOpen hDH, real_inner_add_add_self]
    ring
  have hcov : ∀ i j, AEMeasurable
      (fun ω => zeroGFFTestCov (D ω : Set ℂ) (distGen V i) (distGen V j)) P := by
    intro i j
    refine (((hEm (distGen V i + distGen V j)).sub (hEm (distGen V i))).sub
      (hEm (distGen V j))).div_const 2 |>.congr ?_
    filter_upwards [hDV] with ω hω
    exact (hpol ω hω.2 _ _ hω.1).symm
  obtain ⟨Q, hQ, hQae⟩ := exists_kernel_ae_eq_gaussLaw P V hVH hDV hcm hcov
  refine ⟨Q, hQ, ?_⟩
  -- the characteristic functional
  have hall : ∀ᵐ ω ∂P, Q ω = gaussLaw V (D ω) (c ω) ∧ (V ≤ D ω ∧ (D ω : Set ℂ) ⊆ H) ∧
      ContinuousOn (rpath (W · ω)) (Icc 0 (s ω : ℝ)) ∧ W 0 ω = 0 ∧
      Disjoint (V : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (s ω)) := by
    filter_upwards [hQae, hDV, hgood] with ω h1 h2 h3
    exact ⟨h1, h2, h3.2.1, h3.2.2, h3.1.2⟩
  filter_upwards [hall] with ω ⟨hQω, hVD, hw, hw0, hdis⟩ ψ
  rw [hQω, integral_cexp_gaussLaw hVD.1 hVD.2, cfAt]
  have h1 : c ω ψ = ∫ z, couplingMean κ (fun r : ℝ => W r.toNNReal ω) (s ω) (u ω (s ω)) z * ψ z :=
    meanDist_apply κ hw (hu ω (s ω)).1 hVH hdis ψ
  have h2 : zeroGFFTestCov (D ω : Set ℂ) ψ ψ =
      loewnerGreenEnergy (fun r : ℝ => W r.toNNReal ω) (s ω) ψ :=
    zeroGFFTestCov_hullDom hw hw0 hVH hdis ψ
  rw [h1, h2]
  congr 1
  push_cast
  ring

/-- **(1.8) for the protected kernels** (Astra (1.8): `E[Q_T^U | 𝓕_S] = Q_S^U` for protected stops `S ≤ T`). For
stopping times `σ ≤ τ` of the usual augmentation with `V` protected through `τ`, and Markov kernels `Q_σ`, `Q_τ` with
the protected characteristic functionals at `σ` and `τ`, the joint laws `P ⊗ Q_τ` and `P ⊗ Q_σ` agree on every
rectangle `A × B` with `A ∈ 𝓖_σ`. -/
theorem compProd_prod_eq_of_protected {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0))
    (hστ : ∀ ω, σ ω ≤ τ ω) {V : TopologicalSpace.Opens ℂ} (hVH : (V : Set ℂ) ⊆ H)
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (V : Set ℂ) (fwdHull (fun r : ℝ => W r.toNNReal ω) (τ ω)))
    {Qσ Qτ : ProbabilityTheory.Kernel Ω (DistOn V)} [IsMarkovKernel Qσ] [IsMarkovKernel Qτ]
    (hQσ : ∀ᵐ ω ∂P, ∀ ψ : TestOn V,
      ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(Qσ ω) = cfAt κ W u ψ 1 σ ω)
    (hQτ : ∀ᵐ ω ∂P, ∀ ψ : TestOn V,
      ∫ g, Complex.exp (Complex.I * (g ψ : ℂ)) ∂(Qτ ω) = cfAt κ W u ψ 1 τ ω)
    {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) {B : Set (DistOn V)}
    (hB : MeasurableSet B) : (P ⊗ₘ Qτ) (A ×ˢ B) = (P ⊗ₘ Qσ) (A ×ˢ B) := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hA' : MeasurableSet A := hσ.measurableSpace_le _ hA
  refine compProd_prod_eq_of_setIntegral_cexp hA' (fun ψ => ?_) hB
  have hτs : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport (toTestH V ψ)) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω)) := by
    filter_upwards [hτV] with ω h
    refine ⟨h.1, h.2.mono_left ?_⟩
    rw [coe_toTestH hVH]
    exact ψ.tsupport_subset
  have hmart := setIntegral_cfAt_eq_of_le hE hκ u hu (toTestH V ψ) hσ hτ hστ hτs hA 1
  rw [coe_toTestH hVH] at hmart
  rw [setIntegral_congr_ae hA' (hQτ.mono fun ω h _ => h ψ),
    setIntegral_congr_ae hA' (hQσ.mono fun ω h _ => h ψ), hmart]

end Main

end Protected

end Coupling

end InteractingSLE
