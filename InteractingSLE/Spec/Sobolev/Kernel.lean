import LQGMetric.Statement.Field
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Distributions commute with integrals of smooth test-function families

Analytic infrastructure for the specification's Aux. lemmas 11–13 (`source/spec/p049-096.md`,
`#aux-11`–`#aux-13`, pp. 83–86): the pairing of a distribution `T ∈ 𝒟'(U)` with a
parametric integral of test functions is the integral of the pairings,

  `T (x ↦ ∫ g ξ * k ξ x dξ) = ∫ g ξ * T (k ξ) dξ`,

for a jointly smooth kernel `k : ℂ → ℂ → ℝ` whose `x`-support lies in a fixed compact `K ⊆ U`,
whose `x`-derivatives grow at most polynomially in the parameter, and a weight `g` integrable
against every polynomial. This is the bridge between the Fourier definition of the negative
Sobolev norm and the pairing of a distribution with test functions ("Fourier definition of the
inhomogeneous Sobolev norm", proof of Aux. lemma 11, and the duality used in Aux. lemma 12).

Proof: on `𝓓_K` the continuous functional `T` is bounded by finitely many derivative sup-norms
(`Seminorm.bound_of_continuous`), hence factors through the Banach space of the first `N + 1`
derivatives, where it extends by Hahn–Banach; there the integral is a Bochner integral, which
commutes with the extension; and the Bochner integral of the derivatives is the derivative of the
integral (differentiation under the integral sign, by induction on the order).

## Main results

* `iteratedFDeriv_kernel_eq`, `continuous_iteratedFDeriv_kernel` : partial derivatives of a jointly
  smooth kernel and their joint continuity;
* `kernelIn` : the family `ξ ↦ k ξ` in `𝓓_K`; `continuous_kernelIn`;
* `iteratedFDeriv_integral_kernel`, `contDiff_integral_kernel` : differentiation under the integral;
* `apply_integral_kernel` : the interchange.
-/

noncomputable section

open MeasureTheory Set Filter Topology Function
open scoped Distributions ContDiff BoundedContinuousFunction

namespace InteractingSLE.Sobolev

open LQGMetric TopologicalSpace

/-! ### Partial derivatives of a jointly smooth kernel -/

section Kernel

variable {k : ℂ → ℂ → ℝ}

/-- The `x`-derivatives of a jointly smooth kernel are its joint derivatives restricted to the
`x`-direction. -/
theorem iteratedFDeriv_kernel_eq (hk : ContDiff ℝ ∞ (uncurry k)) (i : ℕ) (ξ x : ℂ) :
    iteratedFDeriv ℝ i (k ξ) x =
      (iteratedFDeriv ℝ i (uncurry k) (ξ, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr ℝ ℂ ℂ) := by
  have h1 : k ξ = (fun z : ℂ × ℂ => uncurry k ((ξ, 0) + z)) ∘ ContinuousLinearMap.inr ℝ ℂ ℂ := by
    funext y; simp
  have hc : ContDiff ℝ ∞ (fun z : ℂ × ℂ => uncurry k ((ξ, 0) + z)) :=
    hk.comp (contDiff_const.add contDiff_id)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc _ (by exact_mod_cast le_top),
    iteratedFDeriv_comp_add_left]
  simp

theorem norm_iteratedFDeriv_kernel_le (hk : ContDiff ℝ ∞ (uncurry k)) (i : ℕ) (ξ x : ℂ) :
    ‖iteratedFDeriv ℝ i (k ξ) x‖ ≤ ‖iteratedFDeriv ℝ i (uncurry k) (ξ, x)‖ := by
  rw [iteratedFDeriv_kernel_eq hk]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine le_of_le_of_eq (mul_le_mul_of_nonneg_left (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ ℂ ℂ)) (norm_nonneg _)) (mul_one _)

theorem continuous_iteratedFDeriv_kernel (hk : ContDiff ℝ ∞ (uncurry k)) (i : ℕ) :
    Continuous (fun p : ℂ × ℂ => iteratedFDeriv ℝ i (k p.1) p.2) := by
  have : (fun p : ℂ × ℂ => iteratedFDeriv ℝ i (k p.1) p.2) = fun p =>
      ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
        (fun _ : Fin i => ContinuousLinearMap.inr ℝ ℂ ℂ) (iteratedFDeriv ℝ i (uncurry k) p) := by
    funext p
    rw [iteratedFDeriv_kernel_eq hk]
    rfl
  rw [this]
  exact (ContinuousLinearMap.continuous _).comp
    (hk.continuous_iteratedFDeriv (by exact_mod_cast le_top))

theorem contDiff_kernel (hk : ContDiff ℝ ∞ (uncurry k)) (ξ : ℂ) : ContDiff ℝ ∞ (k ξ) := by
  have : k ξ = uncurry k ∘ fun x => (ξ, x) := by funext x; rfl
  rw [this]
  exact hk.comp (contDiff_const.prodMk contDiff_id)

/-- The `x`-derivatives of `k ξ` vanish outside the compact `K` containing the `x`-support. -/
theorem iteratedFDeriv_kernel_eq_zero {K : Set ℂ} (hK : IsClosed K)
    (hkK : ∀ ξ x, x ∉ K → k ξ x = 0) (i : ℕ) (ξ : ℂ) {x : ℂ} (hx : x ∉ K) :
    iteratedFDeriv ℝ i (k ξ) x = 0 := by
  by_contra h
  have h1 : x ∈ tsupport (k ξ) := support_iteratedFDeriv_subset i h
  have h2 : tsupport (k ξ) ⊆ K :=
    closure_minimal (fun y hy => by_contra fun hyK => hy (hkK ξ y hyK)) hK
  exact hx (h2 h1)

variable {K : Compacts ℂ}

/-- The sections `k ξ` of a jointly smooth kernel supported in `K`, as elements of `𝓓_K`. -/
def kernelIn (hk : ContDiff ℝ ∞ (uncurry k)) (hkK : ∀ ξ x, x ∉ K → k ξ x = 0) (ξ : ℂ) :
    𝓓_{K}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset (contDiff_kernel hk ξ)
    (fun x hx => by_contra fun h => hx (hkK ξ x h))

@[simp] theorem kernelIn_apply (hk : ContDiff ℝ ∞ (uncurry k))
    (hkK : ∀ ξ x, x ∉ K → k ξ x = 0) (ξ x : ℂ) : kernelIn hk hkK ξ x = k ξ x := rfl

/-- The family `ξ ↦ k ξ` is continuous into `𝓓_K`. -/
theorem continuous_kernelIn (hk : ContDiff ℝ ∞ (uncurry k)) (hkK : ∀ ξ x, x ∉ K → k ξ x = 0) :
    Continuous (kernelIn hk hkK) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  rw [Metric.continuous_iff]
  intro ξ₀ ε hε
  have hG := continuous_iteratedFDeriv_kernel hk i
  have hc : Continuous (fun p : ℂ × ℂ =>
      dist (iteratedFDeriv ℝ i (k p.1) p.2) (iteratedFDeriv ℝ i (k ξ₀) p.2)) :=
    hG.dist (hG.comp (continuous_const.prodMk continuous_snd))
  have hev : ∀ᶠ ξ in 𝓝 ξ₀, ∀ x ∈ (K : Set ℂ),
      dist (iteratedFDeriv ℝ i (k ξ) x) (iteratedFDeriv ℝ i (k ξ₀) x) < ε / 2 := by
    refine K.isCompact.eventually_forall_of_forall_eventually fun x _ => ?_
    refine (hc.tendsto (ξ₀, x)).eventually (gt_mem_nhds ?_)
    simp only [dist_self]
    exact half_pos hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun ξ hξ => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun x => ?_)
    (half_lt_self hε)
  simp only [comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
  change dist (iteratedFDeriv ℝ i (k ξ) x) (iteratedFDeriv ℝ i (k ξ₀) x) ≤ ε / 2
  by_cases hx : x ∈ (K : Set ℂ)
  · exact (hδε hξ x hx).le
  · rw [iteratedFDeriv_kernel_eq_zero K.isCompact.isClosed hkK i ξ hx,
      iteratedFDeriv_kernel_eq_zero K.isCompact.isClosed hkK i ξ₀ hx, dist_self]
    exact (half_pos hε).le

end Kernel

/-! ### Differentiation under the integral sign -/


section ParamIntegral

variable {k : ℂ → ℂ → ℝ} (hk : ContDiff ℝ ∞ (uncurry k))
  (hbd : ∀ i : ℕ, ∃ C, ∀ ξ x, ‖iteratedFDeriv ℝ i (k ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ i)
  {g : ℂ → ℝ} (hg : ∀ m : ℕ, Integrable (fun ξ => (1 + ‖ξ‖) ^ m * g ξ))
include hk hbd hg

omit hk hbd in
theorem integrable_norm_mul_bound (C : ℝ) (m : ℕ) :
    Integrable (fun ξ => ‖g ξ‖ * (C * (1 + ‖ξ‖) ^ m)) := by
  refine ((hg m).norm.const_mul C).congr (Eventually.of_forall fun ξ => ?_)
  have h1 : 0 ≤ (1 + ‖ξ‖) ^ m := by positivity
  simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h1]
  ring

omit hk hbd in
theorem aestronglyMeasurable_weight : AEStronglyMeasurable g :=
  ((hg 0).congr (Eventually.of_forall fun ξ => by simp)).aestronglyMeasurable

omit hk hbd hg in
theorem fderiv_iteratedFDeriv_kernel_eq (i : ℕ) (ξ x : ℂ) :
    fderiv ℝ (iteratedFDeriv ℝ i (k ξ)) x =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => ℂ) ℝ
        (iteratedFDeriv ℝ (i + 1) (k ξ) x) := by
  rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, LinearIsometryEquiv.apply_symm_apply]

theorem hasFDerivAt_integral_iteratedFDeriv (i : ℕ) (x₀ : ℂ) :
    HasFDerivAt (fun x => ∫ ξ, g ξ • iteratedFDeriv ℝ i (k ξ) x)
      (∫ ξ, g ξ • fderiv ℝ (iteratedFDeriv ℝ i (k ξ)) x₀) x₀ := by
  obtain ⟨C, hC⟩ := hbd (i + 1)
  obtain ⟨C₀, hC₀⟩ := hbd i
  have hgm := aestronglyMeasurable_weight hg
  have hcont : ∀ (j : ℕ) (x : ℂ), Continuous (fun ξ => iteratedFDeriv ℝ j (k ξ) x) :=
    fun j x => (continuous_iteratedFDeriv_kernel hk j).comp (continuous_id.prodMk continuous_const)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := univ)
    (F := fun x ξ => g ξ • iteratedFDeriv ℝ i (k ξ) x)
    (F' := fun x ξ => g ξ • fderiv ℝ (iteratedFDeriv ℝ i (k ξ)) x)
    (bound := fun ξ => ‖g ξ‖ * (C * (1 + ‖ξ‖) ^ (i + 1))) univ_mem
    (Eventually.of_forall fun x => hgm.smul (hcont i x).aestronglyMeasurable) ?_ ?_
    (Eventually.of_forall fun ξ x _ => ?_) (integrable_norm_mul_bound hg C (i + 1))
    (Eventually.of_forall fun ξ x _ => ?_)
  · refine Integrable.mono' (integrable_norm_mul_bound hg C₀ i)
      (hgm.smul (hcont i x₀).aestronglyMeasurable) (Eventually.of_forall fun ξ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hC₀ ξ x₀) (norm_nonneg _)
  · simp_rw [fderiv_iteratedFDeriv_kernel_eq i _ x₀]
    exact hgm.smul ((LinearIsometryEquiv.continuous _).comp (hcont (i + 1) x₀)).aestronglyMeasurable
  · rw [norm_smul, norm_fderiv_iteratedFDeriv]
    exact mul_le_mul_of_nonneg_left (hC ξ x) (norm_nonneg _)
  · have hd : Differentiable ℝ (iteratedFDeriv ℝ i (k ξ)) :=
      (contDiff_kernel hk ξ).differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top i)
    exact (hd x).hasFDerivAt.const_smul (g ξ)

/-- Differentiation under the integral sign, at every order. -/
theorem iteratedFDeriv_integral_kernel (i : ℕ) :
    iteratedFDeriv ℝ i (fun x => ∫ ξ, g ξ * k ξ x) =
      fun x => ∫ ξ, g ξ • iteratedFDeriv ℝ i (k ξ) x := by
  induction i with
  | zero =>
    funext x
    rw [iteratedFDeriv_zero_eq_comp, comp_apply]
    simp_rw [iteratedFDeriv_zero_eq_comp, comp_apply]
    refine (LinearIsometry.integral_comp_comm (𝕜 := ℝ)
      (continuousMultilinearCurryFin0 ℝ ℂ ℝ).symm.toLinearIsometry (fun ξ => g ξ * k ξ x)).symm.trans ?_
    congr 1
  | succ i ih =>
    funext x
    rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, ih,
      (hasFDerivAt_integral_iteratedFDeriv hk hbd hg i x).fderiv]
    refine (LinearIsometry.integral_comp_comm (𝕜 := ℝ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => ℂ) ℝ).symm.toLinearIsometry
      (fun ξ => g ξ • fderiv ℝ (iteratedFDeriv ℝ i (k ξ)) x)).symm.trans ?_
    congr 1

theorem contDiff_integral_kernel : ContDiff ℝ ∞ (fun x => ∫ ξ, g ξ * k ξ x) := by
  refine contDiff_of_differentiable_iteratedFDeriv fun m _ => ?_
  rw [iteratedFDeriv_integral_kernel hk hbd hg m]
  exact fun x => (hasFDerivAt_integral_iteratedFDeriv hk hbd hg m x).differentiableAt

end ParamIntegral

/-! ### Distributions have finite order on `𝓓_K`; extension to jets -/

section Jet

/-- The real basis `1, i` of `ℂ`. -/
def basisC : Fin 2 → ℂ := ![1, Complex.I]

theorem norm_basisC (k : Fin 2) : ‖basisC k‖ = 1 := by
  fin_cases k <;> simp [basisC]

/-- Real coordinates of `z` in the basis `1, i`. -/
def coordC (z : ℂ) : Fin 2 → ℝ := ![z.re, z.im]

theorem sum_coordC_smul_basisC (z : ℂ) : ∑ k : Fin 2, coordC z k • basisC k = z := by
  simp only [Fin.sum_univ_two, coordC, basisC, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.real_smul, mul_one]
  exact Complex.re_add_im z

theorem abs_coordC_le (z : ℂ) (k : Fin 2) : |coordC z k| ≤ ‖z‖ := by
  fin_cases k
  · exact Complex.abs_re_le_norm z
  · exact Complex.abs_im_le_norm z

/-- A real multilinear map on `ℂ^i` is bounded by the sum of its values on basis tuples. -/
theorem norm_multilinear_le_sum_basisC {i : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin i => ℂ) ℝ) :
    ‖M‖ ≤ ∑ m : Fin i → Fin 2, ‖M (fun t => basisC (m t))‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun j => ∑ k : Fin 2, coordC (v j) k • basisC k := by
    funext j; exact (sum_coordC_smul_basisC (v j)).symm
  rw [hv, M.map_sum (fun j k => coordC (v j) k • basisC k), Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  rw [M.map_smul_univ (fun j => coordC (v j) (m j)) (fun j => basisC (m j)), norm_smul,
    Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    fun j _ => ?_) (norm_nonneg _)
  beta_reduce
  rw [sum_coordC_smul_basisC]
  exact abs_coordC_le _ _

/-- Indices of the jet coordinates: an order `i ≤ N` and a basis tuple of length `i`. -/
abbrev JetIdx (N : ℕ) : Type := Σ i : Fin (N + 1), (Fin (i : ℕ) → Fin 2)

/-- The Banach space of `N`-jets in coordinates: the derivatives of order `≤ N` evaluated on basis
tuples, as bounded continuous functions. -/
abbrev JetSpace (N : ℕ) : Type := JetIdx N → (ℂ →ᵇ ℝ)

/-- One jet coordinate `f ↦ (x ↦ D^i f(x)(e_{m 1}, …, e_{m i}))`. -/
def jetComp (K : Compacts ℂ) (N : ℕ) (j : JetIdx N) : 𝓓_{K}(ℂ, ℝ) →L[ℝ] (ℂ →ᵇ ℝ) :=
  ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin (j.1 : ℕ) => ℂ) ℝ
    (fun t => basisC (j.2 t))).compLeftContinuousBounded ℂ).comp
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (j.1 : ℕ))

/-- The jet map `𝓓_K → JetSpace N`. -/
def jet (K : Compacts ℂ) (N : ℕ) : 𝓓_{K}(ℂ, ℝ) →L[ℝ] JetSpace N :=
  ContinuousLinearMap.pi (jetComp K N)

theorem jet_apply_apply (K : Compacts ℂ) (N : ℕ) (f : 𝓓_{K}(ℂ, ℝ)) (j : JetIdx N) (x : ℂ) :
    jet K N f j x = iteratedFDeriv ℝ j.1 f x (fun t => basisC (j.2 t)) := by
  simp [jet, jetComp, ContinuousMultilinearMap.apply_apply]

theorem jet_injective (K : Compacts ℂ) (N : ℕ) : Injective (jet K N) := by
  intro f g h
  refine ContDiffMapSupportedIn.ext fun x => ?_
  have := congrArg (fun J : JetSpace N => J ⟨0, Fin.elim0⟩ x) h
  rw [jet_apply_apply, jet_apply_apply] at this
  change iteratedFDeriv ℝ 0 f x (fun t => basisC (Fin.elim0 t)) =
    iteratedFDeriv ℝ 0 g x (fun t => basisC (Fin.elim0 t)) at this
  rwa [iteratedFDeriv_zero_apply, iteratedFDeriv_zero_apply] at this

/-- The `i`-th derivative sup-norm is controlled by the jet norm. -/
theorem norm_structureMap_le_jet (K : Compacts ℂ) (N : ℕ) (f : 𝓓_{K}(ℂ, ℝ)) {i : ℕ}
    (hi : i ≤ N) :
    ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i f‖ ≤ 2 ^ N * ‖jet K N f‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  refine (norm_multilinear_le_sum_basisC _).trans ?_
  have h1 : ∀ m : Fin i → Fin 2, ‖iteratedFDeriv ℝ i f x (fun t => basisC (m t))‖ ≤
      ‖jet K N f‖ := by
    intro m
    have := jet_apply_apply K N f ⟨⟨i, Nat.lt_succ_of_le hi⟩, m⟩ x
    rw [← this]
    exact (BoundedContinuousFunction.norm_coe_le_norm _ x).trans (norm_le_pi_norm _ _)
  refine (Finset.sum_le_sum fun m _ => h1 m).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) (norm_nonneg _)

variable {U : Opens ℂ}

/-- The functional `T` restricted to `𝓓_K`. -/
def restrictIn (T : DistOn U) {K : Compacts ℂ} (hKU : (K : Set ℂ) ⊆ U) :
    𝓓_{K}(ℂ, ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.comp T (TestFunction.ofSupportedInCLM ℝ hKU)

@[simp] theorem restrictIn_apply (T : DistOn U) {K : Compacts ℂ} (hKU : (K : Set ℂ) ⊆ U)
    (f : 𝓓_{K}(ℂ, ℝ)) : restrictIn T hKU f = T (TestFunction.ofSupportedIn hKU f) := rfl

/-- A distribution has finite order on each `𝓓_K`: it is bounded by finitely many derivative
sup-norms. -/
theorem exists_jet_bound (T : DistOn U) {K : Compacts ℂ} (hKU : (K : Set ℂ) ⊆ U) :
    ∃ N : ℕ, ∃ C : ℝ, ∀ f : 𝓓_{K}(ℂ, ℝ), ‖restrictIn T hKU f‖ ≤ C * ‖jet K N f‖ := by
  set TK := restrictIn T hKU
  let q : Seminorm ℝ 𝓓_{K}(ℂ, ℝ) := (normSeminorm ℝ ℝ).comp TK.toLinearMap
  have hq : Continuous q := continuous_norm.comp TK.continuous
  obtain ⟨s, C, -, hqC⟩ :=
    Seminorm.bound_of_continuous (ContDiffMapSupportedIn.withSeminorms ℝ ℂ ℝ ⊤ K) q hq
  refine ⟨s.sup id, C * 2 ^ (s.sup id), fun f => ?_⟩
  have h1 : ‖TK f‖ ≤ C * (s.sup (ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K)) f := hqC f
  have h2 : (s.sup (ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K)) f ≤
      2 ^ (s.sup id) * ‖jet K (s.sup id) f‖ := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun i hi => ?_
    rw [ContDiffMapSupportedIn.seminorm_apply]
    exact norm_structureMap_le_jet K (s.sup id) f (Finset.le_sup (f := id) hi)
  rw [mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 C.2)

/-- Hahn–Banach: on `𝓓_K`, a distribution is a continuous linear functional of the `N`-jet. -/
theorem exists_jet_extension (T : DistOn U) {K : Compacts ℂ} (hKU : (K : Set ℂ) ⊆ U) :
    ∃ N : ℕ, ∃ ℓ : JetSpace N →L[ℝ] ℝ, ∀ f : 𝓓_{K}(ℂ, ℝ), restrictIn T hKU f = ℓ (jet K N f) := by
  obtain ⟨N, C, hC⟩ := exists_jet_bound T hKU
  set TK := restrictIn T hKU
  let p : Submodule ℝ (JetSpace N) := LinearMap.range (jet K N).toLinearMap
  let e : 𝓓_{K}(ℂ, ℝ) ≃ₗ[ℝ] p := LinearEquiv.ofInjective (jet K N).toLinearMap (jet_injective K N)
  let f₀ : p →ₗ[ℝ] ℝ := TK.toLinearMap.comp e.symm.toLinearMap
  have hf₀ : ∀ y : p, ‖f₀ y‖ ≤ C * ‖y‖ := by
    intro y
    obtain ⟨φ, rfl⟩ := e.surjective y
    have h1 : f₀ (e φ) = TK φ := by simp [f₀]
    have h2 : ‖e φ‖ = ‖jet K N φ‖ := rfl
    rw [h1, h2]
    exact hC φ
  obtain ⟨ℓ, hℓ, -⟩ := exists_extension_norm_eq (𝕜 := ℝ) p (f₀.mkContinuous C hf₀)
  refine ⟨N, ℓ, fun φ => ?_⟩
  have h1 := hℓ (e φ)
  have h2 : ((e φ : p) : JetSpace N) = jet K N φ := rfl
  rw [h2] at h1
  rw [h1]
  simp [f₀]

end Jet

/-! ### The interchange -/

section Interchange

variable {U : Opens ℂ} {K : Compacts ℂ} {k : ℂ → ℂ → ℝ}

/-- **A distribution commutes with integrals of smooth test-function families.** For a jointly
smooth kernel `k` whose `x`-support lies in a compact `K ⊆ U` and whose `x`-derivatives grow at most
polynomially in the parameter, and a weight `g` integrable against every polynomial, the pairing
of `T` with `x ↦ ∫ g ξ * k ξ x` is `∫ g ξ * T (k ξ)`. -/
theorem apply_integral_kernel (T : DistOn U) (hKU : (K : Set ℂ) ⊆ U)
    (hk : ContDiff ℝ ∞ (uncurry k)) (hkK : ∀ ξ x, x ∉ K → k ξ x = 0)
    (hbd : ∀ i : ℕ, ∃ C, ∀ ξ x, ‖iteratedFDeriv ℝ i (k ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ i)
    {g : ℂ → ℝ} (hg : ∀ m : ℕ, Integrable (fun ξ => (1 + ‖ξ‖) ^ m * g ξ))
    (F : TestOn U) (hF : ∀ x, F x = ∫ ξ, g ξ * k ξ x) :
    T F = ∫ ξ, g ξ * T (TestFunction.ofSupportedIn hKU (kernelIn hk hkK ξ)) := by
  obtain ⟨N, ℓ, hℓ⟩ := exists_jet_extension T hKU
  have hFK : ∀ x, x ∉ (K : Set ℂ) → F x = 0 := fun x hx => by
    rw [hF x]; simp [hkK _ x hx]
  let FK : 𝓓_{K}(ℂ, ℝ) := ContDiffMapSupportedIn.of_support_subset F.contDiff
    (fun x hx => by_contra fun h => hx (hFK x h))
  have hFK' : TestFunction.ofSupportedIn hKU FK = F := TestFunction.ext fun x => rfl
  have hbd' := hbd
  choose C hC using hbd'
  set B : ℝ := ∑ i ∈ Finset.range (N + 1), |C i|
  have hjet_bd : ∀ ξ, ‖jet K N (kernelIn hk hkK ξ)‖ ≤ B * (1 + ‖ξ‖) ^ N := by
    intro ξ
    have h1 : (1 : ℝ) ≤ 1 + ‖ξ‖ := le_add_of_nonneg_right (norm_nonneg _)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
    have hi : (j.1 : ℕ) ≤ N := Nat.lt_succ_iff.1 j.1.2
    have hB : |C j.1| ≤ B :=
      Finset.single_le_sum (f := fun i => |C i|) (fun i _ => abs_nonneg _)
        (Finset.mem_range.2 j.1.2)
    calc ‖jet K N (kernelIn hk hkK ξ) j x‖
        = ‖iteratedFDeriv ℝ j.1 (k ξ) x (fun t => basisC (j.2 t))‖ := by
          rw [jet_apply_apply]; rfl
      _ ≤ ‖iteratedFDeriv ℝ j.1 (k ξ) x‖ * ∏ t, ‖basisC (j.2 t)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ j.1 (k ξ) x‖ := by simp [norm_basisC]
      _ ≤ C j.1 * (1 + ‖ξ‖) ^ (j.1 : ℕ) := hC j.1 ξ x
      _ ≤ |C j.1| * (1 + ‖ξ‖) ^ (j.1 : ℕ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ B * (1 + ‖ξ‖) ^ N :=
          mul_le_mul hB (pow_le_pow_right₀ h1 hi) (by positivity) (le_trans (abs_nonneg _) hB)
  have hint : Integrable (fun ξ => g ξ • jet K N (kernelIn hk hkK ξ)) := by
    refine Integrable.mono' (integrable_norm_mul_bound hg B N)
      ((aestronglyMeasurable_weight hg).smul
        ((jet K N).continuous.comp (continuous_kernelIn hk hkK)).aestronglyMeasurable)
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hjet_bd ξ) (norm_nonneg _)
  have hjet : jet K N FK = ∫ ξ, g ξ • jet K N (kernelIn hk hkK ξ) := by
    funext j
    refine BoundedContinuousFunction.ext fun x => ?_
    let L : JetSpace N →L[ℝ] ℝ :=
      (BoundedContinuousFunction.evalCLM ℝ x).comp (ContinuousLinearMap.proj (R := ℝ) j)
    have hL : L (∫ ξ, g ξ • jet K N (kernelIn hk hkK ξ)) =
        ∫ ξ, L (g ξ • jet K N (kernelIn hk hkK ξ)) := (L.integral_comp_comm hint).symm
    change jet K N FK j x = L (∫ ξ, g ξ • jet K N (kernelIn hk hkK ξ))
    rw [hL, jet_apply_apply]
    have hFfun : (FK : ℂ → ℝ) = fun x => ∫ ξ, g ξ * k ξ x := funext hF
    rw [hFfun, iteratedFDeriv_integral_kernel hk hbd hg]
    let A : ContinuousMultilinearMap ℝ (fun _ : Fin (j.1 : ℕ) => ℂ) ℝ →L[ℝ] ℝ :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin (j.1 : ℕ) => ℂ) ℝ (fun t => basisC (j.2 t))
    have hintA : Integrable (fun ξ => g ξ • iteratedFDeriv ℝ j.1 (k ξ) x) := by
      refine Integrable.mono' (integrable_norm_mul_bound hg (C j.1) j.1)
        ((aestronglyMeasurable_weight hg).smul ((continuous_iteratedFDeriv_kernel hk j.1).comp
          (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
        (Eventually.of_forall fun ξ => ?_)
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hC j.1 ξ x) (norm_nonneg _)
    change A (∫ ξ, g ξ • iteratedFDeriv ℝ j.1 (k ξ) x) = _
    rw [← A.integral_comp_comm hintA]
    congr 1
  rw [← hFK', ← restrictIn_apply, hℓ, hjet, ← ℓ.integral_comp_comm hint]
  congr 1
  funext ξ
  rw [map_smul, ← hℓ, smul_eq_mul, restrictIn_apply]

end Interchange

end InteractingSLE.Sobolev
