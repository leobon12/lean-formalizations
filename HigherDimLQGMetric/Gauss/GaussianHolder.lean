import HigherDimLQGMetric.Gauss.GaussianHolderApprox
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# The Gaussian Hölder inequality (D-GH): the two target statements (packet G2)

Source: planning audit `planning/audits/MA4-sections-7-10-appA.md`, §1.5 item 22, Details (a) A7
and Details (c) (statement shapes, durable copy `planning/audits/statements/MA4Surface.lean.txt`,
section `GaussianHolder`); [7] = Chen–Dafnis–Paouris, arXiv:1306.2410, Theorem 1(i) with all
exponents `p_i = K` (equivalently Theorem 3(i) with `d_i = 1/K`).

* `gaussianHolder_geom` — the geometric form: for co-isometries `U_i : ℝ^N → ℝ^{n_i}`
  (`U_i U_i† = id`) with `∑_i ‖U_i x‖² ≤ K ‖x‖²` (`K ≥ 1`) and measurable `f_i : ℝ^{n_i} → [0, 1]`,
  `∫ ∏_i f_i(U_i x) dγ_N(x) ≤ ∏_i (∫ f_i^K dγ_{n_i})^{1/K}`. It is the case
  `E = ℝ^N`, `F_i = ℝ^{n_i}` of `gaussianHolder_geom_general` (proved in
  `GaussianHolderApprox` from the Ornstein–Uhlenbeck semigroup argument of
  `GaussianHolderMehler`/`GaussianHolderCore`).
* `gaussianHolder_prob` — the probabilistic form used by Lemma A.1 (packet G3): for a centred
  Gaussian process `X = (X_{i,k})` with orthonormal blocks and `Var(∑ w_{ik} X_{ik}) ≤ K ∑ w_{ik}²`,
  `E ∏_i f_i(X_i) ≤ ∏_i (E f_i(X_i)^K)^{1/K}`.

Route for the probabilistic form (replacing A7's Gram–Schmidt by Mathlib's multivariate Gaussian):
the vector `Y = (X_{i,k})_{(i,k)}` has law `Q₊ γ` for some linear `Q`
(`exists_map_stdGaussian_eq_law`, via `multivariateGaussian 0 Cov = (Cov^{1/2})₊ γ`); with the
block maps `B_i`, `U_i := B_i ∘ Q` is a co-isometry because
`⟪U_i† e, U_i† e'⟫ = E[⟪e, X_i⟫⟪e', X_i⟫] = ⟪e, e'⟫` (`inner_adjoint_eq_integral`, orthonormal
blocks), and `∑_i ‖U_i x‖² = ‖Q x‖² ≤ K ‖x‖²` because `‖Q† w‖² = Var⟪w, Y⟫ ≤ K ‖w‖²`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace HigherDimLQGMetric.Gauss

section Geometric

variable {ι : Type*} [Fintype ι] {n : ι → ℕ} {N : ℕ}

/-- **D-GH, geometric form** ([7] Theorem 3(i) with `d_i = 1/K`; blocks whitened). If every
`U_i : ℝ^N → ℝ^{n_i}` is a co-isometry (`U_i U_i^* = id`) and `∑_i U_i^* U_i ≤ K`, then
`∫ ∏_i f_i(U_i x) dγ_N ≤ ∏_i (∫ f_i^K dγ_{n_i})^{1/K}` for measurable `f_i : ℝ^{n_i} → [0,1]`. -/
theorem gaussianHolder_geom
    (U : (i : ι) → EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin (n i)))
    (hU : ∀ i, (U i).comp (ContinuousLinearMap.adjoint (U i)) = ContinuousLinearMap.id ℝ _)
    {K : ℝ} (hK : 1 ≤ K) (hUK : ∀ x, ∑ i, ‖U i x‖ ^ 2 ≤ K * ‖x‖ ^ 2)
    (f : (i : ι) → EuclideanSpace ℝ (Fin (n i)) → ℝ) (hfm : ∀ i, Measurable (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hf1 : ∀ i y, f i y ≤ 1) :
    ∫ x, ∏ i, f i (U i x) ∂(stdGaussian (EuclideanSpace ℝ (Fin N))) ≤
      ∏ i, (∫ y, f i y ^ K ∂(stdGaussian (EuclideanSpace ℝ (Fin (n i))))) ^ K⁻¹ :=
  gaussianHolder_geom_general U hU hK hUK f hfm hf0 hf1

end Geometric

variable {ι : Type*} [Fintype ι] {n : ι → ℕ}

/-- The `i`-th block `(v_{(i,k)})_k` of a vector indexed by `Σ i, Fin (n i)`. -/
def blockCLM (n : ι → ℕ) (i : ι) :
    EuclideanSpace ℝ (Σ i, Fin (n i)) →L[ℝ] EuclideanSpace ℝ (Fin (n i)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n i) => ℝ)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun k : Fin (n i) =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (Σ i, Fin (n i)) => ℝ) ⟨i, k⟩).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : (Σ i, Fin (n i)) => ℝ)).toContinuousLinearMap)

omit [Fintype ι] in
lemma blockCLM_apply (i : ι) (v : EuclideanSpace ℝ (Σ i, Fin (n i))) (k : Fin (n i)) :
    (blockCLM n i v).ofLp k = v.ofLp ⟨i, k⟩ := rfl

lemma sum_norm_blockCLM_sq (v : EuclideanSpace ℝ (Σ i, Fin (n i))) :
    ∑ i, ‖blockCLM n i v‖ ^ 2 = ‖v‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, blockCLM_apply]
  rw [Fintype.sum_sigma]

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : Type*} [Fintype T]

omit [IsProbabilityMeasure P] in
/-- The vector of a finite Gaussian process, as an element of `EuclideanSpace ℝ T`, is Gaussian. -/
lemma hasGaussianLaw_toLp {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P) :
    HasGaussianLaw (fun ω => WithLp.toLp 2 (fun p => Y p ω)) P := by
  have hYfun : HasGaussianLaw (fun ω => (fun p => Y p ω)) P :=
    (hY.hasGaussianLaw Finset.univ).map_fun
      (ContinuousLinearMap.pi fun p : T =>
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : (Finset.univ : Finset T) => ℝ)
          ⟨p, Finset.mem_univ p⟩)
  exact hYfun.toLp_pi 2

omit [IsProbabilityMeasure P] in
/-- A centred finite Gaussian vector has mean zero. -/
lemma integral_id_map_toLp {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hcent : ∀ p, ∫ ω, Y p ω ∂P = 0) :
    ∫ x, id x ∂(P.map (fun ω => WithLp.toLp 2 (fun p => Y p ω))) = 0 := by
  have hYv := hasGaussianLaw_toLp hY
  rw [integral_map hYv.aemeasurable aestronglyMeasurable_id]
  refine PiLp.ext fun p => ?_
  have h := (EuclideanSpace.proj (𝕜 := ℝ) p).integral_comp_comm hYv.integrable
  have h2 : ∀ x : EuclideanSpace ℝ T, EuclideanSpace.proj (𝕜 := ℝ) p x = x.ofLp p :=
    fun x => rfl
  simp only [h2] at h
  show (∫ ω, WithLp.toLp 2 (fun p => Y p ω) ∂P).ofLp p = (0 : EuclideanSpace ℝ T).ofLp p
  rw [← h]
  simp [hcent]

/-- **A finite centred Gaussian vector is the image of the standard Gaussian under a linear
map** (via Mathlib's `multivariateGaussian`, i.e. `Q = (Cov)^{1/2}`). -/
theorem exists_map_stdGaussian_eq_law [DecidableEq T] {Y : T → Ω → ℝ}
    (hY : IsGaussianProcess Y P) (hcent : ∀ p, ∫ ω, Y p ω ∂P = 0) :
    ∃ Q : EuclideanSpace ℝ T →L[ℝ] EuclideanSpace ℝ T,
      P.map (fun ω => WithLp.toLp 2 (fun p => Y p ω)) =
        (stdGaussian (EuclideanSpace ℝ T)).map Q := by
  set V := EuclideanSpace ℝ T
  set Yv : Ω → V := fun ω => WithLp.toLp 2 (fun p => Y p ω) with hYv_def
  have hYv : HasGaussianLaw Yv P := hasGaussianLaw_toLp hY
  have hY2 : ∀ p, MemLp (Y p) 2 P := fun p => (hY.hasGaussianLaw_eval p).memLp_two
  have : IsGaussian (P.map Yv) := hYv.isGaussian_map
  have hmean : ∫ x, id x ∂(P.map Yv) = 0 := integral_id_map_toLp hY hcent
  -- the covariance matrix
  set Cm : Matrix T T ℝ := Matrix.of fun p q => cov[Y p, Y q; P] with hCm_def
  have hcovB : ∀ x y : V, covarianceBilin (P.map Yv) x y =
      ∑ p, ∑ q, x.ofLp p * y.ofLp q * cov[Y p, Y q; P] :=
    fun x y => covarianceBilin_apply_pi hY2 x y
  have hCm : Cm.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext p q
      simp [hCm_def, covariance_comm]
    · have h := covarianceBilin_self_nonneg (μ := P.map Yv) (WithLp.toLp 2 x)
      rw [hcovB] at h
      refine h.trans_eq ?_
      simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum, hCm_def,
        Matrix.of_apply]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have hcov : covarianceBilin (P.map Yv) = covarianceBilin (multivariateGaussian 0 Cm) := by
    refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
    rw [hcovB, covarianceBilin_multivariateGaussian hCm]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, hCm_def, Matrix.of_apply]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have hlaw : P.map Yv = multivariateGaussian 0 Cm :=
    IsGaussian.ext (by rw [hmean, integral_id_multivariateGaussian']) hcov
  refine ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Cm), hlaw.trans ?_⟩
  rw [multivariateGaussian]
  congr 1
  funext x
  simp

/-- Second moments through the representation `Yv ∼ Q₊ γ`:
`⟪Q† w, Q† w'⟫ = E[⟪w, Yv⟫ ⟪w', Yv⟫]`. -/
lemma inner_adjoint_eq_integral {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hcent : ∀ p, ∫ ω, Y p ω ∂P = 0) {Q : EuclideanSpace ℝ T →L[ℝ] EuclideanSpace ℝ T}
    (hQ : P.map (fun ω => WithLp.toLp 2 (fun p => Y p ω)) =
      (stdGaussian (EuclideanSpace ℝ T)).map Q) (w w' : EuclideanSpace ℝ T) :
    ⟪ContinuousLinearMap.adjoint Q w, ContinuousLinearMap.adjoint Q w'⟫ =
      ∫ ω, ⟪w, WithLp.toLp 2 (fun p => Y p ω)⟫ * ⟪w', WithLp.toLp 2 (fun p => Y p ω)⟫ ∂P := by
  have hYv := hasGaussianLaw_toLp hY
  have : IsGaussian (P.map (fun ω => WithLp.toLp 2 (fun p => Y p ω))) := hYv.isGaussian_map
  have h1 : covarianceBilin ((stdGaussian (EuclideanSpace ℝ T)).map Q) w w' =
      ⟪ContinuousLinearMap.adjoint Q w, ContinuousLinearMap.adjoint Q w'⟫ := by
    rw [covarianceBilin_map IsGaussian.memLp_two_id Q w w', covarianceBilin_stdGaussian,
      innerSL_apply_apply]
  rw [← h1, ← hQ, covarianceBilin_apply IsGaussian.memLp_two_id, integral_id_map_toLp hY hcent]
  simp only [sub_zero]
  rw [integral_map hYv.aemeasurable (by fun_prop)]

end Prob

section Targets

/-- **D-GH, probabilistic form** (MA4 A7, "Probabilistic form"; [7] Theorem 1(i) with all
`p_i = K` and whitened blocks): for a centred Gaussian process `X = (X_{i,k})` whose blocks are
orthonormal (`E[X_{i,k} X_{i,l}] = δ_{kl}`) and which satisfies `Var(∑ w_{ik} X_{ik}) ≤ K ∑ w_{ik}²`
(i.e. `T ≤ K diag(T_ii)`), and measurable `f_i : ℝ^{n_i} → [0, 1]`,
`E ∏_i f_i(X_i) ≤ ∏_i (E f_i(X_i)^K)^{1/K}`. -/
theorem gaussianHolder_prob {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : (i : ι) → Fin (n i) → Ω → ℝ)
    (hX : IsGaussianProcess (fun p : (Σ i, Fin (n i)) => X p.1 p.2) P)
    (hcent : ∀ i k, ∫ ω, X i k ω ∂P = 0)
    (horth : ∀ i (k l : Fin (n i)), ∫ ω, X i k ω * X i l ω ∂P = if k = l then 1 else 0)
    {K : ℝ} (hK : 1 ≤ K)
    (hT : ∀ w : (i : ι) → Fin (n i) → ℝ,
      ∫ ω, (∑ i, ∑ k, w i k * X i k ω) ^ 2 ∂P ≤ K * ∑ i, ∑ k, w i k ^ 2)
    (f : (i : ι) → (Fin (n i) → ℝ) → ℝ) (hfm : ∀ i, Measurable (f i))
    (hf0 : ∀ i y, 0 ≤ f i y) (hf1 : ∀ i y, f i y ≤ 1) :
    ∫ ω, ∏ i, f i (fun k => X i k ω) ∂P ≤
      ∏ i, (∫ ω, f i (fun k => X i k ω) ^ K ∂P) ^ K⁻¹ := by
  classical
  have hK0 : 0 < K := by linarith
  set Y : (Σ i, Fin (n i)) → Ω → ℝ := fun p => X p.1 p.2 with hY_def
  set V := EuclideanSpace ℝ (Σ i, Fin (n i))
  set Yv : Ω → V := fun ω => WithLp.toLp 2 (fun p => Y p ω) with hYv_def
  have hYv : HasGaussianLaw Yv P := hasGaussianLaw_toLp hX
  have hYvm := hYv.aemeasurable
  have hcent' : ∀ p, ∫ ω, Y p ω ∂P = 0 := fun p => hcent p.1 p.2
  have hY2 : ∀ p, MemLp (Y p) 2 P := fun p => (hX.hasGaussianLaw_eval p).memLp_two
  obtain ⟨Q, hQ⟩ := exists_map_stdGaussian_eq_law hX hcent'
  have hinner := inner_adjoint_eq_integral hX hcent' hQ
  -- inner products with the field vector
  have hYvi : ∀ (w : V) (ω : Ω), ⟪w, WithLp.toLp 2 (fun p => Y p ω)⟫ =
      ∑ i, ∑ k, w.ofLp ⟨i, k⟩ * X i k ω := by
    intro w ω
    rw [PiLp.inner_apply, Fintype.sum_sigma]
    simp [hY_def, mul_comm]
  -- the block maps `U i = B_i ∘ Q`
  set U : (i : ι) → V →L[ℝ] EuclideanSpace ℝ (Fin (n i)) := fun i => (blockCLM n i).comp Q
    with hU_def
  have hU : ∀ i, (U i).comp (ContinuousLinearMap.adjoint (U i)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n i))) := by
    intro i
    refine ContinuousLinearMap.ext fun e => ext_inner_right ℝ fun e' => ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ← ContinuousLinearMap.adjoint_inner_right (U i) (ContinuousLinearMap.adjoint (U i) e) e']
    simp only [hU_def, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
    rw [hinner]
    have hadjb : ∀ (e : EuclideanSpace ℝ (Fin (n i))) (ω : Ω),
        ⟪ContinuousLinearMap.adjoint (blockCLM n i) e, WithLp.toLp 2 (fun p => Y p ω)⟫ =
          ⟪e, blockCLM n i (WithLp.toLp 2 (fun p => Y p ω))⟫ := fun e ω =>
      ContinuousLinearMap.adjoint_inner_left _ _ _
    simp only [hadjb]
    -- `⟪e, B_i Yv⟫ = ∑_k e_k X_{ik}`
    have hb : ∀ (e : EuclideanSpace ℝ (Fin (n i))) (ω : Ω),
        ⟪e, blockCLM n i (WithLp.toLp 2 (fun p => Y p ω))⟫ = ∑ k, e.ofLp k * X i k ω := by
      intro e ω
      rw [PiLp.inner_apply]
      simp [blockCLM_apply, hY_def, mul_comm]
    simp only [hb, Finset.sum_mul_sum]
    have hint : ∀ k l : Fin (n i),
        Integrable (fun ω => e.ofLp k * X i k ω * (e'.ofLp l * X i l ω)) P := fun k l => by
        have h := (hY2 ⟨i, k⟩).integrable_mul (hY2 ⟨i, l⟩)
        have h' := h.const_mul (e.ofLp k * e'.ofLp l)
        refine h'.congr (ae_of_all _ fun ω => ?_)
        simp only [Pi.mul_apply, hY_def]
        ring
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
    simp_rw [integral_finsetSum _ fun l _ => hint _ l]
    have hkl : ∀ k l : Fin (n i), ∫ ω, e.ofLp k * X i k ω * (e'.ofLp l * X i l ω) ∂P =
        e.ofLp k * e'.ofLp l * (if k = l then 1 else 0) := fun k l => by
      rw [← horth i k l, ← integral_const_mul]
      congr 1; funext ω; ring
    simp_rw [hkl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      PiLp.inner_apply]
    simp [mul_comm]
  -- the frame bound
  have hadj : ∀ w : V, ‖ContinuousLinearMap.adjoint Q w‖ ^ 2 ≤ K * ‖w‖ ^ 2 := by
    intro w
    rw [← real_inner_self_eq_norm_sq, hinner]
    have h := hT (fun i k => w.ofLp ⟨i, k⟩)
    simp only [hYvi, ← sq] at h ⊢
    refine h.trans_eq ?_
    rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_sigma]
  have hUK : ∀ x, ∑ i, ‖U i x‖ ^ 2 ≤ K * ‖x‖ ^ 2 := by
    intro x
    simp only [hU_def, ContinuousLinearMap.comp_apply, sum_norm_blockCLM_sq]
    have h := norm_sum_adjoint_sq_le (ι := Unit) (fun _ => ContinuousLinearMap.adjoint Q)
      hK0.le (fun w => by simpa using hadj w) (fun _ => x)
    simpa [ContinuousLinearMap.adjoint_adjoint] using h
  -- transfer to the standard Gaussian
  set f' : (i : ι) → EuclideanSpace ℝ (Fin (n i)) → ℝ := fun i e => f i e.ofLp with hf'_def
  have hfm' : ∀ i, Measurable (f' i) := fun i => (hfm i).comp (WithLp.measurable_ofLp 2 _)
  have hl : ∫ ω, ∏ i, f i (fun k => X i k ω) ∂P =
      ∫ x, ∏ i, f' i (U i x) ∂(stdGaussian V) := by
    have hG : Measurable (fun v : V => ∏ i, f' i (blockCLM n i v)) :=
      Finset.measurable_prod _ fun i _ => (hfm' i).comp (blockCLM n i).continuous.measurable
    have h1 : ∫ ω, ∏ i, f i (fun k => X i k ω) ∂P =
        ∫ v, ∏ i, f' i (blockCLM n i v) ∂(P.map Yv) := by
      rw [integral_map hYvm hG.aestronglyMeasurable]
      rfl
    rw [h1, hQ, integral_map Q.continuous.aemeasurable (hQ ▸ hG.aestronglyMeasurable)]
    rfl
  have hr : ∀ i, ∫ ω, f i (fun k => X i k ω) ^ K ∂P =
      ∫ y, f' i y ^ K ∂(stdGaussian (EuclideanSpace ℝ (Fin (n i)))) := by
    intro i
    have hG : Measurable (fun v : V => f' i (blockCLM n i v) ^ K) :=
      ((hfm' i).comp (blockCLM n i).continuous.measurable).pow_const K
    have h1 : ∫ ω, f i (fun k => X i k ω) ^ K ∂P =
        ∫ v, f' i (blockCLM n i v) ^ K ∂(P.map Yv) := by
      rw [integral_map hYvm hG.aestronglyMeasurable]
      rfl
    rw [h1, hQ, integral_map Q.continuous.aemeasurable (hQ ▸ hG.aestronglyMeasurable)]
    exact integral_comp_of_comp_adjoint (U i) (hU i) (g := fun y => f' i y ^ K)
      ((hfm' i).pow_const K).aestronglyMeasurable
  rw [hl, Finset.prod_congr rfl fun i _ => by rw [hr i]]
  exact gaussianHolder_geom_general U hU hK hUK f' hfm' (fun i y => hf0 i _) (fun i y => hf1 i _)

end Targets

end HigherDimLQGMetric.Gauss
