import SupercriticalLQGUniqueness.B2.QPos.DGFFMarkovResidual

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

def boxResidualInnerCLM (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    EuclideanSpace ℝ (DGFFSite n) →L[ℝ] EuclideanSpace ℝ I :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ I)
    (EuclideanSpace ℝ O)).comp (boxResidualFieldCLM n e)

theorem boxResidualInnerCLM_apply (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O)
    (h : EuclideanSpace ℝ (DGFFSite n)) :
    boxResidualInnerCLM n e h = (boxResidualField n e h).1 := rfl

def boxResidualInnerLaw (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) : Measure (EuclideanSpace ℝ I) :=
  (boxDGFF n).map (boxResidualInnerCLM n e)

instance boxResidualInnerLaw_isGaussian (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) : IsGaussian (boxResidualInnerLaw n e) := by
  unfold boxResidualInnerLaw
  have hG := (boxResidualField_hasGaussianLaw n e).fst
  change IsGaussian ((boxDGFF n).map (fun h => (boxResidualField n e h).1))
  exact hG.isGaussian_map

theorem boxResidualInnerLaw_mean (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    ∫ h : EuclideanSpace ℝ I, h ∂(boxResidualInnerLaw n e) = 0 := by
  have hG : IsGaussian (boxDGFF n) := by
    unfold boxDGFF WiredConductances.gaussianOfPrecision
    infer_instance
  unfold boxResidualInnerLaw
  rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
    boxDGFF_mean]
  simp

theorem boxResidualInnerLaw_covariance (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) (i j : I) :
    cov[fun h : EuclideanSpace ℝ I => h i,
      fun h : EuclideanSpace ℝ I => h j; boxResidualInnerLaw n e] =
      (boxSplitPrecision n e).toBlocks₁₁⁻¹ i j := by
  rw [boxResidualInnerLaw]
  rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
  change cov[fun h : EuclideanSpace ℝ (DGFFSite n) =>
      (boxResidualField n e h).1 i,
      fun h : EuclideanSpace ℝ (DGFFSite n) =>
      (boxResidualField n e h).1 j; boxDGFF n] = _
  exact boxResidualField_inner_covariance n e i j

 

theorem boxResidualInnerLaw_eq_gaussian (n : ℕ) {I O : Type*}
    [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (e : DGFFSite n ≃ I ⊕ O) :
    boxResidualInnerLaw n e =
      multivariateGaussian 0 (boxSplitPrecision n e).toBlocks₁₁⁻¹ := by
  have hA : (boxSplitPrecision n e).toBlocks₁₁.PosDef :=
    boxInnerPrecision_posDef n e
  apply IsGaussian.ext
  · simp [boxResidualInnerLaw_mean, integral_id_multivariateGaussian]
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun I ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply,
    ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covarianceBilin_apply_eq_cov]
  have hcoord (i : I) :
      (fun u : EuclideanSpace ℝ I ↦
        inner ℝ ((EuclideanSpace.basisFun I ℝ).toBasis i) u) =
      (fun u ↦ u i) := by
    ext u
    simp [PiLp.inner_apply]
  rw [hcoord i, hcoord j, boxResidualInnerLaw_covariance]
  rw [covariance_eval_multivariateGaussian hA.inv.posSemidef]
  all_goals exact IsGaussian.memLp_two_id

end SupercriticalLQGUniqueness.B2.QPos
