import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.ParametricIntegral
import LQGDimension.Gaussian.SteinIBP

/-!
# The Gaussian Hölder inequality (D-GH), part 1: Gaussian toolkit (packet G2)

Source: planning audit `planning/audits/MA4-sections-7-10-appA.md`, §1.5 item 22 and Details (a) A7
(the Gaussian Hölder inequality of Chen–Dafnis–Paouris, arXiv:1306.2410, Theorem 1(i) with all
exponents equal to `K`).

This file collects the facts about the standard Gaussian measure `stdGaussian E` of a
finite-dimensional real inner product space `E` used by the semigroup proof:

* `HasBddGrad H DH C`: `H` is differentiable with gradient `DH`, continuous and bounded by `C`;
* `hasDerivAt_line`, `hasFDerivAt_comp_add_smul`: derivatives along lines and affine maps;
* `integral_inner_mul_eq_integral_inner_grad`: Stein's lemma (Gaussian integration by parts) in
  gradient form, a wrapper of `LQGDimension.SteinIBP.integral_inner_mul_stdGaussian`;
* `stdGaussian_map_of_comp_adjoint`: the image of `stdGaussian E` under a co-isometry
  `U` (`U ∘ U† = id`) is `stdGaussian F`;
* `measurePreserving_rotation`: `stdGaussian E ⊗ stdGaussian E` is invariant under the rotations
  `(x, y) ↦ (cos θ • x + sin θ • y, -sin θ • x + cos θ • y)` (Mathlib's
  `IsGaussian.map_rotation_eq_self`);
* integrability of `‖x‖` and of `‖p.1‖ + ‖p.2‖` under the Gaussian measures.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric.Gauss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `H : E → ℝ` is differentiable with gradient `DH`, and `DH` is continuous and bounded by `C`. -/
structure HasBddGrad (H : E → ℝ) (DH : E → E) (C : ℝ) : Prop where
  hasFDerivAt : ∀ z, HasFDerivAt H (innerSL ℝ (DH z)) z
  continuous_grad : Continuous DH
  norm_grad_le : ∀ z, ‖DH z‖ ≤ C

namespace HasBddGrad

variable {H : E → ℝ} {DH : E → E} {C : ℝ}

lemma continuous (hH : HasBddGrad H DH C) : Continuous H :=
  continuous_iff_continuousAt.2 fun z => (hH.hasFDerivAt z).continuousAt

lemma nonneg (hH : HasBddGrad H DH C) : 0 ≤ C :=
  (norm_nonneg _).trans (hH.norm_grad_le 0)

lemma mono (hH : HasBddGrad H DH C) {C' : ℝ} (hC : C ≤ C') : HasBddGrad H DH C' where
  hasFDerivAt := hH.hasFDerivAt
  continuous_grad := hH.continuous_grad
  norm_grad_le z := (hH.norm_grad_le z).trans hC

end HasBddGrad

/-- Derivative along a line, from a gradient. -/
lemma hasDerivAt_line {G : E → ℝ} {G' : E → E} (hG : ∀ z, HasFDerivAt G (innerSL ℝ (G' z)) z)
    (x e : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => G (x + s • e)) ⟪G' (x + t • e), e⟫ t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • e) e t := by
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  have h2 := (hG (x + t • e)).comp_hasDerivAt t h1
  simpa only [Function.comp_def, innerSL_apply_apply] using h2

/-- Chain rule for `w ↦ G (b + a • w)`. -/
lemma hasFDerivAt_comp_add_smul {G : E → ℝ} {G' : E → E}
    (hG : ∀ z, HasFDerivAt G (innerSL ℝ (G' z)) z) (a : ℝ) (b v : E) :
    HasFDerivAt (fun w => G (b + a • w)) (innerSL ℝ (a • G' (b + a • v))) v := by
  have h1 : HasFDerivAt (fun w : E => b + a • w) (a • ContinuousLinearMap.id ℝ E) v :=
    ((hasFDerivAt_id v).const_smul a).const_add b
  have h2 := (hG (b + a • v)).comp v h1
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [innerSL_apply_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    FunLike.coe_smul, ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
    real_inner_smul_left, real_inner_smul_right]

/-- Chain rule for `w ↦ G (a • w + b)`. -/
lemma hasFDerivAt_comp_smul_add {G : E → ℝ} {G' : E → E}
    (hG : ∀ z, HasFDerivAt G (innerSL ℝ (G' z)) z) (a : ℝ) (b v : E) :
    HasFDerivAt (fun w => G (a • w + b)) (innerSL ℝ (a • G' (a • v + b))) v := by
  have h1 : HasFDerivAt (fun w : E => a • w + b) (a • ContinuousLinearMap.id ℝ E) v :=
    ((hasFDerivAt_id v).const_smul a).add_const b
  have h2 := (hG (a • v + b)).comp v h1
  refine h2.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [innerSL_apply_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    FunLike.coe_smul, ContinuousLinearMap.coe_id', Pi.smul_apply, id_eq,
    real_inner_smul_left, real_inner_smul_right]

/-- `HasBddGrad` is preserved by affine reparametrizations `w ↦ b + a • w`. -/
lemma HasBddGrad.comp_add_smul {G : E → ℝ} {G' : E → E} {C : ℝ} (hG : HasBddGrad G G' C)
    (a : ℝ) (b : E) :
    HasBddGrad (fun w => G (b + a • w)) (fun w => a • G' (b + a • w)) (|a| * C) where
  hasFDerivAt v := hasFDerivAt_comp_add_smul hG.hasFDerivAt a b v
  continuous_grad := continuous_const.smul (hG.continuous_grad.comp (by fun_prop))
  norm_grad_le w := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hG.norm_grad_le _) (abs_nonneg a)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Stein's lemma in gradient form**: for a standard Gaussian vector `x` of `E`, a direction
`a`, and a bounded differentiable `G` with bounded continuous gradient `G'`,
`E[⟪a, x⟫ G(x)] = E[⟪G'(x), a⟫]`. -/
theorem integral_inner_mul_eq_integral_inner_grad {G : E → ℝ} {G' : E → E} {C C' : ℝ}
    (hG : HasBddGrad G G' C') (hGb : ∀ z, |G z| ≤ C) (a : E) :
    ∫ x, ⟪a, x⟫ * G x ∂(stdGaussian E) = ∫ x, ⟪G' x, a⟫ ∂(stdGaussian E) :=
  LQGDimension.SteinIBP.integral_inner_mul_stdGaussian (hasDerivAt_line hG.hasFDerivAt)
    hG.continuous hG.continuous_grad hGb hG.norm_grad_le a

/-- `‖x‖` is integrable under the standard Gaussian measure. -/
lemma integrable_norm_stdGaussian : Integrable (fun x : E => ‖x‖) (stdGaussian E) :=
  (IsGaussian.integrable_id (μ := stdGaussian E)).norm

/-- `‖p.1‖ + ‖p.2‖` is integrable under the product of two standard Gaussian measures. -/
lemma integrable_norm_add_norm_prod :
    Integrable (fun p : E × E => ‖p.1‖ + ‖p.2‖) ((stdGaussian E).prod (stdGaussian E)) :=
  (integrable_norm_stdGaussian.comp_fst (stdGaussian E)).add
    (integrable_norm_stdGaussian.comp_snd (stdGaussian E))

/-- A bounded continuous function is integrable under a finite measure. -/
lemma integrable_of_continuous_of_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ] {g : X → ℝ}
    (hg : Continuous g) {M : ℝ} (hgM : ∀ x, |g x| ≤ M) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable M
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hgM x)

/-- The rotations of `E × E` preserve `stdGaussian E ⊗ stdGaussian E`. -/
theorem measurePreserving_rotation (θ : ℝ) :
    MeasurePreserving (ContinuousLinearMap.rotation (E := E) θ)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
  ⟨(ContinuousLinearMap.rotation (E := E) θ).continuous.measurable,
    IsGaussian.map_rotation_eq_self (integral_id_stdGaussian (E := E)) θ⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_apply_fst (θ : ℝ) (p : E × E) :
    (ContinuousLinearMap.rotation θ p).1 = cos θ • p.1 + sin θ • p.2 := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_apply_snd (θ : ℝ) (p : E × E) :
    (ContinuousLinearMap.rotation θ p).2 = -sin θ • p.1 + cos θ • p.2 := rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotation_rotation_neg (θ : ℝ) (p : E × E) :
    ContinuousLinearMap.rotation θ (ContinuousLinearMap.rotation (-θ) p) = p := by
  obtain ⟨x, y⟩ := p
  simp only [ContinuousLinearMap.rotation_apply, Real.cos_neg, Real.sin_neg, neg_neg, smul_add,
    smul_smul, Prod.mk.injEq]
  have h := Real.cos_sq_add_sin_sq θ
  constructor
  · linear_combination (norm := module) h • x
  · linear_combination (norm := module) h • y

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The adjoint of a co-isometry is an isometry. -/
lemma norm_adjoint_apply_of_comp_adjoint (U : E →L[ℝ] F)
    (hU : U.comp (ContinuousLinearMap.adjoint U) = ContinuousLinearMap.id ℝ F) (t : F) :
    ‖ContinuousLinearMap.adjoint U t‖ = ‖t‖ := by
  have h : ‖ContinuousLinearMap.adjoint U t‖ ^ 2 = ‖t‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, hU,
      ContinuousLinearMap.id_apply]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- **Image of the standard Gaussian under a co-isometry**: if `U ∘ U† = id`, then
`U₊ γ_E = γ_F`. -/
theorem stdGaussian_map_of_comp_adjoint (U : E →L[ℝ] F)
    (hU : U.comp (ContinuousLinearMap.adjoint U) = ContinuousLinearMap.id ℝ F) :
    (stdGaussian E).map U = stdGaussian F := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_apply, integral_map U.continuous.aemeasurable
    (by fun_prop)]
  have h1 : ∀ x, ⟪U x, t⟫ = ⟪x, ContinuousLinearMap.adjoint U t⟫ := fun x =>
    (ContinuousLinearMap.adjoint_inner_right U x t).symm
  simp_rw [h1]
  rw [← charFun_apply, charFun_stdGaussian, norm_adjoint_apply_of_comp_adjoint U hU]

/-- Integrals against the standard Gaussian are invariant under co-isometries. -/
lemma integral_comp_of_comp_adjoint (U : E →L[ℝ] F)
    (hU : U.comp (ContinuousLinearMap.adjoint U) = ContinuousLinearMap.id ℝ F) {g : F → ℝ}
    (hg : AEStronglyMeasurable g (stdGaussian F)) :
    ∫ x, g (U x) ∂(stdGaussian E) = ∫ y, g y ∂(stdGaussian F) := by
  rw [← stdGaussian_map_of_comp_adjoint U hU] at hg ⊢
  rw [integral_map U.continuous.aemeasurable hg]

end HigherDimLQGMetric.Gauss
