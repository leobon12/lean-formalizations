import HigherDimLQGMetric.Gauss.GaussianHolderMehler

/-!
# The Gaussian Hölder inequality (D-GH), part 3: the monotone functional (packet G2)

Source: planning audit `planning/audits/MA4-sections-7-10-appA.md`, Details (a) A7, Steps 2–3
([7] = Chen–Dafnis–Paouris, arXiv:1306.2410, §2.2, proof of Theorem 3).

Fix `c ≥ 0`, subspaces `S i ⊆ E` with `c ‖∑ ξ_i‖² ≤ ∑ ‖ξ_i‖²` whenever `ξ_i ∈ S i`, and functions
`H i : E → [δ, 1]` (`δ > 0`) with bounded continuous gradients `DH i` taking values in `S i`
(`SmoothHolderData`). With `u_i(φ, x) = mehler φ (H i) x`, the functional

  `holderFun c H φ = ∫ exp (c ∑_i log u_i(φ, x)) dγ(x) = ∫ ∏_i u_i(φ, x)^c dγ(x)`

(A7's `a(t)`, angle parametrization `e^{-t} = cos φ`) has derivative

  `-sin φ ∫ ∑_i ⟪mehlerGrad φ (DH i), DΨ_i⟫ dγ = sin φ cos φ · c ∫ e^{L} (∑ ‖ξ_i‖² - c ‖∑ ξ_i‖²) dγ`

with `ξ_i = u_i⁻¹ • mehlerGrad φ (DH i)` (`hasDerivAt_holderFun`, `holderFunDeriv_eq`,
`sum_inner_holderDPsi`), which is `≥ 0` on `[0, π/2]`. Comparing the endpoints `φ = 0` and
`φ = π/2` gives the smooth case of D-GH (`integral_prod_rpow_le_of_smooth`):

  `∫ ∏_i H_i^c dγ ≤ ∏_i (∫ H_i dγ)^c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric.Gauss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*}

/-- Standing hypotheses of the smooth case: `δ ≤ H i ≤ 1` with `δ > 0`, and `H i` has a gradient
`DH i`, continuous, bounded by `C`, with values in the subspace `S i`. -/
structure SmoothHolderData (H : ι → E → ℝ) (DH : ι → E → E) (S : ι → Submodule ℝ E)
    (δ C : ℝ) : Prop where
  pos : 0 < δ
  grad : ∀ i, HasBddGrad (H i) (DH i) C
  le : ∀ i z, δ ≤ H i z
  le_one : ∀ i z, H i z ≤ 1
  mem : ∀ i z, DH i z ∈ S i

/-- `ξ_i = u_i⁻¹ • mehlerGrad φ (DH i)`: the gradient of `log u_i` divided by `cos φ`. -/
def holderXi (H : ι → E → ℝ) (DH : ι → E → E) (i : ι) (φ : ℝ) (x : E) : E :=
  (mehler φ (H i) x)⁻¹ • mehlerGrad φ (DH i) x

namespace SmoothHolderData

variable {H : ι → E → ℝ} {DH : ι → E → E} {S : ι → Submodule ℝ E} {δ C : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma abs_le_one (D : SmoothHolderData H DH S δ C) (i : ι) (z : E) : |H i z| ≤ 1 :=
  abs_le.2 ⟨by linarith [D.le i z, D.pos], D.le_one i z⟩

lemma mehler_ge (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    δ ≤ mehler φ (H i) x :=
  le_mehler (D.grad i).continuous (D.abs_le_one i) (D.le i) φ x

lemma mehler_pos (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    0 < mehler φ (H i) x :=
  D.pos.trans_le (D.mehler_ge i φ x)

lemma mehler_le_one (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    mehler φ (H i) x ≤ 1 :=
  mehler_le (D.grad i).continuous (D.abs_le_one i) (D.le_one i) φ x

lemma continuous_mehler' (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) :
    Continuous (mehler φ (H i)) :=
  continuous_mehler (D.grad i) (D.abs_le_one i) φ

lemma norm_holderXi_le (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    ‖holderXi H DH i φ x‖ ≤ C / δ := by
  rw [holderXi, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (D.mehler_pos i φ x),
    div_eq_inv_mul]
  exact mul_le_mul (inv_anti₀ D.pos (D.mehler_ge i φ x))
    (norm_mehlerGrad_le (D.grad i).norm_grad_le φ x) (norm_nonneg _) (inv_nonneg.2 D.pos.le)

lemma continuous_holderXi (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) :
    Continuous (holderXi H DH i φ) :=
  ((D.continuous_mehler' i φ).inv₀ fun x => (D.mehler_pos i φ x).ne').smul
    (continuous_mehlerGrad (D.grad i).continuous_grad (D.grad i).norm_grad_le φ)

lemma holderXi_mem (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    holderXi H DH i φ x ∈ S i :=
  (S i).smul_mem _ (mehlerGrad_mem (D.grad i).continuous_grad (D.grad i).norm_grad_le
    (D.mem i) φ x)

lemma mehlerGrad_eq_smul (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    mehlerGrad φ (DH i) x = mehler φ (H i) x • holderXi H DH i φ x := by
  rw [holderXi, smul_smul, mul_inv_cancel₀ (D.mehler_pos i φ x).ne', one_smul]

/-- The gradient of `log u_i`. -/
lemma hasFDerivAt_log_mehler (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    HasFDerivAt (fun x => Real.log (mehler φ (H i) x))
      (innerSL ℝ (cos φ • holderXi H DH i φ x)) x := by
  have h := (hasFDerivAt_mehler (D.grad i) (D.abs_le_one i) φ x).log
    (D.mehler_pos i φ x).ne'
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [smul_apply, innerSL_apply_apply, holderXi, smul_eq_mul, real_inner_smul_left]
  ring

end SmoothHolderData

section Fintype

variable [Fintype ι]

/-- The logarithm of the integrand: `holderLog c H φ x = c ∑_i log (mehler φ (H i) x)`. -/
def holderLog (c : ℝ) (H : ι → E → ℝ) (φ : ℝ) (x : E) : ℝ :=
  c * ∑ i, Real.log (mehler φ (H i) x)

/-- The monotone functional `∫ exp (c ∑_i log mehler φ (H i) x) dγ(x)`. -/
def holderFun (c : ℝ) (H : ι → E → ℝ) (φ : ℝ) : ℝ :=
  ∫ x, Real.exp (holderLog c H φ x) ∂(stdGaussian E)

/-- The weights `Ψ_i = c · exp (L - log u_i) = c e^L / u_i`. -/
def holderPsi (c : ℝ) (H : ι → E → ℝ) (i : ι) (φ : ℝ) (x : E) : ℝ :=
  c * Real.exp (holderLog c H φ x - Real.log (mehler φ (H i) x))

/-- The gradient of `holderPsi`. -/
def holderDPsi (c : ℝ) (H : ι → E → ℝ) (DH : ι → E → E) (i : ι) (φ : ℝ) (x : E) : E :=
  holderPsi c H i φ x • (cos φ • (c • ∑ j, holderXi H DH j φ x - holderXi H DH i φ x))

/-- `exp (c ∑ log aᵢ) = ∏ aᵢ ^ c` for positive `aᵢ`. -/
lemma exp_mul_sum_log {c : ℝ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    Real.exp (c * ∑ i, Real.log (a i)) = ∏ i, a i ^ c := by
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.rpow_def_of_pos (ha i), mul_comm]

namespace SmoothHolderData

variable {H : ι → E → ℝ} {DH : ι → E → E} {S : ι → Submodule ℝ E} {δ C c : ℝ}

lemma holderLog_nonpos (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (φ : ℝ) (x : E) :
    holderLog c H φ x ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos hc (Finset.sum_nonpos fun i _ =>
    Real.log_nonpos (D.mehler_pos i φ x).le (D.mehler_le_one i φ x))

lemma exp_holderLog_le_one (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (φ : ℝ) (x : E) :
    Real.exp (holderLog c H φ x) ≤ 1 :=
  Real.exp_le_one_iff.2 (D.holderLog_nonpos hc φ x)

lemma continuous_holderLog (D : SmoothHolderData H DH S δ C) (φ : ℝ) :
    Continuous (holderLog c H φ) :=
  continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (D.continuous_mehler' i φ).log fun x => (D.mehler_pos i φ x).ne')

/-- The gradient of `holderLog`. -/
lemma hasFDerivAt_holderLog (D : SmoothHolderData H DH S δ C) (φ : ℝ) (x : E) :
    HasFDerivAt (holderLog c H φ) (innerSL ℝ (cos φ • c • ∑ i, holderXi H DH i φ x)) x := by
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    D.hasFDerivAt_log_mehler i φ x).const_mul c
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [smul_apply, sum_apply, innerSL_apply_apply, smul_eq_mul, real_inner_smul_left,
    sum_inner]
  rw [← Finset.mul_sum]
  ring

/-- The angle derivative of `holderLog`. -/
lemma hasDerivAt_holderLog_angle (D : SmoothHolderData H DH S δ C) (x : E) (φ : ℝ) :
    HasDerivAt (fun φ => holderLog c H φ x)
      (c * ∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x) φ :=
  (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (hasDerivAt_mehler_angle (D.grad i) (D.abs_le_one i) x φ).log
      (D.mehler_pos i φ x).ne').const_mul c

lemma holderPsi_mul_mehler (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    holderPsi c H i φ x * mehler φ (H i) x = c * Real.exp (holderLog c H φ x) := by
  rw [holderPsi, Real.exp_sub, Real.exp_log (D.mehler_pos i φ x)]
  field_simp [(D.mehler_pos i φ x).ne']

omit [BorelSpace E] in
lemma holderPsi_nonneg (hc : 0 ≤ c) (i : ι) (φ : ℝ) (x : E) : 0 ≤ holderPsi c H i φ x :=
  mul_nonneg hc (Real.exp_pos _).le

lemma holderPsi_le (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (i : ι) (φ : ℝ) (x : E) :
    holderPsi c H i φ x ≤ c / δ := by
  have h1 := D.holderPsi_mul_mehler (c := c) i φ x
  have h2 := D.exp_holderLog_le_one hc φ x
  have hu := D.mehler_pos i φ x
  have hδu := D.mehler_ge i φ x
  have hΨ := holderPsi_nonneg (H := H) hc i φ x
  rw [le_div_iff₀ D.pos]
  calc holderPsi c H i φ x * δ ≤ holderPsi c H i φ x * mehler φ (H i) x :=
        mul_le_mul_of_nonneg_left hδu hΨ
    _ = c * Real.exp (holderLog c H φ x) := h1
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left h2 hc
    _ = c := mul_one c

lemma abs_holderPsi_le (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (i : ι) (φ : ℝ)
    (x : E) : |holderPsi c H i φ x| ≤ c / δ := by
  rw [abs_of_nonneg (holderPsi_nonneg hc i φ x)]
  exact D.holderPsi_le hc i φ x

lemma continuous_holderPsi (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) :
    Continuous (holderPsi c H i φ) :=
  continuous_const.mul (((D.continuous_holderLog φ).sub
    ((D.continuous_mehler' i φ).log fun x => (D.mehler_pos i φ x).ne')).rexp)

/-- The gradient of `holderPsi`. -/
lemma hasFDerivAt_holderPsi (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) (x : E) :
    HasFDerivAt (holderPsi c H i φ) (innerSL ℝ (holderDPsi c H DH i φ x)) x := by
  have h := (((D.hasFDerivAt_holderLog (c := c) φ x).sub
    (D.hasFDerivAt_log_mehler i φ x)).exp).const_mul c
  refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  simp only [smul_apply, sub_apply, innerSL_apply_apply, smul_eq_mul, Pi.sub_apply,
    holderDPsi, holderPsi, real_inner_smul_left, inner_sub_left, holderLog]
  ring

lemma norm_holderDPsi_le (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (i : ι) (φ : ℝ)
    (x : E) :
    ‖holderDPsi c H DH i φ x‖ ≤ c / δ * (c * (Fintype.card ι * (C / δ)) + C / δ) := by
  have hCδ : 0 ≤ C / δ := (norm_nonneg _).trans (D.norm_holderXi_le i φ x)
  rw [holderDPsi, norm_smul, Real.norm_eq_abs, abs_of_nonneg (holderPsi_nonneg hc i φ x)]
  refine mul_le_mul (D.holderPsi_le hc i φ x) ?_ (norm_nonneg _) (div_nonneg hc D.pos.le)
  rw [norm_smul, Real.norm_eq_abs]
  refine (mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one φ)).trans ?_
  refine (norm_sub_le _ _).trans (add_le_add ?_ (D.norm_holderXi_le i φ x))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) hc
  calc ∑ j, ‖holderXi H DH j φ x‖ ≤ ∑ _j : ι, C / δ :=
        Finset.sum_le_sum fun j _ => D.norm_holderXi_le j φ x
    _ = Fintype.card ι * (C / δ) := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

lemma continuous_holderDPsi (D : SmoothHolderData H DH S δ C) (i : ι) (φ : ℝ) :
    Continuous (holderDPsi c H DH i φ) :=
  (D.continuous_holderPsi i φ).smul (continuous_const.smul ((continuous_const.smul
    (continuous_finsetSum _ fun j _ => D.continuous_holderXi j φ)).sub
      (D.continuous_holderXi i φ)))

lemma hasBddGrad_holderPsi (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (i : ι) (φ : ℝ) :
    HasBddGrad (holderPsi c H i φ) (holderDPsi c H DH i φ)
      (c / δ * (c * (Fintype.card ι * (C / δ)) + C / δ)) where
  hasFDerivAt x := D.hasFDerivAt_holderPsi i φ x
  continuous_grad := D.continuous_holderDPsi i φ
  norm_grad_le x := D.norm_holderDPsi_le hc i φ x

/-- The pointwise identity behind the sign of the derivative. -/
lemma sum_inner_holderDPsi (D : SmoothHolderData H DH S δ C) (φ : ℝ) (x : E) :
    ∑ i, ⟪mehlerGrad φ (DH i) x, holderDPsi c H DH i φ x⟫ =
      c * Real.exp (holderLog c H φ x) * cos φ *
        (c * ‖∑ i, holderXi H DH i φ x‖ ^ 2 - ∑ i, ‖holderXi H DH i φ x‖ ^ 2) := by
  set ξ := fun i => holderXi H DH i φ x with hξ
  have hterm : ∀ i, ⟪mehlerGrad φ (DH i) x, holderDPsi c H DH i φ x⟫ =
      c * Real.exp (holderLog c H φ x) * cos φ * (c * ⟪ξ i, ∑ j, ξ j⟫ - ‖ξ i‖ ^ 2) := by
    intro i
    rw [D.mehlerGrad_eq_smul i φ x, holderDPsi, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      ← D.holderPsi_mul_mehler (c := c) i φ x]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← sum_inner, real_inner_self_eq_norm_sq]

lemma integrable_mul_mehlerDeriv (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (i : ι)
    (φ : ℝ) :
    Integrable (fun x => holderPsi c H i φ x * mehlerDeriv φ (DH i) x) (stdGaussian E) := by
  have hb : Integrable (fun x : E => c / δ * C * (‖x‖ + ∫ y, ‖y‖ ∂(stdGaussian E)))
      (stdGaussian E) :=
    (integrable_norm_stdGaussian.add (integrable_const _)).const_mul _
  refine hb.mono' ((D.continuous_holderPsi i φ).mul (continuous_mehlerDeriv
      (D.grad i).continuous_grad (D.grad i).norm_grad_le φ)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul (D.abs_holderPsi_le hc i φ x) (abs_mehlerDeriv_le (D.grad i).norm_grad_le φ x)
    (abs_nonneg _) (div_nonneg hc D.pos.le)

lemma integrable_inner_holderDPsi (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (i : ι)
    (φ : ℝ) :
    Integrable (fun x => ⟪mehlerGrad φ (DH i) x, holderDPsi c H DH i φ x⟫) (stdGaussian E) :=
  integrable_of_continuous_of_bound
    ((continuous_mehlerGrad (D.grad i).continuous_grad (D.grad i).norm_grad_le φ).inner
      (D.continuous_holderDPsi i φ))
    (M := C * (c / δ * (c * (Fintype.card ι * (C / δ)) + C / δ))) fun x =>
      (abs_real_inner_le_norm _ _).trans (mul_le_mul
        (norm_mehlerGrad_le (D.grad i).norm_grad_le φ x) (D.norm_holderDPsi_le hc i φ x)
        (norm_nonneg _) ((D.grad i).nonneg))

/-- The derivative of the monotone functional, in integration-by-parts form. -/
lemma holderFunDeriv_eq (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (φ : ℝ) :
    ∫ x, Real.exp (holderLog c H φ x) *
        (c * ∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x) ∂(stdGaussian E) =
      -sin φ * ∫ x, ∑ i, ⟪mehlerGrad φ (DH i) x, holderDPsi c H DH i φ x⟫ ∂(stdGaussian E) := by
  have hpt : ∀ x, Real.exp (holderLog c H φ x) *
      (c * ∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x) =
        ∑ i, holderPsi c H i φ x * mehlerDeriv φ (DH i) x := by
    intro x
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h := D.holderPsi_mul_mehler (c := c) i φ x
    have hu := (D.mehler_pos i φ x).ne'
    have hΨ : holderPsi c H i φ x = c * Real.exp (holderLog c H φ x) / mehler φ (H i) x := by
      rw [eq_div_iff hu]; exact h
    rw [hΨ]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => D.integrable_mul_mehlerDeriv hc i φ,
    integral_finsetSum _ fun i _ => D.integrable_inner_holderDPsi hc i φ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_mul_mehlerDeriv (D.grad i).continuous_grad (D.grad i).norm_grad_le
    (D.hasBddGrad_holderPsi hc i φ) (D.abs_holderPsi_le hc i φ) φ


lemma continuous_holderFunDerivIntegrand (D : SmoothHolderData H DH S δ C) (φ : ℝ) :
    Continuous (fun x => Real.exp (holderLog c H φ x) *
      (c * ∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x)) :=
  (D.continuous_holderLog φ).rexp.mul (continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (continuous_mehlerDeriv (D.grad i).continuous_grad (D.grad i).norm_grad_le φ).div
      (D.continuous_mehler' i φ) fun x => (D.mehler_pos i φ x).ne'))

/-- **The derivative of the monotone functional** (differentiation under the integral sign). -/
theorem hasDerivAt_holderFun (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c) (φ₀ : ℝ) :
    HasDerivAt (holderFun c H)
      (∫ x, Real.exp (holderLog c H φ₀ x) *
        (c * ∑ i, mehlerDeriv φ₀ (DH i) x / mehler φ₀ (H i) x) ∂(stdGaussian E)) φ₀ := by
  set M₁ := ∫ y, ‖y‖ ∂(stdGaussian E) with hM₁
  have hb : Integrable (fun x : E => c * (Fintype.card ι * (C * (‖x‖ + M₁) / δ)))
      (stdGaussian E) :=
    ((((integrable_norm_stdGaussian (E := E)).add (integrable_const M₁)).const_mul C).div_const
      δ |>.const_mul (Fintype.card ι : ℝ)).const_mul c
  have hbound : ∀ (φ : ℝ) (x : E), ‖Real.exp (holderLog c H φ x) *
      (c * ∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x)‖ ≤
        c * (Fintype.card ι * (C * (‖x‖ + M₁) / δ)) := by
    intro φ x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_nonneg hc]
    have hsum : |∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x| ≤
        Fintype.card ι * (C * (‖x‖ + M₁) / δ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |mehlerDeriv φ (DH i) x / mehler φ (H i) x|
          ≤ ∑ _i : ι, C * (‖x‖ + M₁) / δ := Finset.sum_le_sum fun i _ => by
            rw [abs_div, abs_of_pos (D.mehler_pos i φ x)]
            have h1 := abs_mehlerDeriv_le (D.grad i).norm_grad_le φ x
            exact div_le_div₀ ((abs_nonneg _).trans h1) h1 D.pos (D.mehler_ge i φ x)
        _ = Fintype.card ι * (C * (‖x‖ + M₁) / δ) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hnn : 0 ≤ c * (Fintype.card ι * (C * (‖x‖ + M₁) / δ)) :=
      mul_nonneg hc ((abs_nonneg _).trans hsum)
    calc Real.exp (holderLog c H φ x) * (c * |∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x|)
        ≤ 1 * (c * (Fintype.card ι * (C * (‖x‖ + M₁) / δ))) :=
          mul_le_mul (D.exp_holderLog_le_one hc φ x) (mul_le_mul_of_nonneg_left hsum hc)
            (mul_nonneg hc (abs_nonneg _)) zero_le_one
      _ = c * (Fintype.card ι * (C * (‖x‖ + M₁) / δ)) := one_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGaussian E)
    (F := fun φ x => Real.exp (holderLog c H φ x))
    (F' := fun φ x => Real.exp (holderLog c H φ x) *
      (c * ∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x))
    (x₀ := φ₀) (bound := fun x => c * (Fintype.card ι * (C * (‖x‖ + M₁) / δ))) (s := univ)
    univ_mem
    (Eventually.of_forall fun φ => (D.continuous_holderLog φ).rexp.aestronglyMeasurable)
    (integrable_of_continuous_of_bound (D.continuous_holderLog φ₀).rexp (M := 1) fun x => by
      rw [abs_of_pos (Real.exp_pos _)]; exact D.exp_holderLog_le_one hc φ₀ x)
    (D.continuous_holderFunDerivIntegrand φ₀).aestronglyMeasurable
    (ae_of_all _ fun x φ _ => hbound φ x) hb
    (ae_of_all _ fun x φ _ => (D.hasDerivAt_holderLog_angle x φ).exp)
  exact key.2

/-- **The derivative is nonnegative on `[0, π/2]`** (MA4 A7, Step 3: `a′ ≥ 0`). -/
theorem holderFunDeriv_nonneg (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c)
    (hS : ∀ ξ : ι → E, (∀ i, ξ i ∈ S i) → c * ‖∑ i, ξ i‖ ^ 2 ≤ ∑ i, ‖ξ i‖ ^ 2) {φ : ℝ}
    (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ π / 2) :
    0 ≤ ∫ x, Real.exp (holderLog c H φ x) *
      (c * ∑ i, mehlerDeriv φ (DH i) x / mehler φ (H i) x) ∂(stdGaussian E) := by
  rw [D.holderFunDeriv_eq hc φ]
  refine mul_nonneg_of_nonpos_of_nonpos
    (neg_nonpos.2 (sin_nonneg_of_nonneg_of_le_pi hφ0 (by linarith [pi_pos]))) ?_
  refine integral_nonpos fun x => ?_
  show ∑ i, ⟪mehlerGrad φ (DH i) x, holderDPsi c H DH i φ x⟫ ≤ 0
  rw [D.sum_inner_holderDPsi φ x]
  have hcos : 0 ≤ cos φ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hφ1⟩
  have hb := hS (fun i => holderXi H DH i φ x) (fun i => D.holderXi_mem i φ x)
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (mul_nonneg hc (Real.exp_pos _).le) hcos)
    (by linarith)

/-- **Monotonicity**: `holderFun c H 0 ≤ holderFun c H (π / 2)`. -/
theorem holderFun_zero_le (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c)
    (hS : ∀ ξ : ι → E, (∀ i, ξ i ∈ S i) → c * ‖∑ i, ξ i‖ ^ 2 ≤ ∑ i, ‖ξ i‖ ^ 2) :
    holderFun c H 0 ≤ holderFun c H (π / 2) := by
  have hderiv := fun φ => D.hasDerivAt_holderFun hc φ
  have hmono : MonotoneOn (holderFun c H) (Icc 0 (π / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2)) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.2 fun φ => (hderiv φ).continuousAt).continuousOn
    · exact fun φ _ => (hderiv φ).differentiableAt.differentiableWithinAt
    · intro φ hφ
      rw [interior_Icc] at hφ
      rw [(hderiv φ).deriv]
      exact D.holderFunDeriv_nonneg hc hS hφ.1.le hφ.2.le
  have hπ : (0 : ℝ) ≤ π / 2 := by positivity
  exact hmono (left_mem_Icc.2 hπ) (right_mem_Icc.2 hπ) hπ

omit [BorelSpace E] in
lemma holderFun_zero (D : SmoothHolderData H DH S δ C) :
    holderFun c H 0 = ∫ x, ∏ i, H i x ^ c ∂(stdGaussian E) := by
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [holderLog, mehler_zero]
  exact exp_mul_sum_log fun i => D.pos.trans_le (D.le i x)

omit [Fintype ι] in
lemma integral_ge (D : SmoothHolderData H DH S δ C) (i : ι) :
    δ ≤ ∫ x, H i x ∂(stdGaussian E) := by
  have h := D.mehler_ge i (π / 2) 0
  rwa [mehler_pi_div_two] at h

lemma holderFun_pi_div_two (D : SmoothHolderData H DH S δ C) :
    holderFun c H (π / 2) = ∏ i, (∫ x, H i x ∂(stdGaussian E)) ^ c := by
  simp only [holderFun, holderLog, mehler_pi_div_two, integral_const, probReal_univ, one_smul]
  exact exp_mul_sum_log fun i => D.pos.trans_le (D.integral_ge i)

end SmoothHolderData

/-- **D-GH, smooth case** (MA4 A7, Steps 1–3): under `SmoothHolderData` and the gradient
condition `c ‖∑ ξ_i‖² ≤ ∑ ‖ξ_i‖²` (`ξ_i ∈ S i`),
`∫ ∏_i (H i x)^c dγ(x) ≤ ∏_i (∫ H i dγ)^c`. -/
theorem integral_prod_rpow_le_of_smooth {H : ι → E → ℝ} {DH : ι → E → E}
    {S : ι → Submodule ℝ E} {δ C c : ℝ} (D : SmoothHolderData H DH S δ C) (hc : 0 ≤ c)
    (hS : ∀ ξ : ι → E, (∀ i, ξ i ∈ S i) → c * ‖∑ i, ξ i‖ ^ 2 ≤ ∑ i, ‖ξ i‖ ^ 2) :
    ∫ x, ∏ i, H i x ^ c ∂(stdGaussian E) ≤ ∏ i, (∫ x, H i x ∂(stdGaussian E)) ^ c := by
  rw [← D.holderFun_zero, ← D.holderFun_pi_div_two]
  exact D.holderFun_zero_le hc hS

end Fintype

end HigherDimLQGMetric.Gauss
