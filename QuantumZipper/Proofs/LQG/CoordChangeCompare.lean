import QuantumZipper.Proofs.LQG.CoordChangeTRL
import QuantumZipper.Proofs.LQG.CoordChangeTilt

/-!
# M4-T4, step 3: pointwise `L¹` comparison of the densities

At a fixed point `t` of the inner interval compare the density of `bdryApprox γ y k`,
`y = coordChange (X ω) ψ Q` (normalized by `X ω (fc(0, R))`), with the density at the
semicircle `fc(ψ t, ψ'(t) 2^{-k})`, multiplied by the Jacobian `ψ'(t)`:

  `E|dA − dB| ≤ Kc · (2^{-k})^{1/2 − γ²/12}`   (`integral_abs_dA_sub_dB_le`).

Ingredients: the energy lemma (`abs_kernelCov2_pc_fc_le`), the variance of `X(ψ_* fc)`
(`abs_varA_sub_varB_le`), the tilted comparison (`integral_abs_exp_sub_exp_le`), the identity
`γQ/2 = 1 + γ²/4` for `Q = 2/γ + γ/2`, and `|cc − log ψ'(t)| ≤ (4C/m) r`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate Real
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CoordChange

open GaussTK BdryExist

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasLaw_pair {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) {p₁ p₂ : Measure ℂ} (h₁ : IsAdmissibleH p₁)
    (h₂ : IsAdmissibleH p₂) (hm : p₁ univ = p₂ univ) :
    HasLaw (fun ω => X ω p₁ - X ω p₂)
      (gaussianReal 0 (kernelCov2 neumannH (p₁, p₂) (p₁, p₂)).toNNReal) P := by
  have hG : HasGaussianLaw (fun ω => X ω p₁ - X ω p₂) P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(p₁, p₂), h₁, h₂, hm⟩
  have hmeas : AEMeasurable (fun ω => X ω p₁ - X ω p₂) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  refine ⟨hmeas, ?_⟩
  rw [hG.map_eq_gaussianReal, hX.centered _ _ h₁ h₂ hm, ← covariance_self hmeas,
    hX.covariance_eq (p₁, p₂) (p₁, p₂) h₁ h₂ hm h₁ h₂ hm]

theorem measurable_avgReg_coordChange_at {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (ψ : ℂ → ℂ) (Q : ℝ) (k : ℕ) (t : ℝ) :
    Measurable fun ω => avgReg (coordChange (X ω) ψ Q) k (t : ℂ) := by
  unfold avgReg
  exact (StronglyMeasurable.limUnder fun n =>
    ((measurable_coordChange_apply ψ Q _).comp (measurable_fieldSample hX)).stronglyMeasurable).measurable

theorem measurable_wProc_at {P : Measure Ω} {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (ψ : ℂ → ℂ) (R r t : ℝ) :
    Measurable fun ω => wProc X ψ R r t ω := by
  unfold wProc wRaw
  exact (StronglyMeasurable.limUnder fun n =>
    (((measurable_evalReg _).comp (measurable_fieldSample hX)).sub
      (hX.measurable_coord _)).stronglyMeasurable).measurable

theorem Qc_mul (γ : ℝ) (hγ : γ ≠ 0) : γ / 2 * Qc γ = 1 + γ ^ 2 / 4 := by
  unfold Qc; field_simp; ring

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

theorem abs_kernelCov_pc_self_add_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr : 0 < r) (hr0 : r ≤ r0 δ m C) :
    |kernelCov neumannH (pc ψ t r) (pc ψ t r) + 2 * log r + 2 * log (deriv ψ t).re| ≤
      8 * C / m * r := by
  have hrδ : r ≤ δ := hr0.trans r0_le_δ
  have htt : |t - t| + r ≤ r := by simp
  rw [h.kernelCov_pc_left ht hrδ hr htt (pc ψ t r), add_assoc]
  refine (integrable_and_abs_integral_add_le
    (h.aestronglyMeasurable_potF_comp ht hrδ hr htt (pc ψ t r)) ?_).2
  filter_upwards [ae_mem_circleUnif hr htt, ae_norm_circleUnif t hr] with w hw hw'
  rw [h.potF_psi_foldH ht hrδ hw, h.potF_pc ht hrδ hr htt]
  obtain ⟨hi, hb, -, heq⟩ := h.integral_neumannH_psi ht hr.le hr0 hr htt hw
  rw [heq, norm_sub_rev, hw', max_self]
  have := (integrable_and_abs_integral_add_le hi.1 hb).2
  calc |∫ v', rem ψ w v' ∂circleUnif (t : ℂ) r - 2 * log r +
        (2 * log r + 2 * log (deriv ψ t).re)|
      = |∫ v', rem ψ w v' ∂circleUnif (t : ℂ) r + 2 * log (deriv ψ t).re| := by ring_nf
    _ ≤ _ := this

theorem norm_psi_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ} (hr : 0 < r)
    (hr0 : r ≤ r0 δ m C) {w : ℂ} (hw : w ∈ closedBall (t : ℂ) r) :
    ‖ψ w‖ ≤ |(ψ t).re| + r * ((deriv ψ t).re + m / 2) := by
  have hrδ : r ≤ δ := hr0.trans r0_le_δ
  have htB : (t : ℂ) ∈ closedBall (t : ℂ) r := mem_closedBall_self hr.le
  have hsub := h.sub_eq ht (h.closedBall_sub t hrδ hw) (h.closedBall_sub t hrδ htB)
  have hψt : ‖ψ t‖ = |(ψ t).re| := by
    have him := h.im_eq_zero ht (mem_ball_self (by linarith [h.δpos]) : (t : ℂ) ∈ ball (t : ℂ) (2 * δ))
    rw [show ψ t = (((ψ t).re : ℝ) : ℂ) from Complex.ext (by simp) (by simp [him]),
      Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
  have hdq : ‖dq ψ w t‖ ≤ (deriv ψ t).re + m / 2 := by
    have h1 := h.norm_dq_sub_deriv_le ht hrδ hw htB
    have h2 := h.two_C_r_le ht hr.le hr0
    have h3 := norm_sub_norm_le (dq ψ w t) (deriv ψ t)
    rw [h.norm_deriv ht] at h3
    linarith
  have hwt : ‖w - t‖ ≤ r := by rw [← dist_eq_norm]; exact hw
  calc ‖ψ w‖ = ‖ψ t + (w - t) * dq ψ w t‖ := by rw [← hsub]; ring_nf
    _ ≤ ‖ψ t‖ + ‖w - t‖ * ‖dq ψ w t‖ := by rw [← norm_mul]; exact norm_add_le _ _
    _ ≤ |(ψ t).re| + r * ((deriv ψ t).re + m / 2) := by
        rw [hψt]
        exact add_le_add le_rfl (mul_le_mul hwt hdq (norm_nonneg _) hr.le)

/-- The variance of `X(ψ_* fc(t,r)) − X(fc(0,R))` is that of the comparison semicircle up to
`O(r)`. -/
theorem abs_varA_sub_varB_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ}
    (hr : 0 < r) (hr0 : r ≤ r0 δ m C) {R : ℝ} (hR : |(ψ t).re| + 1 ≤ R)
    (hr1 : r * ((deriv ψ t).re + m / 2) ≤ 1) :
    |kernelCov2 neumannH (pc ψ t r, foldedCircle 0 R) (pc ψ t r, foldedCircle 0 R) -
      (2 * log R - 2 * log ((deriv ψ t).re * r))| ≤ 8 * C / m * r := by
  have hrδ : r ≤ δ := hr0.trans r0_le_δ
  have htt : |t - t| + r ≤ r := by simp
  have hR0 : 0 < R := by linarith [abs_nonneg (ψ t).re]
  have hμ : IsAdmissibleH (pc ψ t r) := h.isAdmissibleH_pc ht hr.le hr0 hr htt
  have hν : IsAdmissibleH (foldedCircle 0 R) := isAdmissibleH_foldedCircle zero_mem_Hbar hR0
  have hK1 := h.abs_kernelCov_pc_self_add_le ht hr hr0
  have hK2 : kernelCov neumannH (pc ψ t r) (foldedCircle 0 R) = -2 * log R := by
    rw [h.kernelCov_pc_left ht hrδ hr htt]
    have e : ∀ᵐ w ∂circleUnif (t : ℂ) r,
        potF (foldedCircle 0 R) (ψ (foldH w)) = -2 * log R := by
      filter_upwards [ae_mem_circleUnif hr htt] with w hw
      rw [h.potF_psi_foldH ht hrδ hw]
      have := potF_fc_real 0 hR0 (ψ w)
      rw [Complex.ofReal_zero] at this
      rw [this, zero_sub, norm_neg, max_eq_left]
      linarith [h.norm_psi_le ht hr hr0 hw]
    rw [integral_congr_ae e]; simp
  have hK3 : kernelCov neumannH (foldedCircle 0 R) (pc ψ t r) = -2 * log R := by
    rw [kernelCov_comm_of_admissible hν hμ, hK2]
  have hK4 : kernelCov neumannH (foldedCircle 0 R) (foldedCircle 0 R) = -2 * log R := by
    have := kernelCov_fc_real_sameCenter (s := 0) hR0 hR0
    rw [Complex.ofReal_zero, max_self] at this
    exact this
  have hd := h.deriv_re_pos ht
  unfold kernelCov2
  simp only
  rw [hK2, hK3, hK4, log_mul hd.ne' hr.ne']
  have e : kernelCov neumannH (pc ψ t r) (pc ψ t r) - -2 * log R - -2 * log R + -2 * log R -
      (2 * log R - 2 * (log (deriv ψ t).re + log r)) =
      kernelCov neumannH (pc ψ t r) (pc ψ t r) + 2 * log r + 2 * log (deriv ψ t).re := by ring
  rw [e]; exact hK1

theorem abs_cc_sub_log_le (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {r : ℝ} (hr : 0 < r)
    (hr0 : r ≤ r0 δ m C) : |cc ψ t r - log (deriv ψ t).re| ≤ 4 * C / m * r := by
  have hrδ : r ≤ δ := hr0.trans r0_le_δ
  have htt : |t - t| + r ≤ r := by simp
  have htB : (t : ℂ) ∈ closedBall (t : ℂ) r := mem_closedBall_self hr.le
  have hgc := h.continuousOn_log_norm_deriv ht hr.le hr0
  have hae := ae_mem_foldedCircle hr htt
  have hsm : AEStronglyMeasurable (fun z => log ‖deriv ψ z‖) (foldedCircle (t : ℂ) r) := by
    have := hgc.aestronglyMeasurable (μ := foldedCircle (t : ℂ) r) measurableSet_closedBall
    rwa [Measure.restrict_eq_self_of_ae_mem (hae.mono fun z hz => hz.1)] at this
  have hL : log (deriv ψ t).re = log ‖deriv ψ (t : ℂ)‖ := by rw [h.norm_deriv ht]
  unfold cc
  rw [hL, sub_eq_add_neg]
  refine (integrable_and_abs_integral_add_le hsm (c := -log ‖deriv ψ (t : ℂ)‖) ?_).2
  filter_upwards [hae] with z hz
  rw [← sub_eq_add_neg]
  refine (h.abs_log_norm_deriv_sub_le ht hr.le hr0 hz.1 htB).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by linarith [h.C_nonneg ht]) h.mpos.le)
  rw [← dist_eq_norm]; exact hz.1

/-- The constant of the pointwise comparison. -/
def Kc (γ R m C : ℝ) (j : ℕ) : ℝ :=
  γ / 2 * M4 ^ (1 / 4 : ℝ) * √(24 * C / m) * 2 *
      exp ((1 + γ ^ 2 / 4) * (|log m| + j * log 2 + 1) +
        4 / 3 * (γ / 2) ^ 2 * (log R + (|log m| + j * log 2) + 1)) +
    2 * (1 + γ ^ 2 / 4) * (4 * C / m) *
      exp ((1 + γ ^ 2 / 4) * (|log m| + j * log 2 + 1) +
        (γ / 2) ^ 2 * (log R + (|log m| + j * log 2)))

set_option maxHeartbeats 2000000 in
/-- **Pointwise comparison of the densities** (M4-T4 step 3). -/
theorem integral_abs_dA_sub_dB_le {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) {γ : ℝ}
    (hγ : 0 < γ) (_hγ2 : γ < 2) {R : ℝ} (hR : |(ψ t).re| + 1 ≤ R) {j k : ℕ}
    (hj : (deriv ψ t).re ≤ 2 ^ j) (hk0 : 2 * radius k ≤ r0 δ m C)
    (hk1 : 2 ^ j * radius k ≤ 1 / 4) :
    Integrable (fun ω => |radius k ^ (γ ^ 2 / 4) * exp (γ / 2 *
        (avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - X ω (foldedCircle 0 R))) -
        (deriv ψ t).re * ((deriv ψ t).re * radius k) ^ (γ ^ 2 / 4) *
          exp (γ / 2 * wProc X ψ R (radius k) t ω)|) P ∧
    ∫ ω, |radius k ^ (γ ^ 2 / 4) * exp (γ / 2 *
        (avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - X ω (foldedCircle 0 R))) -
        (deriv ψ t).re * ((deriv ψ t).re * radius k) ^ (γ ^ 2 / 4) *
          exp (γ / 2 * wProc X ψ R (radius k) t ω)| ∂P
      ≤ Kc γ R m C j * exp ((1 / 2 - γ ^ 2 / 12) * log (radius k)) := by
  -- scalars
  have hr : 0 < radius k := radius_pos k
  have hr1 : radius k ≤ 1 := radius_le_one k
  have hlr : log (radius k) ≤ 0 := log_nonpos hr.le hr1
  have hr0 : radius k ≤ r0 δ m C := by linarith
  have hm := h.mpos
  have hC := h.C_nonneg ht
  have hdm : m ≤ (deriv ψ t).re := h.dre t ht
  have h24 : 0 ≤ 24 * C / m := div_nonneg (by linarith) hm.le
  have h4 : 0 ≤ 4 * C / m := div_nonneg (by linarith) hm.le
  have hd : 0 < (deriv ψ t).re := hm.trans_le hdm
  have hLΛ : |log (deriv ψ t).re| ≤ |log m| + j * log 2 := by
    have h1 : log m ≤ log (deriv ψ t).re := log_le_log hm hdm
    have h2 : log (deriv ψ t).re ≤ j * log 2 := by
      have := log_le_log hd hj; rwa [log_pow] at this
    have h3 : 0 ≤ (j : ℝ) * log 2 := mul_nonneg (Nat.cast_nonneg j) (log_nonneg one_le_two)
    rw [abs_le]; constructor <;> linarith [neg_abs_le (log m), le_abs_self (log m)]
  have hCr : C * radius k / m ≤ 1 / 4 := by
    have h1 : radius k ≤ m / (4 * (C + 1)) := hr0.trans (min_le_right _ _)
    rw [div_le_iff₀ hm]
    calc C * radius k ≤ C * (m / (4 * (C + 1))) := mul_le_mul_of_nonneg_left h1 hC
      _ ≤ 1 / 4 * m := by
          rw [mul_div_assoc', div_le_iff₀ (by linarith : (0:ℝ) < 4 * (C + 1))]; nlinarith
  have hρ : 0 < (deriv ψ t).re * radius k := mul_pos hd hr
  have hρ4 : (deriv ψ t).re * radius k ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_right hj hr.le).trans hk1
  have hrd : radius k * ((deriv ψ t).re + m / 2) ≤ 1 := by
    have : radius k * ((deriv ψ t).re + m / 2) ≤ radius k * (2 * 2 ^ j) := by
      apply mul_le_mul_of_nonneg_left _ hr.le; linarith
    nlinarith
  have hαQ : γ / 2 * Qc γ = 1 + γ ^ 2 / 4 := Qc_mul γ hγ.ne'
  have hα0 : 0 ≤ γ / 2 := by linarith
  -- measures and Gaussian variables
  have htt : |t - t| + radius k ≤ radius k := by simp
  have hR0 : 0 < R := by linarith [abs_nonneg (ψ t).re]
  have hlogR : 0 ≤ log R := log_nonneg (by linarith [abs_nonneg (ψ t).re])
  have hμ : IsAdmissibleH (pc ψ t (radius k)) := h.isAdmissibleH_pc ht hr.le hr0 hr htt
  have hν0 : IsAdmissibleH (foldedCircle 0 R) := isAdmissibleH_foldedCircle zero_mem_Hbar hR0
  have hνρ : IsAdmissibleH (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) :=
    isAdmissibleH_foldedCircle (ofReal_mem_Hbar _) hρ
  have lA := hasLaw_pair hX hμ hν0 (by rw [measure_univ, measure_univ])
  have lB := hasLaw_pair hX hνρ hν0 (by rw [measure_univ, measure_univ])
  have lD : HasLaw (fun ω =>
      (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) -
        X ω (foldedCircle 0 R)) - (X ω (pc ψ t (radius k)) - X ω (foldedCircle 0 R)))
      (gaussianReal 0 (kernelCov2 neumannH
        (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))
        (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))).toNNReal)
      P :=
    (hasLaw_pair hX hνρ hμ (by rw [measure_univ, measure_univ])).congr
      (ae_of_all _ fun ω => by dsimp only; ring)
  have hAm : AEMeasurable (fun ω => X ω (pc ψ t (radius k)) - X ω (foldedCircle 0 R)) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hBm : AEMeasurable (fun ω =>
      X ω (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) -
        X ω (foldedCircle 0 R)) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  obtain ⟨hTi, hT⟩ := integral_abs_exp_sub_exp_le hAm hBm lA lB lD hα0
  -- variances
  obtain ⟨vB, hvB⟩ : ∃ v : ℝ, v = 2 * log R - 2 * log ((deriv ψ t).re * radius k) := ⟨_, rfl⟩
  have hvB0 : 0 ≤ vB := by
    have : log ((deriv ψ t).re * radius k) ≤ 0 := log_nonpos hρ.le (by linarith)
    rw [hvB]; linarith
  have hvBeq : kernelCov2 neumannH
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), foldedCircle 0 R)
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), foldedCircle 0 R) = vB := by
    rw [hvB]; exact fcPairCov_Zself (t := (ψ t).re) hρ (by linarith)
  have hvA := h.abs_varA_sub_varB_le ht hr hr0 hR hrd
  rw [← hvB] at hvA
  have hvD : |kernelCov2 neumannH
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))| ≤
      24 * C / m * radius k := by
    have := h.abs_kernelCov2_pc_fc_le ht hr hr0
    have e : kernelCov2 neumannH
        (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))
        (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k)) =
        kernelCov2 neumannH
        (pc ψ t (radius k), foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k))
        (pc ψ t (radius k), foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) := by
      unfold kernelCov2; ring
    rw [e]; exact this
  have h8 : 8 * C / m * radius k ≤ 2 := by
    have : 8 * C / m * radius k = 8 * (C * radius k / m) := by ring
    rw [this]; linarith
  have hvA' : ((kernelCov2 neumannH (pc ψ t (radius k), foldedCircle 0 R)
      (pc ψ t (radius k), foldedCircle 0 R)).toNNReal : ℝ) ≤ vB + 2 := by
    rw [Real.coe_toNNReal']
    refine max_le ?_ (by linarith)
    have := (abs_le.1 hvA).2
    linarith
  have hvB' : ((kernelCov2 neumannH
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), foldedCircle 0 R)
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), foldedCircle 0 R)).toNNReal
        : ℝ) = vB := by
    rw [hvBeq, Real.coe_toNNReal _ hvB0]
  have hvD' : ((kernelCov2 neumannH
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))).toNNReal
        : ℝ) ≤ 24 * C / m * radius k := by
    rw [Real.coe_toNNReal']
    exact max_le ((le_abs_self _).trans hvD) (mul_nonneg h24 hr.le)
  -- the tilt term, bounded
  obtain ⟨T0, hT0⟩ : ∃ T : ℝ, T = ∫ ω, |exp (γ / 2 * (X ω (pc ψ t (radius k)) -
      X ω (foldedCircle 0 R))) - exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ)
      ((deriv ψ t).re * radius k)) - X ω (foldedCircle 0 R)))| ∂P := ⟨_, rfl⟩
  have hT' : T0 ≤ γ / 2 * M4 ^ (1 / 4 : ℝ) * √(24 * C / m) * exp (log (radius k) / 2) *
      (2 * exp (4 / 3 * (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k) + 1))) := by
    rw [hT0]
    refine hT.trans ?_
    set vD := ((kernelCov2 neumannH
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))
      (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), pc ψ t (radius k))).toNNReal
        : ℝ) with hvDdef
    have hD0 : 0 ≤ vD := NNReal.coe_nonneg _
    have e1 : (M4 * vD ^ 2) ^ (1 / 4 : ℝ) = M4 ^ (1 / 4 : ℝ) * √vD := by
      rw [mul_rpow M4_nonneg (by positivity), Real.sqrt_eq_rpow, ← rpow_natCast, ← rpow_mul hD0]
      norm_num
    have e2 : √(24 * C / m * radius k) = √(24 * C / m) * exp (log (radius k) / 2) := by
      rw [Real.sqrt_mul h24, Real.sqrt_eq_rpow (radius k), rpow_def_of_pos hr]
      congr 2; ring
    rw [e1]
    have b1 : √vD ≤ √(24 * C / m) * exp (log (radius k) / 2) := by
      rw [← e2]; exact Real.sqrt_le_sqrt hvD'
    have e3 : 2 / 3 * (γ / 2) ^ 2 * (vB + 2) =
        4 / 3 * (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k) + 1) := by
      rw [hvB, log_mul hd.ne' hr.ne']; ring
    have c1 : exp (2 / 3 * (γ / 2) ^ 2 * ((kernelCov2 neumannH (pc ψ t (radius k),
        foldedCircle 0 R) (pc ψ t (radius k), foldedCircle 0 R)).toNNReal : ℝ)) ≤
        exp (4 / 3 * (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k) + 1)) := by
      rw [← e3]; exact exp_le_exp.2 (mul_le_mul_of_nonneg_left hvA' (by positivity))
    have c2 : exp (2 / 3 * (γ / 2) ^ 2 * ((kernelCov2 neumannH
        (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), foldedCircle 0 R)
        (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), foldedCircle 0 R)).toNNReal
          : ℝ)) ≤
        exp (4 / 3 * (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k) + 1)) := by
      rw [← e3, hvB']
      exact exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    have hM4 : 0 ≤ M4 ^ (1 / 4 : ℝ) := rpow_nonneg M4_nonneg _
    have hsq : 0 ≤ √vD := Real.sqrt_nonneg _
    calc γ / 2 * (M4 ^ (1 / 4 : ℝ) * √vD) *
          (exp (2 / 3 * (γ / 2) ^ 2 * ((kernelCov2 neumannH (pc ψ t (radius k),
            foldedCircle 0 R) (pc ψ t (radius k), foldedCircle 0 R)).toNNReal : ℝ)) +
          exp (2 / 3 * (γ / 2) ^ 2 * ((kernelCov2 neumannH
            (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), foldedCircle 0 R)
            (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k),
              foldedCircle 0 R)).toNNReal : ℝ)))
        ≤ γ / 2 * (M4 ^ (1 / 4 : ℝ) * (√(24 * C / m) * exp (log (radius k) / 2))) *
          (exp (4 / 3 * (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k) + 1)) +
          exp (4 / 3 * (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k) + 1))) := by
          gcongr
      _ = _ := by ring
  -- the exponential moment of `B`
  have hEB : ∫ ω, exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ)
      ((deriv ψ t).re * radius k)) - X ω (foldedCircle 0 R))) ∂P = exp (vB * (γ / 2) ^ 2 / 2) := by
    have hcomp := lB.integral_comp (f := fun x : ℝ => exp (γ / 2 * x)) (by fun_prop)
    rw [Function.comp_def] at hcomp
    rw [hcomp, ← hvB']
    have := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := (kernelCov2 neumannH
        (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k), foldedCircle 0 R)
        (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k),
          foldedCircle 0 R)).toNNReal)) (γ / 2)
    simp only [mgf] at this
    simpa [mul_comm] using this
  have hBi : Integrable (fun ω => exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ)
      ((deriv ψ t).re * radius k)) - X ω (foldedCircle 0 R)))) P := by
    have := lB.integrable_comp (f := fun x : ℝ => exp (γ / 2 * x))
      (integrable_exp_mul_gaussianReal (γ / 2))
    simpa [Function.comp_def] using this
  -- deterministic factors
  have hccL := h.abs_cc_sub_log_le ht hr hr0
  obtain ⟨E1, hE1⟩ : ∃ E : ℝ, E = exp ((γ / 2) ^ 2 * log (radius k) +
      γ / 2 * Qc γ * cc ψ t (radius k)) := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E : ℝ, E = exp ((γ / 2) ^ 2 * log (radius k) +
      γ / 2 * Qc γ * log (deriv ψ t).re) := ⟨_, rfl⟩
  have hcc1 : cc ψ t (radius k) ≤ |log m| + j * log 2 + 1 := by
    have : 4 * C / m * radius k ≤ 1 := by
      have : 4 * C / m * radius k = 4 * (C * radius k / m) := by ring
      rw [this]; linarith
    linarith [(abs_le.1 hccL).2, le_abs_self (log (deriv ψ t).re)]
  have hαQ0 : 0 ≤ γ / 2 * Qc γ := by rw [hαQ]; positivity
  have hE1le : E1 ≤ exp ((γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * (|log m| + j * log 2 + 1)) := by
    rw [hE1]
    have := mul_le_mul_of_nonneg_left hcc1 hαQ0
    exact exp_le_exp.2 (by linarith)
  have hE2le : E2 ≤ exp ((γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * (|log m| + j * log 2 + 1)) := by
    rw [hE2]
    have hl : log (deriv ψ t).re ≤ |log m| + j * log 2 + 1 := by
      linarith [le_abs_self (log (deriv ψ t).re)]
    have := mul_le_mul_of_nonneg_left hl hαQ0
    exact exp_le_exp.2 (by linarith)
  have hE12 : |E1 - E2| ≤ γ / 2 * Qc γ * (4 * C / m * radius k) *
      (2 * exp ((γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * (|log m| + j * log 2 + 1))) := by
    have h1 := abs_exp_sub_exp_le ((γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * cc ψ t (radius k))
      ((γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * log (deriv ψ t).re)
    rw [← hE1, ← hE2] at h1
    refine h1.trans ?_
    have e : (γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * cc ψ t (radius k) -
        ((γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * log (deriv ψ t).re) =
        γ / 2 * Qc γ * (cc ψ t (radius k) - log (deriv ψ t).re) := by ring
    rw [e, abs_mul, abs_of_nonneg hαQ0]
    have hsum : E1 + E2 ≤ 2 * exp ((γ / 2) ^ 2 * log (radius k) +
        γ / 2 * Qc γ * (|log m| + j * log 2 + 1)) := by linarith
    have hE0 : 0 ≤ E1 + E2 := by rw [hE1, hE2]; positivity
    calc γ / 2 * Qc γ * |cc ψ t (radius k) - log (deriv ψ t).re| * (E1 + E2)
        ≤ γ / 2 * Qc γ * (4 * C / m * radius k) * (E1 + E2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hccL hαQ0) hE0
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum (mul_nonneg hαQ0 (mul_nonneg h4 hr.le))
  -- the pointwise inequality, almost surely
  have hY := h.ae_avgReg_coordChange hX ht (Qc γ) hk0
  have hW := h.ae_wProc_eq hX ht R hr hρ4
  have hpt : ∀ᵐ ω ∂P, |radius k ^ (γ ^ 2 / 4) * exp (γ / 2 *
      (avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - X ω (foldedCircle 0 R))) -
      (deriv ψ t).re * ((deriv ψ t).re * radius k) ^ (γ ^ 2 / 4) *
        exp (γ / 2 * wProc X ψ R (radius k) t ω)| ≤
      E1 * |exp (γ / 2 * (X ω (pc ψ t (radius k)) - X ω (foldedCircle 0 R))) -
        exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) -
          X ω (foldedCircle 0 R)))| +
      |E1 - E2| * exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ)
        ((deriv ψ t).re * radius k)) - X ω (foldedCircle 0 R))) := by
    filter_upwards [hY, hW] with ω hYω hWω
    have eA : radius k ^ (γ ^ 2 / 4) * exp (γ / 2 *
        (avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - X ω (foldedCircle 0 R))) =
        E1 * exp (γ / 2 * (X ω (pc ψ t (radius k)) - X ω (foldedCircle 0 R))) := by
      rw [hYω, hE1, rpow_def_of_pos hr, ← exp_add, ← exp_add]
      congr 1; ring
    have eB : (deriv ψ t).re * ((deriv ψ t).re * radius k) ^ (γ ^ 2 / 4) *
        exp (γ / 2 * wProc X ψ R (radius k) t ω) =
        E2 * exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) -
          X ω (foldedCircle 0 R))) := by
      rw [hWω, hE2, rpow_def_of_pos hρ, log_mul hd.ne' hr.ne']
      have e0 : (deriv ψ t).re = exp (log (deriv ψ t).re) := (exp_log hd).symm
      calc (deriv ψ t).re * exp ((log (deriv ψ t).re + log (radius k)) * (γ ^ 2 / 4)) *
            exp (γ / 2 * fcPairVal X ((((ψ t).re : ℝ) : ℂ), (deriv ψ t).re * radius k, 0, R) ω)
          = exp (log (deriv ψ t).re) * exp ((log (deriv ψ t).re + log (radius k)) * (γ ^ 2 / 4)) *
            exp (γ / 2 * fcPairVal X ((((ψ t).re : ℝ) : ℂ), (deriv ψ t).re * radius k, 0, R) ω) := by
            rw [exp_log hd]
        _ = _ := by
            rw [← exp_add, ← exp_add, ← exp_add]
            congr 1
            simp only [fcPairVal]
            rw [hαQ]; ring
    rw [eA, eB]
    have e : E1 * exp (γ / 2 * (X ω (pc ψ t (radius k)) - X ω (foldedCircle 0 R))) -
        E2 * exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) -
          X ω (foldedCircle 0 R))) =
        E1 * (exp (γ / 2 * (X ω (pc ψ t (radius k)) - X ω (foldedCircle 0 R))) -
          exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) -
            X ω (foldedCircle 0 R)))) +
        (E1 - E2) * exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ)
          ((deriv ψ t).re * radius k)) - X ω (foldedCircle 0 R))) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    have hE10 : 0 ≤ E1 := by rw [hE1]; exact (exp_pos _).le
    rw [abs_mul, abs_mul, abs_of_nonneg hE10, abs_of_pos (exp_pos _)]
  -- integrability
  have hdom : Integrable (fun ω =>
      E1 * |exp (γ / 2 * (X ω (pc ψ t (radius k)) - X ω (foldedCircle 0 R))) -
        exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) -
          X ω (foldedCircle 0 R)))| +
      |E1 - E2| * exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ)
        ((deriv ψ t).re * radius k)) - X ω (foldedCircle 0 R)))) P :=
    (hTi.const_mul _).add (hBi.const_mul _)
  have hmeasL : AEStronglyMeasurable (fun ω => |radius k ^ (γ ^ 2 / 4) * exp (γ / 2 *
      (avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - X ω (foldedCircle 0 R))) -
      (deriv ψ t).re * ((deriv ψ t).re * radius k) ^ (γ ^ 2 / 4) *
        exp (γ / 2 * wProc X ψ R (radius k) t ω)|) P := by
    have h1 := measurable_avgReg_coordChange_at hX ψ (Qc γ) k t
    have h2 := measurable_wProc_at hX ψ R (radius k) t
    have h3 : Measurable fun ω => X ω (foldedCircle 0 R) := hX.measurable_coord (foldedCircle 0 R)
    have hA : Measurable fun ω => radius k ^ (γ ^ 2 / 4) * exp (γ / 2 *
        (avgReg (coordChange (X ω) ψ (Qc γ)) k (t : ℂ) - X ω (foldedCircle 0 R))) :=
      Measurable.const_mul (((h1.sub h3).const_mul (γ / 2)).exp) _
    have hB' : Measurable fun ω => (deriv ψ t).re * ((deriv ψ t).re * radius k) ^ (γ ^ 2 / 4) *
        exp (γ / 2 * wProc X ψ R (radius k) t ω) :=
      Measurable.const_mul ((h2.const_mul (γ / 2)).exp) _
    exact (continuous_abs.measurable.comp (hA.sub hB')).aestronglyMeasurable
  have hint := hdom.mono' hmeasL (hpt.mono fun ω hω => by rw [Real.norm_eq_abs, abs_abs]; exact hω)
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ ω, (E1 * |exp (γ / 2 * (X ω (pc ψ t (radius k)) - X ω (foldedCircle 0 R))) -
          exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ) ((deriv ψ t).re * radius k)) -
            X ω (foldedCircle 0 R)))| +
        |E1 - E2| * exp (γ / 2 * (X ω (foldedCircle (((ψ t).re : ℝ) : ℂ)
          ((deriv ψ t).re * radius k)) - X ω (foldedCircle 0 R)))) ∂P :=
        integral_mono_ae hint hdom hpt
    _ = E1 * T0 + |E1 - E2| * exp (vB * (γ / 2) ^ 2 / 2) := by
        rw [integral_add (hTi.const_mul _) (hBi.const_mul _), integral_const_mul,
          integral_const_mul, hEB, hT0]
    _ ≤ exp ((γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * (|log m| + j * log 2 + 1)) *
          (γ / 2 * M4 ^ (1 / 4 : ℝ) * √(24 * C / m) * exp (log (radius k) / 2) *
            (2 * exp (4 / 3 * (γ / 2) ^ 2 *
              (log R - log (deriv ψ t).re - log (radius k) + 1)))) +
        γ / 2 * Qc γ * (4 * C / m * radius k) *
          (2 * exp ((γ / 2) ^ 2 * log (radius k) + γ / 2 * Qc γ * (|log m| + j * log 2 + 1))) *
          exp (vB * (γ / 2) ^ 2 / 2) := by
        have hT00 : 0 ≤ T0 := by rw [hT0]; exact integral_nonneg fun _ => abs_nonneg _
        have hE10 : 0 ≤ E1 := by rw [hE1]; exact (exp_pos _).le
        gcongr
    _ ≤ Kc γ R m C j * exp ((1 / 2 - γ ^ 2 / 12) * log (radius k)) := by
        have hvBL : vB * (γ / 2) ^ 2 / 2 =
            (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k)) := by
          rw [hvB, log_mul hd.ne' hr.ne']; ring
        rw [hvBL, hαQ]
        set Λ := |log m| + j * log 2 with hΛ
        have hLΛ' : -Λ ≤ log (deriv ψ t).re := by linarith [neg_abs_le (log (deriv ψ t).re)]
        have t1 : exp ((γ / 2) ^ 2 * log (radius k) + (1 + γ ^ 2 / 4) * (Λ + 1)) *
            (γ / 2 * M4 ^ (1 / 4 : ℝ) * √(24 * C / m) * exp (log (radius k) / 2) *
              (2 * exp (4 / 3 * (γ / 2) ^ 2 *
                (log R - log (deriv ψ t).re - log (radius k) + 1)))) ≤
            γ / 2 * M4 ^ (1 / 4 : ℝ) * √(24 * C / m) * 2 *
              exp ((1 + γ ^ 2 / 4) * (Λ + 1) + 4 / 3 * (γ / 2) ^ 2 * (log R + Λ + 1)) *
              exp ((1 / 2 - γ ^ 2 / 12) * log (radius k)) := by
          have key : (γ / 2) ^ 2 * log (radius k) + (1 + γ ^ 2 / 4) * (Λ + 1) +
              log (radius k) / 2 +
              4 / 3 * (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k) + 1) ≤
              (1 + γ ^ 2 / 4) * (Λ + 1) + 4 / 3 * (γ / 2) ^ 2 * (log R + Λ + 1) +
              (1 / 2 - γ ^ 2 / 12) * log (radius k) := by
            nlinarith [mul_nonneg (sq_nonneg γ) (show 0 ≤ Λ + log (deriv ψ t).re by linarith)]
          have hM4 : 0 ≤ M4 ^ (1 / 4 : ℝ) := rpow_nonneg M4_nonneg _
          have hpos : 0 ≤ γ / 2 * M4 ^ (1 / 4 : ℝ) * √(24 * C / m) * 2 := mul_nonneg (mul_nonneg (mul_nonneg hα0 hM4) (Real.sqrt_nonneg _)) (by norm_num)
          calc _ = γ / 2 * M4 ^ (1 / 4 : ℝ) * √(24 * C / m) * 2 *
                exp ((γ / 2) ^ 2 * log (radius k) + (1 + γ ^ 2 / 4) * (Λ + 1) +
                  log (radius k) / 2 +
                  4 / 3 * (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k) + 1)) := by
                simp only [exp_add]; ring
            _ ≤ _ := by
                rw [mul_assoc (γ / 2 * M4 ^ (1 / 4 : ℝ) * √(24 * C / m) * 2), ← exp_add]
                exact mul_le_mul_of_nonneg_left (exp_le_exp.2 key) hpos
        have t2 : (1 + γ ^ 2 / 4) * (4 * C / m * radius k) *
            (2 * exp ((γ / 2) ^ 2 * log (radius k) + (1 + γ ^ 2 / 4) * (Λ + 1))) *
            exp ((γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k))) ≤
            2 * (1 + γ ^ 2 / 4) * (4 * C / m) *
              exp ((1 + γ ^ 2 / 4) * (Λ + 1) + (γ / 2) ^ 2 * (log R + Λ)) *
              exp ((1 / 2 - γ ^ 2 / 12) * log (radius k)) := by
          have key : (γ / 2) ^ 2 * log (radius k) + (1 + γ ^ 2 / 4) * (Λ + 1) +
              (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k)) ≤
              (1 + γ ^ 2 / 4) * (Λ + 1) + (γ / 2) ^ 2 * (log R + Λ) := by
            nlinarith [mul_nonneg (sq_nonneg (γ / 2)) (show 0 ≤ Λ + log (deriv ψ t).re by linarith)]
          have hrle : radius k ≤ exp ((1 / 2 - γ ^ 2 / 12) * log (radius k)) := by
            conv_lhs => rw [← exp_log hr]
            exact exp_le_exp.2 (by nlinarith [mul_nonneg (sq_nonneg γ) (neg_nonneg.2 hlr)])
          have hpos : 0 ≤ 2 * (1 + γ ^ 2 / 4) * (4 * C / m) := mul_nonneg (mul_nonneg (by norm_num) (by nlinarith [sq_nonneg γ])) h4
          calc _ = 2 * (1 + γ ^ 2 / 4) * (4 * C / m) *
                exp ((γ / 2) ^ 2 * log (radius k) + (1 + γ ^ 2 / 4) * (Λ + 1) +
                  (γ / 2) ^ 2 * (log R - log (deriv ψ t).re - log (radius k))) * radius k := by
                simp only [exp_add]; ring
            _ ≤ _ := by gcongr
        have := add_le_add t1 t2
        refine this.trans (le_of_eq ?_)
        unfold Kc; rw [← hΛ]; ring

end Data

end CoordChange
end QuantumZipper
