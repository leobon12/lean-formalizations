import HigherDimLQGContinuity.Frame.Form
import HigherDimLQGMetric.Sphere.PotCov

/-!
# Pairing frame II: logarithmic potentials of mean-zero test functions

Packet N3 (NA4 Details (a) A2, step 3 and item 10; blueprint Part C `c:lem-frame-pot`).

For a test function `ψ` let `Gψ(y) = ∫ log|y - x|⁻¹ ψ(x) dx`, written with HDLM's potentials of the measures
`ψ^± dx` as `framePotRaw ψ = logPotM (ψ⁺ dx) - logPotM (ψ⁻ dx)`, and `e_ψ = Gψ - ∫ Gψ dσ₁` (`framePot`,
`σ₁ = unitSphereProb d`). For `d ≥ 1`:

* `continuous_framePotRaw`, and `Gψ(y) = ∫ ψ(x) log|y - x|⁻¹ dx` (`framePotRaw_eq_integral`);
* `exists_abs_framePotRaw_le`: `Gψ` is bounded if `∫ ψ = 0` (for `|y| ≥ 2(|D| + 1)` the mean-zero condition gives
  `|Gψ(y)| ≤ log 2 · ‖ψ‖₁`; on the ball, continuity);
* `integral_mul_framePot`: `∫ φ e_ψ = ⟨ψ, φ⟩₋` for mean-zero test functions `φ` (Fubini); `integral_framePot_sphere`:
  `∫ e_ψ dσ₁ = 0` (`d ≥ 1`);
* `integral_framePot_eq_logCov`: `∫ e_ψ dν = logCov(ψ⁺ dx, ψ⁻ dx, ν, σ₁)` for every probability measure `ν` for which
  the four measures are `LogPairable` (Fubini on the four product integrals).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ## Integrals against `f⁺ dx` -/

theorem frame_integral_posM_eq {f : Rd d → ℝ} (hf : Measurable f) (F : Rd d → ℝ) :
    ∫ x, F x ∂(posM f) = ∫ x, max (f x) 0 * F x := by
  rw [posM, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]

theorem frame_integrable_posM_iff {f : Rd d → ℝ} (hf : Measurable f) (F : Rd d → ℝ) :
    Integrable F (posM f) ↔ Integrable (fun x => max (f x) 0 * F x) := by
  rw [posM, integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
  have e : (fun x => (ENNReal.ofReal (f x)).toReal • F x) = fun x => max (f x) 0 * F x := by
    funext x
    rw [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [e]

/-- Fubini for a mutual log energy: `I(μ, α) = ∫ F_μ dα`. -/
theorem logEnergy_eq_integral_logPotM {μ α : Measure (Rd d)} [SFinite μ] [SFinite α]
    (h : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖) (μ.prod α)) :
    logEnergy μ α = ∫ y, logPotM μ y ∂α := by
  unfold logEnergy
  rw [integral_prod_symm _ h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  unfold logPotM
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [norm_sub_rev]

theorem integrable_logPotM_of_prod {μ α : Measure (Rd d)} [SFinite μ] [SFinite α]
    (h : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖) (μ.prod α)) :
    Integrable (logPotM μ) α := by
  have := h.integral_prod_right
  refine this.congr (ae_of_all _ fun y => ?_)
  unfold logPotM
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [norm_sub_rev]

/-! ## The potential of a test function -/

/-- `Gψ = F_{ψ⁺ dx} - F_{ψ⁻ dx}`, i.e. `Gψ(y) = ∫ log|y - x|⁻¹ ψ(x) dx` (`framePotRaw_eq_integral`). -/
def framePotRaw (ψ : TestRd d) (y : Rd d) : ℝ :=
  logPotM (posM ⇑ψ) y - logPotM (posM (-⇑ψ)) y

@[simp]
theorem framePotRaw_zero : framePotRaw (0 : TestRd d) = 0 := by
  funext y
  simp only [framePotRaw, FunLike.coe_zero, neg_zero, sub_self, Pi.zero_apply]

theorem frame_smallBall_const_nonneg {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D) :
    0 ≤ M * volBall d + (posM f).real univ :=
  add_nonneg (mul_nonneg hf.nonneg volBall_nonneg) measureReal_nonneg

section Pot

variable [NeZero d]

theorem continuous_framePotRaw (ψ : TestRd d) : Continuous (framePotRaw ψ) := by
  obtain ⟨M, D, hψ⟩ := exists_isBddSupp_testOn ψ
  have := isFiniteMeasure_posM hψ
  have := isFiniteMeasure_posM hψ.neg
  exact (continuous_logPotM (frame_smallBall_const_nonneg hψ)
    (fun z s hs => posM_real_closedBall_le hψ z hs) (ae_posM_norm_le hψ)).sub
    (continuous_logPotM (frame_smallBall_const_nonneg hψ.neg)
      (fun z s hs => posM_real_closedBall_le hψ.neg z hs) (ae_posM_norm_le hψ.neg))

theorem integrable_mul_neg_log_norm_sub (ψ : TestRd d) (y : Rd d) :
    Integrable fun x => ψ x * (-Real.log ‖y - x‖) := by
  obtain ⟨M, D, hψ⟩ := exists_isBddSupp_testOn ψ
  have := isFiniteMeasure_posM hψ
  have := isFiniteMeasure_posM hψ.neg
  have i1 : Integrable (fun x => -Real.log ‖y - x‖) (posM fun z => ψ z) :=
    (integrable_log_norm_sub_left (frame_smallBall_const_nonneg hψ)
      (fun z s hs => posM_real_closedBall_le hψ z hs) (ae_posM_norm_le hψ) y).neg
  have i2 : Integrable (fun x => -Real.log ‖y - x‖) (posM (-fun z => ψ z)) :=
    (integrable_log_norm_sub_left (frame_smallBall_const_nonneg hψ.neg)
      (fun z s hs => posM_real_closedBall_le hψ.neg z hs) (ae_posM_norm_le hψ.neg) y).neg
  rw [frame_integrable_posM_iff hψ.measurable] at i1
  rw [frame_integrable_posM_iff hψ.neg.measurable] at i2
  refine (i1.sub i2).congr (ae_of_all _ fun x => ?_)
  simp only [Pi.sub_apply, Pi.neg_apply]
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

/-- `Gψ(y) = ∫ ψ(x) log|y - x|⁻¹ dx`. -/
theorem framePotRaw_eq_integral (ψ : TestRd d) (y : Rd d) :
    framePotRaw ψ y = ∫ x, ψ x * (-Real.log ‖y - x‖) := by
  obtain ⟨M, D, hψ⟩ := exists_isBddSupp_testOn ψ
  have := isFiniteMeasure_posM hψ
  have := isFiniteMeasure_posM hψ.neg
  have i1 : Integrable (fun x => -Real.log ‖y - x‖) (posM fun z => ψ z) :=
    (integrable_log_norm_sub_left (frame_smallBall_const_nonneg hψ)
      (fun z s hs => posM_real_closedBall_le hψ z hs) (ae_posM_norm_le hψ) y).neg
  have i2 : Integrable (fun x => -Real.log ‖y - x‖) (posM (-fun z => ψ z)) :=
    (integrable_log_norm_sub_left (frame_smallBall_const_nonneg hψ.neg)
      (fun z s hs => posM_real_closedBall_le hψ.neg z hs) (ae_posM_norm_le hψ.neg) y).neg
  rw [frame_integrable_posM_iff hψ.measurable] at i1
  rw [frame_integrable_posM_iff hψ.neg.measurable] at i2
  have e1 : logPotM (posM ⇑ψ) y = ∫ x, max (ψ x) 0 * (-Real.log ‖y - x‖) :=
    frame_integral_posM_eq hψ.measurable _
  have e2 : logPotM (posM (-⇑ψ)) y = ∫ x, max (-ψ x) 0 * (-Real.log ‖y - x‖) :=
    frame_integral_posM_eq hψ.neg.measurable _
  have i2' : Integrable (fun x => max (-ψ x) 0 * (-Real.log ‖y - x‖)) := i2
  rw [framePotRaw, e1, e2, ← integral_sub i1 i2']
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

/-- `|log a - log b| ≤ log 2` for `b/2 ≤ a ≤ 2b`, `b > 0`. -/
theorem frame_abs_log_sub_log_le {a b : ℝ} (hb : 0 < b) (h1 : b / 2 ≤ a) (h2 : a ≤ 2 * b) :
    |Real.log a - Real.log b| ≤ Real.log 2 := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) h1
  rw [abs_le]
  constructor
  · have := Real.log_le_log (by positivity) h1
    rw [Real.log_div hb.ne' (by norm_num)] at this
    linarith
  · have := Real.log_le_log ha h2
    rw [Real.log_mul (by norm_num) hb.ne'] at this
    linarith

/-- **Boundedness of the potential** of a mean-zero test function. -/
theorem exists_abs_framePotRaw_le (ψ : TestRd d) (hψ0 : ∫ x, ψ x = 0) :
    ∃ C, ∀ y, |framePotRaw ψ y| ≤ C := by
  obtain ⟨M, D, hψ⟩ := exists_isBddSupp_testOn ψ
  set R : ℝ := 2 * (|D| + 1) with hR
  obtain ⟨C₁, hC₁⟩ := (isCompact_closedBall (0 : Rd d) R).exists_bound_of_continuousOn
    (continuous_framePotRaw ψ).continuousOn
  set C₂ : ℝ := Real.log 2 * ∫ x, |ψ x| with hC₂
  refine ⟨max C₁ C₂, fun y => ?_⟩
  by_cases hy : ‖y‖ ≤ R
  · have := hC₁ y (by rwa [mem_closedBall, dist_zero_right])
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [not_le] at hy
    have hD1 : |D| + 1 ≤ ‖y‖ / 2 := by rw [hR] at hy; linarith
    have hy0 : 0 < ‖y‖ := by
      have := abs_nonneg D
      linarith
    have hint := integrable_mul_neg_log_norm_sub ψ y
    have e : framePotRaw ψ y = ∫ x, ψ x * (-Real.log ‖y - x‖ + Real.log ‖y‖) := by
      rw [framePotRaw_eq_integral]
      have h0 : ∫ x, ψ x * Real.log ‖y‖ = 0 := by rw [integral_mul_const, hψ0, zero_mul]
      rw [← add_zero (∫ x, ψ x * (-Real.log ‖y - x‖)), ← h0,
        ← integral_add hint ((integrable_testOn ψ).mul_const _)]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only
      ring
    have hb : ∀ x, ‖ψ x * (-Real.log ‖y - x‖ + Real.log ‖y‖)‖ ≤ Real.log 2 * |ψ x| := by
      intro x
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      by_cases hx : D < ‖x‖
      · rw [hψ.eq_zero x hx, abs_zero, mul_zero, mul_zero]
      · rw [not_lt] at hx
        have hxD : ‖x‖ ≤ |D| := hx.trans (le_abs_self D)
        have h1 : ‖y‖ / 2 ≤ ‖y - x‖ := by
          have := norm_sub_norm_le y x
          linarith
        have h2 : ‖y - x‖ ≤ 2 * ‖y‖ := by
          have := norm_sub_le y x
          linarith
        have := frame_abs_log_sub_log_le hy0 h1 h2
        rw [show -Real.log ‖y - x‖ + Real.log ‖y‖ = -(Real.log ‖y - x‖ - Real.log ‖y‖) by ring,
          abs_neg]
        exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    have hle := norm_integral_le_of_norm_le ((integrable_testOn ψ).abs.const_mul (Real.log 2))
      (ae_of_all _ hb)
    rw [← e, Real.norm_eq_abs, integral_const_mul] at hle
    exact hle.trans (le_max_right _ _)

/-- `∫ φ Gψ = ⟨ψ, φ⟩₋` for test functions `ψ, φ` (Fubini). -/
theorem integral_mul_framePotRaw (ψ φ : TestRd d) :
    ∫ y, φ y * framePotRaw ψ y = frameForm ψ φ := by
  obtain ⟨M, D, hψ⟩ := exists_isBddSupp_testOn ψ
  obtain ⟨M', D', hφ⟩ := exists_isBddSupp_testOn φ
  have hint := integrable_logKer hψ hφ
  unfold frameForm logCovF
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [framePotRaw_eq_integral, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [norm_sub_rev]
  ring

/-- The frame vector of a test function: `e_ψ = Gψ - ∫ Gψ dσ₁` (Part C `c:lem-frame-pot`). -/
def framePot (ψ : TestRd d) : C(Rd d, ℝ) where
  toFun y := framePotRaw ψ y - ∫ u, framePotRaw ψ u ∂(unitSphereProb d)
  continuous_toFun := (continuous_framePotRaw ψ).sub continuous_const

theorem framePot_apply (ψ : TestRd d) (y : Rd d) :
    framePot ψ y = framePotRaw ψ y - ∫ u, framePotRaw ψ u ∂(unitSphereProb d) := rfl

/-- `e_0 = 0` (so `e_j = 0` off `J`, where `ψ_j = 0`). -/
theorem framePot_zero : framePot (0 : TestRd d) = 0 := by
  ext y
  simp only [framePot_apply, framePotRaw_zero, Pi.zero_apply, integral_zero, sub_zero,
    ContinuousMap.zero_apply]

/-- `e_ψ` is bounded for mean-zero `ψ` (Part C `c:lem-frame-pot`(a)). -/
theorem exists_abs_framePot_le (ψ : TestRd d) (hψ0 : ∫ x, ψ x = 0) :
    ∃ C, ∀ y, |framePot ψ y| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_framePotRaw_le ψ hψ0
  refine ⟨C + |∫ u, framePotRaw ψ u ∂(unitSphereProb d)|, fun y => ?_⟩
  rw [framePot_apply]
  exact (abs_sub _ _).trans (add_le_add (hC y) le_rfl)

/-- `∫ e_ψ dσ₁ = 0` (Part C `c:lem-frame-pot`(b)). -/
theorem integral_framePot_sphere (ψ : TestRd d) : ∫ u, framePot ψ u ∂(unitSphereProb d) = 0 := by
  have := isProbabilityMeasure_unitSphereProb (Nat.one_le_iff_ne_zero.2 (NeZero.ne d))
  simp only [framePot_apply]
  rw [integral_sub (integrable_unitSphereProb_of_continuous (continuous_framePotRaw ψ))
    (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]

/-- `∫ φ e_ψ = ⟨ψ, φ⟩₋` for mean-zero `φ` (Part C `c:lem-frame-pot`(b)). -/
theorem integral_mul_framePot (ψ : TestRd d) {φ : TestRd d} (hφ0 : ∫ x, φ x = 0) :
    ∫ y, φ y * framePot ψ y = frameForm ψ φ := by
  obtain ⟨M, D, hφ⟩ := exists_isBddSupp_testOn φ
  simp only [framePot_apply, mul_sub]
  rw [integral_sub (integrable_mul_continuous_of_isBddSupp hφ (continuous_framePotRaw ψ))
    ((integrable_testOn φ).mul_const _), integral_mul_const, hφ0, zero_mul, sub_zero,
    integral_mul_framePotRaw]

/-- **Pairing with a measure** (Part C `c:lem-frame-pot`(c)): for a probability measure `ν` such that
`ψ⁺ dx, ψ⁻ dx, ν, σ₁` are `LogPairable`, `∫ e_ψ dν = logCov(ψ⁺ dx, ψ⁻ dx, ν, σ₁)`. -/
theorem integral_framePot_eq_logCov (ψ : TestRd d) (ν : Measure (Rd d)) [IsProbabilityMeasure ν]
    (hP : HigherDimLFPP.LogPairable (posM ⇑ψ) (posM (-⇑ψ)) ν (unitSphereProb d)) :
    ∫ y, framePot ψ y ∂ν =
      HigherDimLFPP.logCov (posM ⇑ψ) (posM (-⇑ψ)) ν (unitSphereProb d) := by
  obtain ⟨M, D, hψ⟩ := exists_isBddSupp_testOn ψ
  have := isFiniteMeasure_posM hψ
  have := isFiniteMeasure_posM hψ.neg
  have i13 : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖) ((posM ⇑ψ).prod ν) :=
    (hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _)).neg
  have i14 : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖)
      ((posM ⇑ψ).prod (unitSphereProb d)) :=
    (hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₄ _ _ _ _)).neg
  have i23 : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖) ((posM (-⇑ψ)).prod ν) :=
    (hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₂ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _)).neg
  have i24 : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖)
      ((posM (-⇑ψ)).prod (unitSphereProb d)) :=
    (hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₂ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₄ _ _ _ _)).neg
  rw [logCov_eq_logEnergy, logEnergy_eq_integral_logPotM i13, logEnergy_eq_integral_logPotM i14,
    logEnergy_eq_integral_logPotM i23, logEnergy_eq_integral_logPotM i24]
  have iG : Integrable (fun y => logPotM (posM ⇑ψ) y - logPotM (posM (-⇑ψ)) y) ν :=
    (integrable_logPotM_of_prod i13).sub (integrable_logPotM_of_prod i23)
  simp only [framePot_apply, framePotRaw]
  rw [integral_sub iG (integrable_const _),
    integral_sub (integrable_logPotM_of_prod i13) (integrable_logPotM_of_prod i23),
    integral_sub (integrable_logPotM_of_prod i14) (integrable_logPotM_of_prod i24),
    integral_const, probReal_univ, one_smul]
  ring

end Pot

end HigherDimLQGContinuity
