import GaussianLQG.LQG.Scaling.Affine

/-!
# Moments and the law of `log D(z, w)` (blueprint Lemma `lem:scaling`(a),(b))

* (a) `Setup.lintegral_abs_log_D_le`: for `p ≥ 1` there are `γ* > 0` and `C` with
  `E|log D^γ(0,1)|^p ≤ C` for `γ ∈ (0, γ*]`, from (S6) through `I(B̄_1, 1) ≤ D(0,1) ≤ A(B̄_1)`
  and `|log x| ≤ x + x⁻¹`. Consequences: `memLp_log_D`, `integrable_log_D`, `abs_b_le`.
* (b) `Setup.map_log_D_sub`: for `z ≠ w` and `r = |w - z|`, the law of
  `log D(z,w) - ξQ log r - ξ h_r(z)` is the law of `log D(0,1)` (from (S4) with `a = w - z`);
  hence `E log D(z,w) = b_γ + ξQ log r` (`integral_log_D`, `exists_integral_log_D`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace GaussianLQG

theorem abs_log_le_add_inv {x : ℝ} (hx : 0 < x) : |Real.log x| ≤ x + x⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos hx
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
  rw [Real.log_inv] at h2
  have h3 : 0 < x⁻¹ := inv_pos.2 hx
  rw [abs_le]
  constructor <;> linarith

namespace Setup

variable (S : Setup)

/-! ## (a) Moments of `log D(0, 1)` -/

/-- `|log D(0,1)| ≤ A(B̄_1) + I(B̄_1, 1)⁻¹`. -/
theorem ofReal_abs_log_D_le (γ : ℝ) (ω : Coord) :
    ENNReal.ofReal |Real.log ((S.D γ ω).1 (0, 1))| ≤
      holderConst (S.D γ ω).1 (closedBall 0 1) + (sepInf (S.D γ ω).1 (closedBall 0 1) 1)⁻¹ := by
  set x := (S.D γ ω).1 (0, 1)
  have hx : 0 < x := contMetric_pos (S.D γ ω) zero_ne_one
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_self zero_le_one
  have h1 : (1 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp
  have hn : ‖(0 : ℂ) - 1‖ = 1 := by simp
  refine (ENNReal.ofReal_le_ofReal (abs_log_le_add_inv hx)).trans ?_
  rw [ENNReal.ofReal_add hx.le (inv_nonneg.2 hx.le)]
  gcongr
  · have h := ofReal_div_le_holderConst (S.D γ ω).1 h0 h1 zero_ne_one
    rwa [hn, Real.one_rpow, div_one] at h
  · rw [ENNReal.ofReal_inv_of_pos hx]
    exact ENNReal.inv_le_inv.2 (sepInf_le_ofReal _ h0 h1 hn.ge)

/-- **Lemma `lem:scaling`(a)**: for `p ≥ 1` there are `γ* > 0` and `C` such that
`E|log D^γ(0,1)|^p ≤ C` for all `γ ∈ (0, γ*]`. -/
theorem lintegral_abs_log_D_le :
    ∀ p : ℝ, 1 ≤ p → ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
      ∫⁻ ω, ENNReal.ofReal |Real.log ((S.D γ ω).1 (0, 1))| ^ p ∂stdP ≤ ENNReal.ofReal C := by
  intro p hp
  obtain ⟨γp, hγp, hS6⟩ := S.S6 p hp
  obtain ⟨C, hCtop, hC⟩ := hS6 (closedBall 0 1) (isCompact_closedBall 0 1) 1 one_pos
  refine ⟨γp, 2 ^ p * C.toReal, hγp, fun γ hγ => ?_⟩
  obtain ⟨hA, hI⟩ := hC γ hγ
  have hp0 : 0 ≤ p := by linarith
  have hmA : Measurable fun ω => holderConst (S.D γ ω).1 (closedBall 0 1) :=
    (measurable_holderConst_cont _).comp (S.measurable_coe_D γ)
  have hmI : Measurable fun ω => (sepInf (S.D γ ω).1 (closedBall 0 1) 1)⁻¹ :=
    ((measurable_sepInf_cont _ _).comp (S.measurable_coe_D γ)).inv
  calc ∫⁻ ω, ENNReal.ofReal |Real.log ((S.D γ ω).1 (0, 1))| ^ p ∂stdP
      ≤ ∫⁻ ω, 2 ^ (p - 1) * (holderConst (S.D γ ω).1 (closedBall 0 1) ^ p +
          (sepInf (S.D γ ω).1 (closedBall 0 1) 1)⁻¹ ^ p) ∂stdP := by
        refine lintegral_mono fun ω => ?_
        exact (ENNReal.rpow_le_rpow (S.ofReal_abs_log_D_le γ ω) hp0).trans
          (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp)
    _ = 2 ^ (p - 1) * (∫⁻ ω, holderConst (S.D γ ω).1 (closedBall 0 1) ^ p ∂stdP +
          ∫⁻ ω, (sepInf (S.D γ ω).1 (closedBall 0 1) 1)⁻¹ ^ p ∂stdP) := by
        have hmsum : Measurable fun ω => holderConst (S.D γ ω).1 (closedBall 0 1) ^ p +
            (sepInf (S.D γ ω).1 (closedBall 0 1) 1)⁻¹ ^ p := (hmA.pow_const p).add (hmI.pow_const p)
        rw [lintegral_const_mul _ hmsum, lintegral_add_left (hmA.pow_const p)]
    _ ≤ 2 ^ (p - 1) * (C + C) := by gcongr
    _ = ENNReal.ofReal (2 ^ p * C.toReal) := by
        have h2 : (2 : ℝ≥0∞) ^ p = 2 ^ (p - 1) * 2 := by
          conv_lhs => rw [show p = (p - 1) + 1 by ring]
          rw [ENNReal.rpow_add _ _ (by norm_num) (by norm_num), ENNReal.rpow_one]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hCtop,
          ← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat, h2]
        ring

/-- **Lemma `lem:scaling`(a)**, `L^p` form. -/
theorem memLp_log_D :
    ∀ p : ℝ, 1 ≤ p → ∃ γs : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
      MemLp (fun ω => Real.log ((S.D γ ω).1 (0, 1))) (ENNReal.ofReal p) stdP := by
  intro p hp
  obtain ⟨γs, C, hγs, hC⟩ := S.lintegral_abs_log_D_le p hp
  refine ⟨γs, hγs, fun γ hγ => ⟨(S.measurable_log_D γ 0 1).aestronglyMeasurable, ?_⟩⟩
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 (by linarith)).ne'
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by linarith)]
  simp_rw [Real.enorm_eq_ofReal_abs]
  exact (hC γ hγ).trans_lt ENNReal.ofReal_lt_top

/-- `log D(0,1)` is integrable for small `γ`. -/
theorem integrable_log_D :
    ∃ γs : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
      Integrable (fun ω => Real.log ((S.D γ ω).1 (0, 1))) stdP := by
  obtain ⟨γs, hγs, h⟩ := S.memLp_log_D 1 le_rfl
  refine ⟨γs, hγs, fun γ hγ => ?_⟩
  have := h γ hγ
  rw [ENNReal.ofReal_one] at this
  exact memLp_one_iff_integrable.1 this

/-- **Lemma `lem:scaling`(a)**: `b_γ` is bounded for small `γ`. -/
theorem abs_b_le : ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, |S.b γ| ≤ C := by
  obtain ⟨γs, C, hγs, hC⟩ := S.lintegral_abs_log_D_le 1 le_rfl
  refine ⟨γs, max C 0, hγs, fun γ hγ => ?_⟩
  have h := hC γ hγ
  simp only [ENNReal.rpow_one] at h
  calc |S.b γ| ≤ ∫ ω, |Real.log ((S.D γ ω).1 (0, 1))| ∂stdP := abs_integral_le_integral_abs
    _ = (∫⁻ ω, ENNReal.ofReal |Real.log ((S.D γ ω).1 (0, 1))| ∂stdP).toReal :=
        integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => abs_nonneg _)
          (continuous_abs.measurable.comp (S.measurable_log_D γ 0 1)).aestronglyMeasurable
    _ ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = max C 0 := ENNReal.toReal_ofReal'

/-! ## (b) The law of `log D(z, w)` -/

theorem log_rescaled_apply (γ : ℝ) (z : ℂ) {a : ℂ} (ha : a ≠ 0) (ω : Coord) :
    Real.log (S.rescaled γ z a ω (0, 1)) =
      Real.log ((S.D γ ω).1 (z, z + a)) - S.ξ γ * LQGMetric.Q γ * Real.log ‖a‖ -
        S.ξ γ * pairing S.e (circleMeasure z ‖a‖) ω := by
  rw [rescaled_apply, mul_zero, add_zero, mul_one, rescaleFactor]
  have hD : 0 < (S.D γ ω).1 (z, z + a) :=
    contMetric_pos (S.D γ ω) fun h => ha (by simpa using h.symm)
  rw [Real.log_mul (mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 ha) _)
    (Real.exp_pos _)).ne' hD.ne', Real.log_mul (Real.rpow_pos_of_pos (norm_pos_iff.2 ha) _).ne'
    (Real.exp_pos _).ne', Real.log_rpow (norm_pos_iff.2 ha), Real.log_exp]
  ring

/-- **Lemma `lem:scaling`(b)**: for `z ≠ w` and `r = |w - z|`, the law of
`log D(z,w) - ξQ log r - ξ h_r(z)` is the law of `log D(0,1)`. -/
theorem map_log_D_sub {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {z w : ℂ} (hzw : z ≠ w) :
    stdP.map (fun ω => Real.log ((S.D γ ω).1 (z, w)) -
        S.ξ γ * LQGMetric.Q γ * Real.log ‖w - z‖ -
          S.ξ γ * pairing S.e (circleMeasure z ‖w - z‖) ω) =
      stdP.map fun ω => Real.log ((S.D γ ω).1 (0, 1)) := by
  have ha : w - z ≠ 0 := sub_ne_zero.2 hzw.symm
  have hF : Measurable fun d : C(ℂ × ℂ, ℝ) => Real.log (d (0, 1)) :=
    Real.measurable_log.comp (ContinuousMap.measurable_eval _)
  have h := S.map_comp_rescaled hγ hγ2 z ha hF
  have e : (fun ω => Real.log (S.rescaled γ z (w - z) ω (0, 1))) =
      fun ω => Real.log ((S.D γ ω).1 (z, w)) - S.ξ γ * LQGMetric.Q γ * Real.log ‖w - z‖ -
        S.ξ γ * pairing S.e (circleMeasure z ‖w - z‖) ω := by
    funext ω
    rw [S.log_rescaled_apply γ z ha ω, add_sub_cancel]
  rw [e] at h
  exact h

/-- **Lemma `lem:scaling`(b)**: `E log D(z,w) = b_γ + ξQ log|w - z|`, provided `log D(0,1)` is
integrable (which holds for small `γ`, `integrable_log_D`). -/
theorem integral_log_D {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hint : Integrable (fun ω => Real.log ((S.D γ ω).1 (0, 1))) stdP) {z w : ℂ} (hzw : z ≠ w) :
    ∫ ω, Real.log ((S.D γ ω).1 (z, w)) ∂stdP =
      S.b γ + S.ξ γ * LQGMetric.Q γ * Real.log ‖w - z‖ := by
  have hr : 0 < ‖w - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hzw.symm)
  set X : Coord → ℝ := fun ω => Real.log ((S.D γ ω).1 (z, w)) -
    S.ξ γ * LQGMetric.Q γ * Real.log ‖w - z‖ - S.ξ γ * pairing S.e (circleMeasure z ‖w - z‖) ω
  have hXm : Measurable X :=
    ((S.measurable_log_D γ z w).sub_const _).sub ((measurable_pairing _ _).const_mul _)
  have hYm := S.measurable_log_D γ 0 1
  have hmap := S.map_log_D_sub hγ hγ2 hzw
  have hXint : Integrable X stdP := by
    have h1 : Integrable id (stdP.map fun ω => Real.log ((S.D γ ω).1 (0, 1))) :=
      (integrable_map_measure aestronglyMeasurable_id hYm.aemeasurable).2 hint
    rw [← hmap] at h1
    exact (integrable_map_measure aestronglyMeasurable_id hXm.aemeasurable).1 h1
  have hXint' : ∫ ω, X ω ∂stdP = S.b γ := by
    have h1 := integral_map (μ := stdP) hXm.aemeasurable (aestronglyMeasurable_id (α := ℝ))
    rw [hmap, integral_map hYm.aemeasurable aestronglyMeasurable_id] at h1
    exact h1.symm
  have hh : Integrable (pairing S.e (circleMeasure z ‖w - z‖)) stdP :=
    integrable_of_hasLaw_gaussianReal (hasLaw_pairing_circleMeasure S.frame z hr)
  have hh0 := integral_pairing S.frame (isRegular_circleMeasure z hr)
  have e : (fun ω => Real.log ((S.D γ ω).1 (z, w))) = fun ω =>
      X ω + S.ξ γ * LQGMetric.Q γ * Real.log ‖w - z‖ +
        S.ξ γ * pairing S.e (circleMeasure z ‖w - z‖) ω := by
    funext ω
    simp only [X]
    ring
  have h1 : Integrable (fun ω => X ω + S.ξ γ * LQGMetric.Q γ * Real.log ‖w - z‖) stdP :=
    hXint.add (integrable_const _)
  have h2 : Integrable (fun ω => S.ξ γ * pairing S.e (circleMeasure z ‖w - z‖) ω) stdP :=
    hh.const_mul _
  rw [e, integral_add h1 h2, integral_add hXint (integrable_const _), integral_const,
    probReal_univ, one_smul, integral_const_mul, hh0, hXint', mul_zero, add_zero]

/-- **Lemma `lem:scaling`(b)** for small `γ`: `E log D(z,w) = b_γ + ξQ log|w - z|`. -/
theorem exists_integral_log_D :
    ∃ γs : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ z w : ℂ, z ≠ w →
      ∫ ω, Real.log ((S.D γ ω).1 (z, w)) ∂stdP =
        S.b γ + S.ξ γ * LQGMetric.Q γ * Real.log ‖w - z‖ := by
  obtain ⟨γs, hγs, h⟩ := S.integrable_log_D
  refine ⟨min γs 1, lt_min hγs one_pos, fun γ hγ z w hzw => ?_⟩
  exact S.integral_log_D hγ.1 (lt_of_le_of_lt (hγ.2.trans (min_le_right _ _)) one_lt_two)
    (h γ ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩) hzw

end Setup

end GaussianLQG
