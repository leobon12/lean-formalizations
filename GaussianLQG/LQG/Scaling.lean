import GaussianLQG.LQG.Scaling.LogMoments

/-!
# The scaling lemma (blueprint Lemma `lem:scaling`)

For every `S : Setup`:

* (a) `Setup.lintegral_abs_log_D_le`, `Setup.memLp_log_D`, `Setup.abs_b_le`
  (in `LQG/Scaling/LogMoments.lean`);
* (b) `Setup.map_log_D_sub`, `Setup.integral_log_D`, `Setup.exists_integral_log_D`
  (in `LQG/Scaling/LogMoments.lean`);
* (c) `Setup.holderScaling : S.HolderScaling`:
  `E[A_γ(B̄_R)^p] ≤ C R^{p(ξQ - 1/2) + p² ξ²}` for `R ≥ 1`, `γ ≤ γ*`;
* (d) `Setup.annulusScaling : S.AnnulusScaling`: `E[L_R^{-p}] ≤ C R^{-pξQ + p² ξ²}`.

Proof of (c), (d): apply (S4) with `z = 0`, `a = R`; the rescaled metric
`D̃(x, y) = R^{-ξQ} e^{-ξ h_R(0)} D(Rx, Ry)` has the law of `D`, and deterministically
`A_γ(B̄_R) ≤ R^{ξQ - 1/2} e^{ξ h_R(0)} Ã(B̄_1)` and `L_R⁻¹ ≤ R^{-ξQ} e^{-ξ h_R(0)} L̃_1⁻¹`. Since
`h_R(0)` need not be independent of `D̃`, use Cauchy–Schwarz, the Gaussian moment
`E e^{t h_R(0)} = R^{t²/2}` (`Var h_R(0) = ℰ(σ_{0,R}, σ_{0,R}) = log R`), and (S6) at order `2p`
for `K = B̄_1` (resp. `L_1 ≥ I(B̄_2, 1)` and `K = B̄_2`), `δ = 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace GaussianLQG

/-- Cauchy–Schwarz for lower Lebesgue integrals. -/
theorem lintegral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a * g a ∂μ ≤
      (∫⁻ a, f a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
  ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg

namespace Setup

variable (S : Setup)

theorem rescaleFactor_ofReal (γ : ℝ) {R : ℝ} (hR : 0 < R) (ω : Coord) :
    S.rescaleFactor γ 0 (R : ℂ) ω = R ^ (-(S.ξ γ * LQGMetric.Q γ)) *
      Real.exp (-(S.ξ γ) * pairing S.e (circleMeasure 0 R) ω) := by
  unfold rescaleFactor
  rw [Complex.norm_of_nonneg hR.le]

/-- `E[R^α e^{t h_R(0)}] = R^{α + t²/2}` for `R ≥ 1`. -/
theorem lintegral_ofReal_rpow_mul_exp {R : ℝ} (hR : 1 ≤ R) (α t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (R ^ α * Real.exp (t * pairing S.e (circleMeasure 0 R) ω)) ∂stdP =
      ENNReal.ofReal (R ^ (α + t ^ 2 / 2)) := by
  have hR0 : 0 < R := by linarith
  have hint := integrable_exp_mul_pairing_circleMeasure S.frame 0 hR0 t
  have hm : Measurable fun ω => ENNReal.ofReal (Real.exp (t * pairing S.e (circleMeasure 0 R) ω)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_pairing _ _).const_mul t))
  simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR0.le α)]
  rw [lintegral_const_mul _ hm, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun _ => (Real.exp_pos _).le),
    integral_exp_mul_pairing_circleMeasure_zero S.frame hR t,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hR0.le _), ← Real.rpow_add hR0]

/-! ## (c) Hölder constants of large balls -/

/-- The pointwise bound `A_γ(B̄_R) ≤ R^{ξQ - 1/2} e^{ξ h_R(0)} Ã(B̄_1)`. -/
theorem holderConst_closedBall_le_rescaled (γ : ℝ) {R : ℝ} (hR : 0 < R) (ω : Coord) :
    holderConst (S.D γ ω).1 (closedBall 0 R) ≤
      ENNReal.ofReal (R ^ (S.ξ γ * LQGMetric.Q γ - 1 / 2) *
        Real.exp (S.ξ γ * pairing S.e (circleMeasure 0 R) ω)) *
        holderConst (S.rescaled γ 0 (R : ℂ) ω) (closedBall 0 1) := by
  have hc := S.rescaleFactor_pos γ 0 (a := (R : ℂ)) (Complex.ofReal_ne_zero.2 hR.ne') ω
  have h := holderConst_closedBall_le_of_rescale (d := (S.D γ ω).1)
    (d' := S.rescaled γ 0 (R : ℂ) ω) hR hc fun u v => by rw [rescaled_apply, zero_add, zero_add]
  have hfac : (S.rescaleFactor γ 0 (R : ℂ) ω)⁻¹ * (R ^ (1 / 2 : ℝ))⁻¹ =
      R ^ (S.ξ γ * LQGMetric.Q γ - 1 / 2) *
        Real.exp (S.ξ γ * pairing S.e (circleMeasure 0 R) ω) := by
    rw [rescaleFactor_ofReal S γ hR, mul_inv, Real.rpow_neg hR.le, inv_inv, neg_mul, Real.exp_neg,
      inv_inv, Real.rpow_sub hR, div_eq_mul_inv]
    ring
  rwa [hfac] at h

/-- **Lemma `lem:scaling`(c)**: `E[A_γ(B̄_R)^p] ≤ C R^{p(ξQ - 1/2) + p² ξ²}`. -/
theorem holderScaling : S.HolderScaling := by
  intro p hp
  obtain ⟨γp, hγp, hS6⟩ := S.S6 (2 * p) (by linarith)
  obtain ⟨C, hCtop, hC⟩ := hS6 (closedBall 0 1) (isCompact_closedBall 0 1) 1 one_pos
  refine ⟨min γp 1, C.toReal ^ (1 / 2 : ℝ), lt_min hγp one_pos, fun γ hγ R hR => ?_⟩
  have hγ0 : 0 < γ := hγ.1
  have hγ2 : γ < 2 := lt_of_le_of_lt (hγ.2.trans (min_le_right _ _)) one_lt_two
  have hCγ := (hC γ ⟨hγ0, hγ.2.trans (min_le_left _ _)⟩).1
  have hR0 : 0 < R := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0.ne'
  set ξ := S.ξ γ with hξ
  set Q := LQGMetric.Q γ with hQ
  set h : Coord → ℝ := pairing S.e (circleMeasure 0 R) with hh
  set k : Coord → ℝ := fun ω => R ^ (ξ * Q - 1 / 2) * Real.exp (ξ * h ω) with hk
  set A : Coord → ℝ≥0∞ := fun ω => holderConst (S.rescaled γ 0 (R : ℂ) ω) (closedBall 0 1)
    with hA
  have hkpos : ∀ ω, 0 < k ω := fun ω => mul_pos (Real.rpow_pos_of_pos hR0 _) (Real.exp_pos _)
  have hmk : Measurable k :=
    measurable_const.mul (Real.measurable_exp.comp ((measurable_pairing _ _).const_mul _))
  have hmA : Measurable A := (measurable_holderConst_cont _).comp (S.measurable_rescaled γ 0 _)
  have hfirst : (∫⁻ ω, (ENNReal.ofReal (k ω) ^ p) ^ (2 : ℝ) ∂stdP) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (R ^ (p * (ξ * Q - 1 / 2) + p ^ 2 * ξ ^ 2)) := by
    have hpt : ∀ ω, (ENNReal.ofReal (k ω) ^ p) ^ (2 : ℝ) =
        ENNReal.ofReal (R ^ (2 * p * (ξ * Q - 1 / 2)) * Real.exp ((2 * p * ξ) * h ω)) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (hkpos ω).le hp0,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hkpos ω).le _) (by norm_num),
        ← Real.rpow_mul (hkpos ω).le]
      congr 1
      simp only [hk]
      rw [Real.mul_rpow (Real.rpow_nonneg hR0.le _) (Real.exp_pos _).le, ← Real.rpow_mul hR0.le,
        ← Real.exp_mul]
      congr 2 <;> ring
    simp_rw [hpt]
    rw [S.lintegral_ofReal_rpow_mul_exp hR,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hR0.le _) (by norm_num),
      ← Real.rpow_mul hR0.le]
    congr 2
    ring
  have hsecond : ∫⁻ ω, (A ω ^ p) ^ (2 : ℝ) ∂stdP =
      ∫⁻ ω, holderConst (S.D γ ω).1 (closedBall 0 1) ^ (2 * p) ∂stdP := by
    have hpt : ∀ ω, (A ω ^ p) ^ (2 : ℝ) = A ω ^ (2 * p) := fun ω => by
      rw [← ENNReal.rpow_mul, mul_comm]
    simp_rw [hpt]
    exact S.lintegral_comp_rescaled hγ0 hγ2 0 hRne ((measurable_holderConst_cont _).pow_const _)
  calc ∫⁻ ω, holderConst (S.D γ ω).1 (closedBall 0 R) ^ p ∂stdP
      ≤ ∫⁻ ω, ENNReal.ofReal (k ω) ^ p * A ω ^ p ∂stdP := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0]
        exact ENNReal.rpow_le_rpow (S.holderConst_closedBall_le_rescaled γ hR0 ω) hp0
    _ ≤ (∫⁻ ω, (ENNReal.ofReal (k ω) ^ p) ^ (2 : ℝ) ∂stdP) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, (A ω ^ p) ^ (2 : ℝ) ∂stdP) ^ (1 / 2 : ℝ) :=
        lintegral_mul_le_sqrt_mul_sqrt stdP
          ((ENNReal.measurable_ofReal.comp hmk).pow_const p).aemeasurable
          (hmA.pow_const p).aemeasurable
    _ ≤ ENNReal.ofReal (R ^ (p * (ξ * Q - 1 / 2) + p ^ 2 * ξ ^ 2)) * C ^ (1 / 2 : ℝ) := by
        rw [hfirst, hsecond]
        gcongr
    _ = ENNReal.ofReal (C.toReal ^ (1 / 2 : ℝ) * R ^ (p * (ξ * Q - 1 / 2) + p ^ 2 * ξ ^ 2)) := by
        rw [mul_comm, ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
          ENNReal.ofReal_toReal hCtop]

/-! ## (d) Annulus crossings -/

/-- The pointwise bound `L_R⁻¹ ≤ R^{-ξQ} e^{-ξ h_R(0)} L̃_1⁻¹`. -/
theorem annulusCross_inv_le_rescaled (γ : ℝ) {R : ℝ} (hR : 0 < R) (ω : Coord) :
    (annulusCross (S.D γ ω).1 R)⁻¹ ≤
      ENNReal.ofReal (R ^ (-(S.ξ γ * LQGMetric.Q γ)) *
        Real.exp (-(S.ξ γ) * pairing S.e (circleMeasure 0 R) ω)) *
        (annulusCross (S.rescaled γ 0 (R : ℂ) ω) 1)⁻¹ := by
  have hc := S.rescaleFactor_pos γ 0 (a := (R : ℂ)) (Complex.ofReal_ne_zero.2 hR.ne') ω
  have h := annulusCross_inv_le_of_rescale (d := (S.D γ ω).1)
    (d' := S.rescaled γ 0 (R : ℂ) ω) hR hc fun u v => by rw [rescaled_apply, zero_add, zero_add]
  rwa [rescaleFactor_ofReal S γ hR] at h

/-- **Lemma `lem:scaling`(d)**: `E[L_R^{-p}] ≤ C R^{-pξQ + p² ξ²}`. -/
theorem annulusScaling : S.AnnulusScaling := by
  intro p hp
  obtain ⟨γp, hγp, hS6⟩ := S.S6 (2 * p) (by linarith)
  obtain ⟨C, hCtop, hC⟩ := hS6 (closedBall 0 2) (isCompact_closedBall 0 2) 1 one_pos
  refine ⟨min γp 1, C.toReal ^ (1 / 2 : ℝ), lt_min hγp one_pos, fun γ hγ R hR => ?_⟩
  have hγ0 : 0 < γ := hγ.1
  have hγ2 : γ < 2 := lt_of_le_of_lt (hγ.2.trans (min_le_right _ _)) one_lt_two
  have hCγ := (hC γ ⟨hγ0, hγ.2.trans (min_le_left _ _)⟩).2
  have hR0 : 0 < R := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0.ne'
  set ξ := S.ξ γ with hξ
  set Q := LQGMetric.Q γ with hQ
  set h : Coord → ℝ := pairing S.e (circleMeasure 0 R) with hh
  set c : Coord → ℝ := fun ω => R ^ (-(ξ * Q)) * Real.exp (-ξ * h ω) with hc
  set L : Coord → ℝ≥0∞ := fun ω => (annulusCross (S.rescaled γ 0 (R : ℂ) ω) 1)⁻¹ with hL
  have hcpos : ∀ ω, 0 < c ω := fun ω => mul_pos (Real.rpow_pos_of_pos hR0 _) (Real.exp_pos _)
  have hmc : Measurable c :=
    measurable_const.mul (Real.measurable_exp.comp ((measurable_pairing _ _).const_mul _))
  have hmL : Measurable L :=
    ((measurable_annulusCross_cont 1).comp (S.measurable_rescaled γ 0 _)).inv
  have hfirst : (∫⁻ ω, (ENNReal.ofReal (c ω) ^ p) ^ (2 : ℝ) ∂stdP) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (R ^ (-(p * (ξ * Q)) + p ^ 2 * ξ ^ 2)) := by
    have hpt : ∀ ω, (ENNReal.ofReal (c ω) ^ p) ^ (2 : ℝ) =
        ENNReal.ofReal (R ^ (2 * p * (-(ξ * Q))) * Real.exp ((2 * p * (-ξ)) * h ω)) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (hcpos ω).le hp0,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hcpos ω).le _) (by norm_num),
        ← Real.rpow_mul (hcpos ω).le]
      congr 1
      simp only [hc]
      rw [Real.mul_rpow (Real.rpow_nonneg hR0.le _) (Real.exp_pos _).le, ← Real.rpow_mul hR0.le,
        ← Real.exp_mul]
      congr 2 <;> ring
    simp_rw [hpt]
    rw [S.lintegral_ofReal_rpow_mul_exp hR,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hR0.le _) (by norm_num),
      ← Real.rpow_mul hR0.le]
    congr 2
    ring
  have hsecond : ∫⁻ ω, (L ω ^ p) ^ (2 : ℝ) ∂stdP ≤ C := by
    have hpt : ∀ ω, (L ω ^ p) ^ (2 : ℝ) = L ω ^ (2 * p) := fun ω => by
      rw [← ENNReal.rpow_mul, mul_comm]
    simp_rw [hpt]
    have hF : Measurable fun d : C(ℂ × ℂ, ℝ) => (annulusCross d 1)⁻¹ ^ (2 * p) :=
      ((measurable_annulusCross_cont 1).inv).pow_const (2 * p)
    calc ∫⁻ ω, L ω ^ (2 * p) ∂stdP
        = ∫⁻ ω, (annulusCross (S.D γ ω).1 1)⁻¹ ^ (2 * p) ∂stdP :=
          S.lintegral_comp_rescaled hγ0 hγ2 0 hRne hF
      _ ≤ ∫⁻ ω, (sepInf (S.D γ ω).1 (closedBall 0 2) 1)⁻¹ ^ (2 * p) ∂stdP :=
          lintegral_mono fun ω => ENNReal.rpow_le_rpow
            (ENNReal.inv_le_inv.2 (sepInf_le_annulusCross_one _)) (by linarith)
      _ ≤ C := hCγ
  calc ∫⁻ ω, (annulusCross (S.D γ ω).1 R)⁻¹ ^ p ∂stdP
      ≤ ∫⁻ ω, ENNReal.ofReal (c ω) ^ p * L ω ^ p ∂stdP := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0]
        exact ENNReal.rpow_le_rpow (S.annulusCross_inv_le_rescaled γ hR0 ω) hp0
    _ ≤ (∫⁻ ω, (ENNReal.ofReal (c ω) ^ p) ^ (2 : ℝ) ∂stdP) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, (L ω ^ p) ^ (2 : ℝ) ∂stdP) ^ (1 / 2 : ℝ) :=
        lintegral_mul_le_sqrt_mul_sqrt stdP
          ((ENNReal.measurable_ofReal.comp hmc).pow_const p).aemeasurable
          (hmL.pow_const p).aemeasurable
    _ ≤ ENNReal.ofReal (R ^ (-(p * (ξ * Q)) + p ^ 2 * ξ ^ 2)) * C ^ (1 / 2 : ℝ) := by
        rw [hfirst]
        gcongr
    _ = ENNReal.ofReal (C.toReal ^ (1 / 2 : ℝ) * R ^ (-(p * (ξ * Q)) + p ^ 2 * ξ ^ 2)) := by
        rw [mul_comm, ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
          ENNReal.ofReal_toReal hCtop]

end Setup

end GaussianLQG
