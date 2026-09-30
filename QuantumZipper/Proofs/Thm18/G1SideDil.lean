import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.LQG.GoodSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (4): an offset radius as a dyadic radius of a dilated family member

Let `x` be a field and `Z` a field (in the application: `x` the pulled-back canonical wedge
field `coordChange (rescale w Q s) ψ Q`, `Z = coordChange w (z ↦ s ψ(a z)) Q` a member of the
dilation family of `G1Side.ae_wedge_transport_family`). If, at every point `t` of the support of
a test function `f`, the regularized average of `x` on the offset circle `fc(t, a 2^{-k})` equals
the dyadic average of `Z` at `t/a` minus `Q log a`, then

  `∫ f d(bdryR γ x (a 2^{-k})) = ∫ f(a ·) d(bdryApprox γ Z k)`

(`integral_bdryR_offset_of_avg`). This is the coordinate-change rule for the dilation
`z ↦ a z` (Duplantier–Sheffield, *LQG and KPZ*, Invent. Math. 185 (2011), (5.1)/Prop. 2.1:
`γ Q / 2 = 1 + γ²/4`), exactly as in `SWCore.integral_bdryR_dilate` (SWCoreB8Dil.lean), but with
the identity of densities only on the support of `f`, and no regularity of `x` or `Z` assumed.
Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

/-- The density of `bdryApprox γ Z k` at `u`. -/
def apxDens (γ : ℝ) (Z : FieldSample) (k : ℕ) (u : ℝ) : ℝ :=
  radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg Z k (u : ℂ))

theorem measurable_apxDens (γ : ℝ) (Z : FieldSample) (k : ℕ) : Measurable (apxDens γ Z k) :=
  measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
    ((measurable_avgReg k).comp (measurable_const.prodMk Complex.measurable_ofReal))))

theorem apxDens_nonneg (γ : ℝ) (Z : FieldSample) (k : ℕ) (u : ℝ) : 0 ≤ apxDens γ Z k u :=
  mul_nonneg (Real.rpow_nonneg (radius_pos k).le _) (Real.exp_pos _).le

theorem integral_bdryApprox_eq_apxDens (γ : ℝ) (Z : FieldSample) (k : ℕ) (g : ℝ → ℝ) :
    ∫ u, g u ∂bdryApprox γ Z k = ∫ u, g u * apxDens γ Z k u := by
  show ∫ u, g u ∂volume.withDensity (fun t => ENNReal.ofReal (apxDens γ Z k t)) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (measurable_apxDens γ Z k).ennreal_ofReal.aemeasurable
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (apxDens_nonneg γ Z k u), mul_comm]

/-- The density identity at one point. -/
theorem bdryDens_eq_apxDens {γ : ℝ} (hγ : 0 < γ) {x Z : FieldSample} {a : ℝ} (ha : 0 < a)
    (k : ℕ) {t : ℝ}
    (hE : evalReg x (foldedCircle (t : ℂ) (a * radius k)) =
      avgReg Z k ((t / a : ℝ) : ℂ) - Qc γ * Real.log a) :
    bdryDens γ x (a * radius k) t = a⁻¹ * apxDens γ Z k (t / a) := by
  have hQ := GoodTransforms.gammaQ_bdry hγ
  have hr := radius_pos k
  unfold bdryDens apxDens
  rw [hE, Real.mul_rpow ha.le hr.le, Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hr,
    show a⁻¹ = Real.exp (-Real.log a) by rw [Real.exp_neg, Real.exp_log ha]]
  simp only [← Real.exp_add]
  congr 1
  linear_combination (-(Real.log a)) * hQ

/-- **Offset radius = dyadic radius of the dilated family member** (on the support of `f`). -/
theorem integral_bdryR_offset_of_avg {γ : ℝ} (hγ : 0 < γ) {x Z : FieldSample} {a : ℝ}
    (ha : 0 < a) (k : ℕ) {f : ℝ → ℝ}
    (hE : ∀ t ∈ tsupport f, evalReg x (foldedCircle (t : ℂ) (a * radius k)) =
      avgReg Z k ((t / a : ℝ) : ℂ) - Qc γ * Real.log a) :
    ∫ t, f t ∂bdryR γ x (a * radius k) = ∫ u, f (a * u) ∂bdryApprox γ Z k := by
  set T := tsupport f with hT
  have hTm : MeasurableSet T := (isClosed_tsupport f).measurableSet
  have hz : ∀ t, t ∉ T → f t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
  set D : ℝ → ℝ := fun t => a⁻¹ * apxDens γ Z k (t / a) with hD
  have hDm : Measurable D :=
    measurable_const.mul ((measurable_apxDens γ Z k).comp (measurable_id.div_const a))
  have hD0 : ∀ t, 0 ≤ D t := fun t => mul_nonneg (inv_nonneg.2 ha.le) (apxDens_nonneg _ _ _ _)
  -- the left side as an integral against `D`
  have hL : ∫ t, f t ∂bdryR γ x (a * radius k) = ∫ t, f t * D t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    unfold bdryR
    rw [restrict_withDensity hTm]
    have hc : (volume.restrict T).withDensity
        (fun t => ENNReal.ofReal (bdryDens γ x (a * radius k) t)) =
        (volume.restrict T).withDensity (fun t => ENNReal.ofReal (D t)) := by
      refine withDensity_congr_ae ?_
      filter_upwards [ae_restrict_mem hTm] with t ht
      rw [bdryDens_eq_apxDens hγ ha k (hE t ht)]
    rw [hc, integral_withDensity_eq_integral_toReal_smul₀
      hDm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have e : ∀ t, (ENNReal.ofReal (D t)).toReal • f t = f t * D t := fun t => by
      rw [ENNReal.toReal_ofReal (hD0 t), smul_eq_mul, mul_comm]
    simp_rw [e]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by rw [hz t ht, zero_mul]
  rw [hL, integral_bdryApprox_eq_apxDens]
  -- change of variables `t = a u`
  have hsub := Measure.integral_comp_mul_left (fun t => f t * D t) a
  rw [abs_inv, abs_of_pos ha, smul_eq_mul] at hsub
  have e2 : ∀ u, f (a * u) * D (a * u) = a⁻¹ * (f (a * u) * apxDens γ Z k u) := fun u => by
    simp only [hD, mul_div_cancel_left₀ u ha.ne']
    ring
  simp_rw [e2, integral_const_mul] at hsub
  have := congrArg (fun y => a * y) hsub
  rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul, one_mul] at this
  exact this.symm

end G1Side
end QuantumZipper
