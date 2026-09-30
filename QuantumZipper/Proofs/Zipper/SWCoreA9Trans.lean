import QuantumZipper.Proofs.Zipper.SWCoreA6Fam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A9 (1): offset transport — radii `α 2^{-k}`, uniformly in `α ∈ [1,2]`

Offset form of `area_transport_nonneg_fam` / `transport_signed_fam` (SWCoreA6Fam) for one map
`ψ` of a rational area class: the approximations of `x ∘ ψ + Q log|ψ'|` at the radius
`α 2^{-k}` (`areaR`, circle averages at arbitrary radius) converge to `∫ f∘ψ⁻¹ dμ^x`, uniformly
in `α ∈ [1,2]`, hence along `goodFilter` (`a9_tendsto_goodFilter`).

* The density factorizes exactly (`γ Q = 2 + γ²/2`) as
  `‖ψ'(z)‖² μ^x_{α 2^{-k}‖ψ'(z)‖}(ψ z) e^{γ err}` with the offset distortion error `pushErrR`
  (`areaDens_coordChange_eqR`, as `areaDensK_coordChange_eq`).
* The variable-scale window limit `unifWin` (SW Cor. 3.2 from the window measures of SW Thm 1.1,
  p. 9) is applied to the family indexed by `α ∈ [1,2]`, with scale `α ‖ψ'(ψ⁻¹ w)‖`: the
  offset only multiplies the scale by a constant in `[1,2]`, so equicontinuity of `log₂` of the
  scale is unchanged. Hence the offset window limits need no new probabilistic input.

Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7), pp. 11–13 (their radius `ε`
is continuous, so the offsets are part of their statement). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

variable {γ : ℝ} {x : FieldSample}

/-- The offset distortion error at `(z, r)`: circle average of `x ∘ ψ + Q log|ψ'|` at radius
`r`, minus `Q log|ψ'(z)|`, minus the round average of `x` at `(ψ z, r |ψ'(z)|)`. -/
def pushErrR (γ : ℝ) (x : FieldSample) (ψ : ℂ → ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  evalReg (coordChange x ψ (Qc γ)) (foldedCircle z r) - Qc γ * Real.log ‖deriv ψ z‖ -
    evalReg x (foldedCircle (ψ z) (r * ‖deriv ψ z‖))

/-- **Exact factorization of the pushed density at radius `r`.** -/
theorem areaDens_coordChange_eqR (hγ : 0 < γ) (x : FieldSample) (ψ : ℂ → ℂ) {r : ℝ}
    (hr : 0 < r) {z : ℂ} (hz : deriv ψ z ≠ 0) :
    areaDens γ (coordChange x ψ (Qc γ)) r z =
      ‖deriv ψ z‖ ^ 2 * areaDens γ x (r * ‖deriv ψ z‖) (ψ z) *
        Real.exp (γ * pushErrR γ x ψ r z) := by
  set a := ‖deriv ψ z‖ with ha_def
  have ha : 0 < a := norm_pos_iff.2 hz
  have hQ : γ * Qc γ = 2 + γ ^ 2 / 2 := by
    unfold Qc; field_simp
  have ha2 : a ^ 2 = Real.exp (2 * Real.log a) := by
    rw [show 2 * Real.log a = Real.log a + Real.log a by ring, Real.exp_add, Real.exp_log ha]
    ring
  have hra : (r * a) ^ (γ ^ 2 / 2) =
      r ^ (γ ^ 2 / 2) * Real.exp (Real.log a * (γ ^ 2 / 2)) := by
    rw [Real.mul_rpow hr.le ha.le, Real.rpow_def_of_pos ha]
  unfold areaDens pushErrR
  rw [← ha_def, ha2, hra]
  set A := evalReg (coordChange x ψ (Qc γ)) (foldedCircle z r)
  set E := evalReg x (foldedCircle (ψ z) (r * a))
  have hexp : Real.exp (2 * Real.log a) * Real.exp (Real.log a * (γ ^ 2 / 2)) *
      Real.exp (γ * E) * Real.exp (γ * (A - Qc γ * Real.log a - E)) = Real.exp (γ * A) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-Real.log a) * hQ
  rw [← hexp]
  ring

theorem a9_measurable_areaDens (γ : ℝ) (y : FieldSample) (r : ℝ) :
    Measurable (areaDens γ y r) := by
  have hin : Measurable fun z : ℂ => (y, (z, r)) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  have hE : Measurable fun z : ℂ => evalReg y (foldedCircle z r) := by
    have h := IndepParams.measurable_evalReg_fc₂.comp hin
    exact h
  have hexp : Measurable fun z : ℂ => Real.exp (γ * evalReg y (foldedCircle z r)) :=
    Real.measurable_exp.comp (hE.const_mul γ)
  have hpow : Measurable fun _ : ℂ => r ^ (γ ^ 2 / 2) := measurable_const
  exact hpow.mul hexp

/-- Integrals against `areaR` are integrals over `ℍ` against its density. -/
theorem a9_integral_areaR_eq (γ : ℝ) (y : FieldSample) {r : ℝ} (hr : 0 < r) (g : ℂ → ℝ) :
    ∫ z, g z ∂areaR γ y r = ∫ z in H, areaDens γ y r z * g z := by
  show ∫ z, g z ∂((volume.restrict H).withDensity fun z => ENNReal.ofReal (areaDens γ y r z)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (a9_measurable_areaDens γ y r).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (GoodSample.areaDens_nonneg γ y hr z)]

/-- **Change of variables** for the pushed density at radius `α 2^{-k}`. -/
theorem a9_lintegral_pushDens_eq {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass a b c d ρ M m) {f : ℂ → ℝ}
    (hfK : tsupport f ⊆ interior (rectC a b c d)) (α : ℝ) (k : ℕ) :
    ∫⁻ z in H, ENNReal.ofReal (f z) *
        ENNReal.ofReal (‖deriv ψ z‖ ^ 2 * areaDens γ x (α * radius k * ‖deriv ψ z‖) (ψ z)) =
      vsInt γ x (pullTest ψ (rectC a b c d) f) (fun w => α * pullScale ψ (rectC a b c d) w) k := by
  set K := rectC a b c d with hKdef
  have hKH : K ⊆ H := rectC_subset_H hc
  have hKm : MeasurableSet K := measurableSet_rectC a b c d
  have hfz : ∀ z, f z ≠ 0 → z ∈ K := fun z h =>
    interior_subset (hfK (subset_tsupport f h))
  have hsupp1 : (support fun z => ENNReal.ofReal (f z) *
      ENNReal.ofReal (‖deriv ψ z‖ ^ 2 * areaDens γ x (α * radius k * ‖deriv ψ z‖) (ψ z))) ⊆
        K := by
    intro z hz
    refine hfz z fun h => hz ?_
    simp [h]
  set G : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (pullTest ψ K f w) *
    ENNReal.ofReal (areaDens γ x (radius k * (α * pullScale ψ K w)) w) with hG
  have hsupp2 : support G ⊆ ψ '' K := by
    intro w hw
    by_contra h
    apply hw
    simp [hG, pullTest, h]
  calc _ = ∫⁻ z in K, ENNReal.ofReal (f z) *
        ENNReal.ofReal (‖deriv ψ z‖ ^ 2 * areaDens γ x (α * radius k * ‖deriv ψ z‖) (ψ z)) := by
        rw [setLIntegral_eq_of_support_subset (hsupp1.trans hKH),
          setLIntegral_eq_of_support_subset hsupp1]
    _ = ∫⁻ z in K, ENNReal.ofReal (‖deriv ψ z‖ ^ 2) * G (ψ z) := by
        refine setLIntegral_congr_fun hKm fun z hz => ?_
        have h1 : Function.invFunOn ψ K (ψ z) = z := swA5_invFunOn_image hρ hψ hz
        have h2 : pullTest ψ K f (ψ z) = f z := swA5_pullTest_image hρ hψ hz f
        have h3 : radius k * (α * pullScale ψ K (ψ z)) = α * radius k * ‖deriv ψ z‖ := by
          simp only [pullScale, h1]; ring
        simp only [hG, h2, h3]
        rw [ENNReal.ofReal_mul (sq_nonneg _)]
        ring
    _ = ∫⁻ w in ψ '' K, G w := lintegral_pull hρ hψ G
    _ = vsInt γ x (pullTest ψ K f) (fun w => α * pullScale ψ K w) k := by
        have hψK : ψ '' K ⊆ H := by
          rintro _ ⟨z, hz, rfl⟩
          exact lt_of_lt_of_le hρ (hψ.2.2.1 z (self_subset_thickening hρ _ hz)).2
        rw [vsInt, setLIntegral_eq_of_support_subset hsupp2,
          setLIntegral_eq_of_support_subset (hsupp2.trans hψK)]

end SWCore
end QuantumZipper
