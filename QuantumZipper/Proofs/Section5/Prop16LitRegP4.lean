import QuantumZipper.Proofs.Section5.Prop16LitRegP3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: local regularity of chart zooms, assembly (D98)

`Prop16Lit.localAreaRegular_zoomLit`: under `ChartY` for the free sample `y`, the chart zoom
`zoomFieldLit γ C h t ψ` of a field whose translate agrees near `ψ(U)` with `y + g` is
`LocalAreaRegular` on `U`, with limit `e^{γ (g∘ψ + C/γ)} (ν|_U)` (`ν` the area limit of
`y ∘ ψ + Q log|ψ'|`, the pullback of `μ_y` by DS11 Prop. 2.1). The convergence at all small
radii is the exponential tilt `GoodSample.tendsto_integral_exp_mul` along `𝓝[>] 0` of the
offset-uniform limit `ChartY.lim`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric Real
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open CoordChangeArea GoodSample SWCore

/-- Finite area approximation at radius `r` on a compact where the circle values are continuous. -/
theorem areaR_lt_top_of_continuousOn {γ : ℝ} {Z : FieldSample} {r : ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hc : ContinuousOn (fun z => evalReg Z (foldedCircle z r)) K) :
    areaR γ Z r K < ∞ :=
  withDensity_lt_top hK ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)
    (continuousOn_const.mul ((continuousOn_const.mul hc).rexp))

/-- The regularized circle values of `y ∘ ψ + Q log|ψ'|` at small circles. -/
theorem evalReg_coordChange_y {γ : ℝ} {ψ : ℂ → ℂ} {y : FieldSample} {ν : Measure ℂ}
    (hy : ChartY γ ψ y ν) (hψd : DifferentiableOn ℂ ψ H) (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ → ContinuousOn
      (fun w => evalReg (coordChange y ψ (Qc γ)) (foldedCircle w ρ)) K ∧
      ∀ w ∈ K, evalReg (coordChange y ψ (Qc γ)) (foldedCircle w ρ) =
        coordChange y ψ (Qc γ) (foldedCircle w ρ) := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun ρ _ _ => ⟨by rw [he]; exact continuousOn_empty _,
      fun w hw => by rw [he] at hw; exact absurd hw (notMem_empty w)⟩⟩
  obtain ⟨ε₀, hε₀, hε₀H⟩ := hK.exists_cthickening_subset_open isOpen_H hKH
  obtain ⟨ρ₁, hρ₁, hrc⟩ := hy.rc K hK hKH
  obtain ⟨ρC, hρC, hC⟩ := hy.cont K hK hKH
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hm0 : 0 < z₀.im := hKH hz₀
  have hlog : ContinuousOn (fun u => Real.log ‖deriv ψ u‖) H := fun u hu => by
    have hA : AnalyticOnNhd ℂ ψ H := hψd.analyticOnNhd isOpen_H
    exact ((hA.deriv u hu).continuousAt.norm.log (norm_ne_zero_iff.2 (hψ0 u hu))).continuousWithinAt
  refine ⟨min (min ρ₁ ρC) (min ε₀ z₀.im), by positivity, fun ρ hρ hρ₀ => ?_⟩
  have h1 : ρ < ρ₁ := lt_of_lt_of_le hρ₀ ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ρ < ρC := lt_of_lt_of_le hρ₀ ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ρ < ε₀ := lt_of_lt_of_le hρ₀ ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : ρ < z₀.im := lt_of_lt_of_le hρ₀ ((min_le_right _ _).trans (min_le_right _ _))
  have heq : ∀ w ∈ K, evalReg (coordChange y ψ (Qc γ)) (foldedCircle w ρ) =
      coordChange y ψ (Qc γ) (foldedCircle w ρ) := fun w hw => by
    unfold evalReg; exact (hrc w hw ρ hρ h1).limUnder_eq
  have hform : ∀ w ∈ K, coordChange y ψ (Qc γ) (foldedCircle w ρ) =
      evalReg y ((foldedCircle w ρ).map ψ) + Qc γ * Real.log ‖deriv ψ w‖ := fun w hw => by
    have hB : closedBall w ρ ⊆ H :=
      (closedBall_subset_cthickening hw _).trans ((cthickening_mono h3.le K).trans hε₀H)
    show evalReg y ((foldedCircle w ρ).map ψ) + Qc γ * ∫ u, Real.log ‖deriv ψ u‖ ∂foldedCircle w ρ = _
    rw [swcNA2_integral_log_deriv_fc isOpen_H hψd hψ0 hρ (h4.le.trans (hmin hw)) hB]
  refine ⟨((hC ρ hρ h2).add ((continuousOn_const (c := Qc γ)).mul (hlog.mono hKH))).congr
    fun w hw => by rw [heq w hw, hform w hw]; rfl, heq⟩

end Prop16Lit
end QuantumZipper
