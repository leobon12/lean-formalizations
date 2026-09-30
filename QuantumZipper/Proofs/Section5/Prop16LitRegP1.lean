import QuantumZipper.Proofs.LQG.CoordChangeAreaRC3T
import QuantumZipper.Proofs.Section5.Prop16LitDilDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: circle averages of chart zooms of locally free fields (D98)

`Prop16Lit.tendsto_coordChange_fc_local`: if `x` agrees near `ψ(U)` with a regular sample `y` plus
a continuous `φ`, and the dyadic smoothings of `y ∘ ψ + Q log|ψ'|` converge at an interior circle,
then those of `x ∘ ψ + Q log|ψ'|` converge there, to the raw value of `y ∘ ψ + Q log|ψ'|` plus
the circle average of `φ ∘ ψ`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open CoordChangeArea GoodSample

theorem tendsto_coordChange_fc_local {x y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : MapsTo ψ H H) (hpush : PushRegular y ψ) {W : Set ℂ}
    (hWo : IsOpen W)
    {φ : ℂ → ℝ} (hφ : ContinuousOn φ W) (hag : Prop16Area.G.CircAgree W x (y + ofFun φ))
    {U : Set ℂ} (hUH : U ⊆ H) (hUW : MapsTo ψ U W) (Q : ℝ) {w : ℂ} {ρ δ : ℝ} (hρ : 0 < ρ)
    (hδ : 0 < δ) (hball : closedBall w (ρ + δ) ⊆ U)
    (hy : Tendsto (fun j => ∫ u, avgReg (coordChange y ψ Q) j u ∂foldedCircle w ρ) atTop
      (𝓝 (coordChange y ψ Q (foldedCircle w ρ)))) :
    Tendsto (fun j => ∫ u, avgReg (coordChange x ψ Q) j u ∂foldedCircle w ρ) atTop
      (𝓝 (coordChange y ψ Q (foldedCircle w ρ) + ∫ u, φ (ψ u) ∂foldedCircle w ρ)) := by
  have hψc : ContinuousOn ψ H := hψd.continuousOn
  set K₂ := closedBall w (ρ + δ) with hK₂def
  have hK₂ : IsCompact K₂ := isCompact_closedBall _ _
  have hK₂H : K₂ ⊆ H := hball.trans hUH
  have hwH : w ∈ Hbar := H_subset_Hbar (hK₂H (mem_closedBall_self (by linarith)))
  have hφψ : ContinuousOn (fun z => φ (ψ z)) K₂ := hφ.comp (hψc.mono hK₂H) (hUW.mono_left hball)
  obtain ⟨g, hgc, hgeq⟩ := exists_continuous_extension hK₂.isClosed hφψ
  obtain ⟨k₀, hk₀⟩ := hpush K₂ hK₂ hK₂H
  have hfc : ∀ᵐ u ∂foldedCircle w ρ, u ∈ closedBall w ρ := G1Side.ae_fc_mem_closedBall hwH hρ.le
  have hρK : closedBall w ρ ⊆ K₂ := closedBall_subset_closedBall (by linarith)
  have hrad : ∀ᶠ j in atTop, k₀ ≤ j ∧ 2 * radius j ≤ δ :=
    (eventually_ge_atTop k₀).and ((RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < δ / 2)) |>.mono
      fun k hk => by linarith)
  have hlog : ContinuousOn (fun u => Real.log ‖deriv ψ u‖) H := fun u hu => by
    have hA : AnalyticOnNhd ℂ ψ H := hψd.analyticOnNhd isOpen_H
    exact ((hA.deriv u hu).continuousAt.norm.log (norm_ne_zero_iff.2 (hψ0 u hu))).continuousWithinAt
  -- the continuous part converges
  have hsm : Tendsto (fun j => ∫ u, smoothFun g u (radius j) ∂foldedCircle w ρ) atTop
      (𝓝 (∫ u, g u ∂foldedCircle w ρ)) := by
    have hU : TendstoUniformlyOn (fun j u => smoothFun g u (radius j)) g atTop (closedBall w ρ) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hs := RegClosure.tendsto_radius_nhdsGT.eventually (smooth_unif hgc.continuousOn
        (isCompact_closedBall w ρ) (fun z hz => H_subset_Hbar (hK₂H (hρK hz))) ε hε)
      filter_upwards [hs] with j hj z hz
      rw [Real.dist_eq, abs_sub_comm]
      exact hj z hz
    exact tendsto_integral_of_tendstoUniformlyOn hU hfc (Eventually.of_forall fun j =>
      integrable_of_continuousOn_carrier (isCompact_closedBall _ _)
        (continuous_smoothFun hgc.continuousOn _).continuousOn hfc)
      (integrable_of_continuousOn_carrier (isCompact_closedBall _ _) hgc.continuousOn hfc)
  have hgφ : ∫ u, g u ∂foldedCircle w ρ = ∫ u, φ (ψ u) ∂foldedCircle w ρ :=
    integral_congr_ae (hfc.mono fun u hu => hgeq (hρK hu))
  rw [← hgφ]
  refine (hy.add hsm).congr' ?_
  filter_upwards [hrad] with j hj
  have hB : ∀ u ∈ closedBall w ρ, closedBall u (2 * radius j) ⊆ K₂ := fun u hu v hv =>
    mem_closedBall.2 ((dist_triangle v u w).trans (by
      linarith [mem_closedBall.1 hv, mem_closedBall.1 hu]))
  have hA : ∀ u ∈ closedBall w ρ, avgReg (coordChange x ψ Q) j u =
      avgReg (coordChange y ψ Q) j u + smoothFun g u (radius j) := fun u hu =>
    avgReg_coordChange_eq_add hWo hF hφ hag hψm hψd hψ0 hK₂ hK₂H (hUW.mono_left hball)
      (fun z hz => H_subset_Hbar (hψH (hK₂H hz))) hgc hgeq Q (hk₀ j hj.1).1 (hk₀ j hj.1).2
      (hB u hu)
  have hAc : ContinuousOn (fun u => avgReg (coordChange y ψ Q) j u) (closedBall w ρ) := by
    refine ((((hk₀ j hj.1).2.mono hρK).add ((continuousOn_const (c := Q)).mul
      (hlog.mono (hρK.trans hK₂H))))).congr fun u hu => ?_
    exact avgReg_coordChange_eq_push hψd hψ0 hK₂H Q (hk₀ j hj.1).2 (hB u hu)
  have hAi := integrable_of_continuousOn_carrier (isCompact_closedBall _ _) hAc hfc
  have hBi := integrable_of_continuousOn_carrier (isCompact_closedBall w ρ)
    (continuous_smoothFun hgc.continuousOn (radius j)).continuousOn hfc
  rw [integral_congr_ae (hfc.mono fun u hu => hA u hu), integral_add hAi hBi]

end Prop16Lit
end QuantumZipper
