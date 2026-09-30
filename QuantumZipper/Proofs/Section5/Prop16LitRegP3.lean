import QuantumZipper.Proofs.Section5.Prop16LitRegP2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: local regularity of chart zooms, second part (D98)

`eventually_avgReg_zoomLit`: the dyadic circle averages of the chart zoom are its regularized
circle values, eventually on compacts. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open CoordChangeArea GoodSample SWCore

theorem eventually_avgReg_zoomLit {γ : ℝ} {ψ : ℂ → ℂ} {y : FieldSample} {ν : Measure ℂ}
    (hy : ChartY γ ψ y ν) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : MapsTo ψ H H) {V : Set ℂ} (hVo : IsOpen V)
    {g : ℂ → ℝ} (hg : ContinuousOn g V) {x' : FieldSample} {t : ℝ}
    (hag : Prop16Area.G.CircAgree V (translate x' (t : ℂ)) (y + ofFun g)) {U : Set ℂ}
    (hUo : IsOpen U) (hUH : U ⊆ H) (hUV : MapsTo ψ U V) (C : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∀ᶠ k in atTop, ∀ z ∈ K,
      avgReg (zoomFieldLit γ C x' t ψ) k z =
        evalReg (zoomFieldLit γ C x' t ψ) (foldedCircle z (radius k)) := by
  obtain ⟨F, hF⟩ := hy.reg
  have hUHb : MapsTo ψ U Hbar := fun z hz => H_subset_Hbar (hψH (hUH hz))
  rcases K.eq_empty_or_nonempty with he | hne
  · exact Eventually.of_forall fun k z hz => by rw [he] at hz; exact absurd hz (notMem_empty z)
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hKU
  have hK₂ : IsCompact (cthickening ε₀ K) := hK.cthickening
  have hK₂H : cthickening ε₀ K ⊆ H := hε₀U.trans hUH
  obtain ⟨g', hg'c, hg'⟩ := exists_ext_comp hψd hg hK₂ hK₂H (hUV.mono_left hε₀U) (C / γ)
  obtain ⟨ρE, hρE, hE⟩ := evalReg_zoomLit_fc hy hψm hψd hψ0 hψH hVo hg hag hUo hUH hUV C hK hKU
  obtain ⟨k₀, hk₀⟩ := hy.push _ hK₂ hK₂H
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hm0 : 0 < z₀.im := hUH (hKU hz₀)
  have hagC := circAgree_addConst hg hag (C / γ)
  have hrad : ∀ᶠ k in atTop, k₀ ≤ k ∧ 2 * radius k ≤ ε₀ ∧ radius k < ρE ∧ radius k < z₀.im := by
    have ht := RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds
    exact (eventually_ge_atTop k₀).and ((ht.eventually (ge_mem_nhds (by linarith :
      (0 : ℝ) < ε₀ / 2))).mono (fun k hk => by linarith) |>.and ((ht.eventually (gt_mem_nhds hρE)).and
      (ht.eventually (gt_mem_nhds hm0))))
  filter_upwards [hrad, eventually_avgReg_addConst_coordChange (γ := γ) hF hψm hψd hy.push hVo hg
    hag hUo hUH hUV hUHb (Qc γ) (C / γ) hK hKU] with k hk hev z hz
  obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
  have hr := radius_pos k
  have hB2 : closedBall z (2 * radius k) ⊆ cthickening ε₀ K :=
    (closedBall_subset_cthickening hz _).trans (cthickening_mono hk2 K)
  have hB1 : closedBall z (radius k) ⊆ cthickening ε₀ K :=
    (closedBall_subset_closedBall (by linarith)).trans hB2
  have hzim : radius k ≤ z.im := hk4.le.trans (hmin hz)
  show avgReg (addConst (coordChange (translate x' (t : ℂ)) ψ (Qc γ)) (C / γ)) k z = _
  rw [← hev z hz,
    avgReg_coordChange_eq_add hVo hF (hg.add continuousOn_const) hagC hψm hψd hψ0 hK₂ hK₂H
      (hUV.mono_left hε₀U) (fun w hw => H_subset_Hbar (hψH (hK₂H hw))) hg'c hg' (Qc γ)
      (hk₀ k hk1).1 (hk₀ k hk1).2 hB2,
    avgReg_coordChange_eq_push hψd hψ0 hK₂H (Qc γ) (hk₀ k hk1).2 hB2,
    hE z hz _ hr hk3]
  show _ = evalReg y ((foldedCircle z (radius k)).map ψ) +
    Qc γ * ∫ u, Real.log ‖deriv ψ u‖ ∂foldedCircle z (radius k) + _
  rw [swcNA2_integral_log_deriv_fc isOpen_H hψd hψ0 hr hzim (hB1.trans hK₂H),
    integral_fc_eq_smoothFun (H_subset_Hbar (hUH (hKU hz))) hr hB1 hg']

end Prop16Lit
end QuantumZipper
