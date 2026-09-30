import QuantumZipper.Proofs.Section5.Prop16LitRegP1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: local regularity of chart zooms of locally free fields (D98)

Deterministic: if the translate `h(· + t)` agrees near `ψ(U)` with `y + g` (`g` continuous) and
`y` is a chart-regular sample (`ChartY`: regular, regular pushed averages, convergent RC3 at small
interior circles uniformly on compacts, continuous pushed averages at all small radii, and an
offset-uniform area limit of `y ∘ ψ + Q log|ψ'|` — all a.s. for the free field), then the chart
zoom `zoomFieldLit γ C h t ψ` is `LocalAreaRegular` on `U`. First part: the regularized circle
averages of the chart zoom (`evalReg_zoomLit_fc`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open CoordChangeArea GoodSample SWCore

/-- Chart-regular samples. -/
structure ChartY (γ : ℝ) (ψ : ℂ → ℂ) (y : FieldSample) (ν : Measure ℂ) : Prop where
  reg : IsRegularSample y
  push : PushRegular y ψ
  rc : ∀ K, IsCompact K → K ⊆ H → ∃ ρ₀ > 0, ∀ w ∈ K, ∀ ρ, 0 < ρ → ρ < ρ₀ →
    Tendsto (fun j => ∫ u, avgReg (coordChange y ψ (Qc γ)) j u ∂foldedCircle w ρ) atTop
      (𝓝 (coordChange y ψ (Qc γ) (foldedCircle w ρ)))
  cont : ∀ K, IsCompact K → K ⊆ H → ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ →
    ContinuousOn (fun w => evalReg y ((foldedCircle w ρ).map ψ)) K
  lim : HasAreaLimit γ (coordChange y ψ (Qc γ)) ν

/-- **The regularized circle averages of the chart zoom.** -/
theorem evalReg_zoomLit_fc {γ : ℝ} {ψ : ℂ → ℂ} {y : FieldSample} {ν : Measure ℂ}
    (hy : ChartY γ ψ y ν) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : MapsTo ψ H H) {V : Set ℂ} (hVo : IsOpen V)
    {g : ℂ → ℝ} (hg : ContinuousOn g V) {x' : FieldSample} {t : ℝ}
    (hag : Prop16Area.G.CircAgree V (translate x' (t : ℂ)) (y + ofFun g)) {U : Set ℂ}
    (hUo : IsOpen U) (hUH : U ⊆ H) (hUV : MapsTo ψ U V) (C : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ ρ₀ > 0, ∀ w ∈ K, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      evalReg (zoomFieldLit γ C x' t ψ) (foldedCircle w ρ) =
        coordChange y ψ (Qc γ) (foldedCircle w ρ) + ∫ u, (g (ψ u) + C / γ) ∂foldedCircle w ρ := by
  obtain ⟨F, hF⟩ := hy.reg
  have hUHb : MapsTo ψ U Hbar := fun z hz => H_subset_Hbar (hψH (hUH hz))
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hKU
  obtain ⟨ρ₁, hρ₁, hrc⟩ := hy.rc K hK (hKU.trans hUH)
  refine ⟨min ρ₁ (ε₀ / 2), lt_min hρ₁ (by linarith), fun w hw ρ hρ hρ₀ => ?_⟩
  have hρ1 : ρ < ρ₁ := lt_of_lt_of_le hρ₀ (min_le_left _ _)
  have hρ2 : ρ < ε₀ / 2 := lt_of_lt_of_le hρ₀ (min_le_right _ _)
  have hball : closedBall w (ρ + ε₀ / 2) ⊆ U :=
    (closedBall_subset_cthickening hw _).trans ((cthickening_mono (by linarith) K).trans hε₀U)
  have hρK : closedBall w ρ ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hball
  have hwH : w ∈ Hbar := H_subset_Hbar (hUH (hρK (mem_closedBall_self hρ.le)))
  have hfc : ∀ᵐ u ∂foldedCircle w ρ, u ∈ closedBall w ρ := G1Side.ae_fc_mem_closedBall hwH hρ.le
  have hagC := circAgree_addConst hg hag (C / γ)
  have ht := tendsto_coordChange_fc_local hF hψm hψd hψ0 hψH hy.push hVo
    (hg.add continuousOn_const) hagC hUH hUV (Qc γ) hρ (by linarith : (0 : ℝ) < ε₀ / 2) hball
    (hrc w hw ρ hρ hρ1)
  have hev := eventually_avgReg_addConst_coordChange (γ := γ) hF hψm hψd hy.push hVo hg hag hUo
    hUH hUV hUHb (Qc γ) (C / γ) (isCompact_closedBall w ρ) hρK
  unfold evalReg
  refine Tendsto.limUnder_eq (ht.congr' ?_)
  filter_upwards [hev] with j hj
  exact integral_congr_ae (hfc.mono fun u hu => hj u hu)

/-- The circle average of `(g ∘ ψ + c)` as a smoothing of a continuous extension. -/
theorem exists_ext_comp {ψ : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ H) {V : Set ℂ} {g : ℂ → ℝ}
    (hg : ContinuousOn g V) {K₂ : Set ℂ} (hK₂ : IsCompact K₂) (hK₂H : K₂ ⊆ H)
    (hK₂V : MapsTo ψ K₂ V) (c : ℝ) :
    ∃ g' : ℂ → ℝ, Continuous g' ∧ EqOn g' (fun u => g (ψ u) + c) K₂ :=
  exists_continuous_extension hK₂.isClosed
    ((hg.comp (hψd.continuousOn.mono hK₂H) hK₂V).add continuousOn_const)

theorem integral_fc_eq_smoothFun {w : ℂ} (hw : w ∈ Hbar) {ρ : ℝ} (hρ : 0 < ρ) {K₂ : Set ℂ}
    (hK : closedBall w ρ ⊆ K₂) {g' G : ℂ → ℝ} (h : EqOn g' G K₂) :
    ∫ u, G u ∂foldedCircle w ρ = smoothFun g' w ρ :=
  integral_congr_ae ((G1Side.ae_fc_mem_closedBall hw hρ.le).mono fun u hu => (h (hK hu)).symm)

/-- **Continuity of the small circle averages of the chart zoom.** -/
theorem continuousOn_evalReg_zoomLit {γ : ℝ} {ψ : ℂ → ℂ} {y : FieldSample} {ν : Measure ℂ}
    (hy : ChartY γ ψ y ν) (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : MapsTo ψ H H) {V : Set ℂ} (hVo : IsOpen V)
    {g : ℂ → ℝ} (hg : ContinuousOn g V) {x' : FieldSample} {t : ℝ}
    (hag : Prop16Area.G.CircAgree V (translate x' (t : ℂ)) (y + ofFun g)) {U : Set ℂ}
    (hUo : IsOpen U) (hUH : U ⊆ H) (hUV : MapsTo ψ U V) (C : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ < ρ₀ →
      ContinuousOn (fun w => evalReg (zoomFieldLit γ C x' t ψ) (foldedCircle w ρ)) K := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun ρ _ _ => by rw [he]; exact continuousOn_empty _⟩
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hKU
  have hK₂ : IsCompact (cthickening ε₀ K) := hK.cthickening
  have hK₂H : cthickening ε₀ K ⊆ H := hε₀U.trans hUH
  obtain ⟨g', hg'c, hg'⟩ := exists_ext_comp hψd hg hK₂ hK₂H (hUV.mono_left hε₀U) (C / γ)
  obtain ⟨ρE, hρE, hE⟩ := evalReg_zoomLit_fc hy hψm hψd hψ0 hψH hVo hg hag hUo hUH hUV C hK hKU
  obtain ⟨ρC, hρC, hC⟩ := hy.cont K hK (hKU.trans hUH)
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  have hm0 : 0 < z₀.im := hUH (hKU hz₀)
  refine ⟨min (min ρE ρC) (min ε₀ z₀.im), by positivity, fun ρ hρ hρ₀ => ?_⟩
  have h1 : ρ < ρE := lt_of_lt_of_le hρ₀ ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ρ < ρC := lt_of_lt_of_le hρ₀ ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ρ < ε₀ := lt_of_lt_of_le hρ₀ ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : ρ < z₀.im := lt_of_lt_of_le hρ₀ ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : ContinuousOn (fun u => Real.log ‖deriv ψ u‖) H := fun u hu => by
    have hA : AnalyticOnNhd ℂ ψ H := hψd.analyticOnNhd isOpen_H
    exact ((hA.deriv u hu).continuousAt.norm.log (norm_ne_zero_iff.2 (hψ0 u hu))).continuousWithinAt
  have hc : ContinuousOn (fun w => evalReg y ((foldedCircle w ρ).map ψ) +
      Qc γ * Real.log ‖deriv ψ w‖ + smoothFun g' w ρ) K :=
    ((hC ρ hρ h2).add ((continuousOn_const (c := Qc γ)).mul (hlog.mono (hKU.trans hUH)))).add
      (continuous_smoothFun hg'c.continuousOn ρ).continuousOn
  refine hc.congr fun w hw => ?_
  have hB : closedBall w ρ ⊆ cthickening ε₀ K :=
    (closedBall_subset_cthickening hw _).trans (cthickening_mono h3.le K)
  have hwim : ρ ≤ w.im := h4.le.trans (hmin hw)
  rw [hE w hw ρ hρ h1]
  show evalReg y ((foldedCircle w ρ).map ψ) + Qc γ * ∫ u, Real.log ‖deriv ψ u‖ ∂foldedCircle w ρ +
    _ = _
  rw [swcNA2_integral_log_deriv_fc isOpen_H hψd hψ0 hρ hwim (hB.trans hK₂H),
    integral_fc_eq_smoothFun (H_subset_Hbar (hUH (hKU hw))) hρ hB hg']

end Prop16Lit
end QuantumZipper
