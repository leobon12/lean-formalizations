import QuantumZipper.Proofs.LQG.CoordChangeAreaRC3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Coordinate change of the area measure: RC3 with convergence (COORD-CHANGE, D98)

The proofs of `CoordChangeArea.evalReg_coordChange_fc` / `ae_rc3_coordChange_free` give more than
the value of the regularized circle average of `y ∘ ψ + Q log|ψ'|` at interior circles: the dyadic
smoothings converge to the raw value (`tendsto_coordChange_fc`, `ae_tendsto_coordChange_fc_free`).
Needed to add continuous functions and constants. Own bookkeeping (same proofs).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample G1Side

set_option maxHeartbeats 400000 in
/-- **RC3 at interior circles, with convergence of the dyadic smoothings** (deterministic). -/
theorem tendsto_coordChange_fc {y : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F)
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hψH : MapsTo ψ H H) {R : Set ℂ} (hRH : R ⊆ H) {k₀ : ℕ}
    (hU : ∀ k ≥ k₀, TendstoUniformlyOn (fun j (p : ℂ × ℝ) =>
        ∫ u, avgReg y j u ∂((foldedCircle p.1 (p.2 * radius k)).map ψ))
      (fun p => evalReg y ((foldedCircle p.1 (p.2 * radius k)).map ψ)) atTop (R ×ˢ Icc 1 2))
    (hC : ∀ k ≥ k₀, ContinuousOn (fun p : ℂ × ℝ =>
      evalReg y ((foldedCircle p.1 (p.2 * radius k)).map ψ)) (R ×ˢ Icc 1 2))
    (Q : ℝ) {w : ℂ} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ) (hwR : closedBall w (ρ + δ) ⊆ R)
    {k₁ : ℕ} (hk₁ : k₀ ≤ k₁) {α₀ : ℝ} (hα₀ : α₀ ∈ Icc (1 : ℝ) 2) (hρk : ρ = α₀ * radius k₁) :
    Tendsto (fun j => ∫ u, avgReg (coordChange y ψ Q) j u ∂foldedCircle w ρ) atTop
      (𝓝 (coordChange y ψ Q (foldedCircle w ρ))) := by
  have hψc : ContinuousOn ψ H := hψd.continuousOn
  have hK₃H : closedBall w (ρ + δ) ⊆ H := hwR.trans hRH
  have hwH : w ∈ Hbar := H_subset_Hbar (hK₃H (mem_closedBall_self (by linarith)))
  have hρK : closedBall w ρ ⊆ closedBall w (ρ + δ) := closedBall_subset_closedBall (by linarith)
  have hg1 : ∀ u ∈ R, ((u, (1 : ℝ)) : ℂ × ℝ) ∈ R ×ˢ Icc (1 : ℝ) 2 :=
    fun u hu => ⟨hu, by norm_num, by norm_num⟩
  have hgα : ∀ u ∈ R, ((u, α₀) : ℂ × ℝ) ∈ R ×ˢ Icc (1 : ℝ) 2 := fun u hu => ⟨hu, hα₀⟩
  have hE1 : ∀ k ≥ k₀, ContinuousOn (pushE y ψ (radius k)) R := fun k hk =>
    ((hC k hk).comp (continuousOn_id.prodMk continuousOn_const) hg1).congr fun u _ => by
      show evalReg y _ = evalReg y _
      rw [one_mul]
      rfl
  have hU1 : ∀ k ≥ k₀, TendstoUniformlyOn (fun j u =>
      ∫ v, avgReg y j v ∂((foldedCircle u (radius k)).map ψ)) (pushE y ψ (radius k)) atTop R := by
    intro k hk
    have h := ((hU k hk).comp fun u : ℂ => ((u, (1 : ℝ)) : ℂ × ℝ)).mono fun u hu => hg1 u hu
    have e1 : (fun j u => ∫ v, avgReg y j v ∂((foldedCircle u (radius k)).map ψ)) =
        fun j => (fun p : ℂ × ℝ => ∫ v, avgReg y j v ∂((foldedCircle p.1 (p.2 * radius k)).map ψ)) ∘
          fun u : ℂ => ((u, (1 : ℝ)) : ℂ × ℝ) := by
      funext j u; simp only [Function.comp_apply, one_mul]
    have e2 : pushE y ψ (radius k) =
        (fun p : ℂ × ℝ => evalReg y ((foldedCircle p.1 (p.2 * radius k)).map ψ)) ∘
          fun u : ℂ => ((u, (1 : ℝ)) : ℂ × ℝ) := by
      funext u; simp only [pushE, Function.comp_apply, one_mul]
    rw [e1, e2]; exact h
  have hEρc : ContinuousOn (pushE y ψ ρ) R := by
    have h := (hC k₁ hk₁).comp (continuousOn_id.prodMk continuousOn_const) hgα
    rw [hρk]; exact h
  have hUρ : TendstoUniformlyOn (fun j u =>
      ∫ v, avgReg y j v ∂((foldedCircle u ρ).map ψ)) (pushE y ψ ρ) atTop R := by
    have h := ((hU k₁ hk₁).comp fun u : ℂ => ((u, α₀) : ℂ × ℝ)).mono fun u hu => hgα u hu
    rw [hρk]; exact h
  have hlog : ContinuousOn (fun u => Real.log ‖deriv ψ u‖) H := fun u hu => by
    have hA : AnalyticOnNhd ℂ ψ H := hψd.analyticOnNhd isOpen_H
    exact ((hA.deriv u hu).continuousAt.norm.log (norm_ne_zero_iff.2 (hψ0 u hu))).continuousWithinAt
  have hfcρ : ∀ᵐ u ∂foldedCircle w ρ, u ∈ closedBall w ρ :=
    G1Side.ae_fc_mem_closedBall hwH hρ.le
  have hlogi : Integrable (fun u => Real.log ‖deriv ψ u‖) (foldedCircle w ρ) :=
    integrable_of_continuousOn_carrier (isCompact_closedBall _ _)
      (hlog.mono (hρK.trans hK₃H)) hfcρ
  have hsym : ∀ j : ℕ, k₀ ≤ j → radius j ≤ δ →
      ∫ u, pushE y ψ (radius j) u ∂foldedCircle w ρ =
        ∫ v, pushE y ψ ρ v ∂foldedCircle w (radius j) := by
    intro j hj hjδ
    have hjK : closedBall w (radius j) ⊆ closedBall w (ρ + δ) :=
      closedBall_subset_closedBall (by linarith)
    exact integral_pushed_swap hF hψm hψc hψH hρ (radius_pos j)
      ((closedBall_subset_closedBall (by linarith)).trans hK₃H)
      ((hU1 j hj).mono (hρK.trans hwR)) ((hE1 j hj).mono (hρK.trans hwR))
      (hUρ.mono (hjK.trans hwR)) (hEρc.mono (hjK.trans hwR))
  have havg : ∀ j : ℕ, k₀ ≤ j → 2 * radius j ≤ δ → ∀ u ∈ closedBall w ρ,
      avgReg (coordChange y ψ Q) j u = pushE y ψ (radius j) u + Q * Real.log ‖deriv ψ u‖ := by
    intro j hj hjδ u hu
    refine avgReg_coordChange_eq_push hψd hψ0 hRH Q (hE1 j hj) fun v hv => hwR ?_
    refine mem_closedBall.2 ((dist_triangle v u w).trans ?_)
    linarith [mem_closedBall.1 hv, mem_closedBall.1 hu]
  have hrad : ∀ᶠ j in atTop, k₀ ≤ j ∧ 2 * radius j ≤ δ :=
    (eventually_ge_atTop k₀).and ((RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < δ / 2)) |>.mono
      fun k hk => by linarith)
  have hev : ∀ᶠ j in atTop, ∫ u, avgReg (coordChange y ψ Q) j u ∂foldedCircle w ρ =
      ∫ v, pushE y ψ ρ v ∂foldedCircle w (radius j) +
        Q * ∫ u, Real.log ‖deriv ψ u‖ ∂foldedCircle w ρ := by
    filter_upwards [hrad] with j hj
    have hEi : Integrable (pushE y ψ (radius j)) (foldedCircle w ρ) :=
      integrable_of_continuousOn_carrier (isCompact_closedBall _ _)
        ((hE1 j hj.1).mono (hρK.trans hwR)) hfcρ
    rw [integral_congr_ae (hfcρ.mono fun u hu => havg j hj.1 hj.2 u hu),
      integral_add hEi (hlogi.const_mul Q), integral_const_mul,
      hsym j hj.1 (by linarith [radius_pos j])]
  have hlim : Tendsto (fun j => ∫ v, pushE y ψ ρ v ∂foldedCircle w (radius j)) atTop
      (𝓝 (pushE y ψ ρ w)) := by
    have hnhds : R ∈ 𝓝 w := Filter.mem_of_superset (ball_mem_nhds w (by linarith))
      (ball_subset_closedBall.trans hwR)
    exact Prop16Asm.tendsto_integral_foldedCircle_radius hδ
      ((hEρc.mono ((closedBall_subset_closedBall (by linarith)).trans hwR)).mono
        inter_subset_left) hwH (hEρc.continuousAt hnhds)
  have hT : coordChange y ψ Q (foldedCircle w ρ) =
      pushE y ψ ρ w + Q * ∫ u, Real.log ‖deriv ψ u‖ ∂foldedCircle w ρ := rfl
  rw [hT]
  exact (hlim.add_const _).congr' (hev.mono fun j hj => hj.symm)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end CoordChangeArea
end QuantumZipper
