import QuantumZipper.Proofs.Zipper.XFlowUCFix
import QuantumZipper.Proofs.Zipper.UnifUC1Rad

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FLOW-MECH (1/3): the admissibility node `F1.FlowAdmStmt`

**Main result** `flowAdmStmt_holds : FlowAdmStmt`: for a continuous driver `W` with `W 0 = 0`,
every `μ_{p,ρ} = (ψ_u)_* (ν_p ⋆ fc(·, ρ))`, `p = (u, s, d, r) ∈ flowPar`, `ρ ∈ [0,1]`, is an
admissible probability measure.

This is the D33 proof `RegUnif.admissible_muUS` (UnifUC1Rad.lean, with `admissible_muUS_zero`,
`muUS_eq_map`, `muUS_zero_eq` of UnifUC1RadBasic.lean) with the dyadic circle `fc(d, 2^{-k})`
replaced by the general circle `fc(d, r)`, `r > 0`, and the time horizon `T = u + s`; nothing in
that proof uses that the radius is dyadic. Sources as there: the Frostman bound of pushed circles
(`RegCont.isFrostman_pfc_frostC`), the mixture stability `RegUnif.goodM_map_bindFc`, and
`FrostmanReg.isAdmissibleH_of_frostman` (own bookkeeping, D33).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

open RegCont TwoPoint B2 RegUnif

variable {W : ℝ → ℝ}

theorem isProbabilityMeasure_flowNu (hW : Continuous W) {p : ℝ × ℝ × ℂ × ℝ} (hs : 0 ≤ p.2.1) :
    IsProbabilityMeasure (flowNu W p) := by
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2.1)) hs
  unfold flowNu
  infer_instance

/-- `ν_p` lives in `ℍ`, inside the ball of radius `revBound (2M) (u+s) (‖d‖ + r)`. -/
theorem flowNu_ae_H_norm (hW : Continuous W) {p : ℝ × ℝ × ℂ × ℝ} {Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) (p.1 + p.2.1), |W t| ≤ Mw) (hu : 0 ≤ p.1) (hs : 0 ≤ p.2.1)
    (hr : 0 < p.2.2.2) :
    ∀ᵐ x ∂flowNu W p, x ∈ H ∧
      ‖x‖ ≤ revBound (2 * Mw) (p.1 + p.2.1) (‖p.2.2.1‖ + p.2.2.2) := by
  have hV := continuous_vrev hW (p.1 + p.2.1)
  have hRm := TwoPoint.measurable_revMap hV hs
  refine (ae_map_iff hRm.aemeasurable (measurableSet_H_norm_le _)).2 ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H p.2.2.1 hr,
    TwoPoint.foldedCircle_ae_norm_le p.2.2.1 hr.le] with z hz hzn
  exact ⟨TwoPoint.im_revMap_pos hV hz hs, (norm_revMap_le_revBound hV hs
    (fun x _ => abs_vrev_le hMw ⟨add_nonneg hu hs, le_rfl⟩ x) _ hzn).trans
    (revBound_mono (by linarith))⟩

/-- `ν_p` is supported in a ball of `ℍ̄` and a.s. in `ℍ` (the D33 `alphaUS_ae_mem`). -/
theorem flowNu_ae_mem (hW : Continuous W) {p : ℝ × ℝ × ℂ × ℝ} (hu : 0 ≤ p.1) (hs : 0 ≤ p.2.1)
    (hr : 0 < p.2.2.2) :
    ∃ R₁ : ℝ, 0 ≤ R₁ ∧ (flowNu W p) (CircleFubini.ballH R₁)ᶜ = 0 ∧
      ∀ᵐ z ∂flowNu W p, z ∈ H := by
  obtain ⟨Mw, hMw⟩ := exists_abs_le_on_Icc hW (p.1 + p.2.1)
  have hα := flowNu_ae_H_norm hW hMw hu hs hr
  set R := revBound (2 * Mw) (p.1 + p.2.1) (‖p.2.2.1‖ + p.2.2.2)
  refine ⟨max R 0, le_max_right _ _, ae_iff.1 (hα.mono fun x hx => ?_), hα.mono fun x hx => hx.1⟩
  exact ⟨mem_closedBall_zero_iff.2 (hx.2.trans (le_max_left _ _)),
    show (0 : ℝ) ≤ x.im from le_of_lt hx.1⟩

theorem flowMu_eq_map (hW : Continuous W) (hW0 : W 0 = 0) {p : ℝ × ℝ × ℂ × ℝ} {Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) (p.1 + p.2.1), |W t| ≤ Mw) (hu : 0 ≤ p.1) (hs : 0 ≤ p.2.1)
    (hr : 0 < p.2.2.2) {ρ : ℝ} (hρ : 0 < ρ) :
    flowMu W p ρ = (bindFc (flowNu W p) ρ).map (revMap (vrev W p.1) p.1) := by
  have := isProbabilityMeasure_flowNu hW hs
  refine Measure.map_congr ?_
  filter_upwards [CoordReg.bind_fc_mem_H_norm _ hρ
    ((flowNu_ae_H_norm hW hMw hu hs hr).mono fun x hx => hx.2)] with x hx
  exact fwdMapInv_eq_revMap_vrev hW hW0 hu hx.1

/-- `μ_{p,0} = (ψ_{u+s})_* fc(d, r)` (cocycle `ψ_u ∘ R_{u,s} = ψ_{u+s}`). -/
theorem flowMu_zero_eq (hW : Continuous W) (hW0 : W 0 = 0) {p : ℝ × ℝ × ℂ × ℝ} {Mw : ℝ}
    (hMw : ∀ t ∈ Icc (0 : ℝ) (p.1 + p.2.1), |W t| ≤ Mw) (hu : 0 ≤ p.1) (hs : 0 ≤ p.2.1)
    (hr : 0 < p.2.2.2) :
    flowMu W p 0 =
      (foldedCircle p.2.2.1 p.2.2.2).map (revMap (vrev W (p.1 + p.2.1)) (p.1 + p.2.1)) := by
  have := isProbabilityMeasure_flowNu hW hs
  have hαH := (flowNu_ae_H_norm hW hMw hu hs hr).mono fun x hx => hx.1
  have hRm := TwoPoint.measurable_revMap (continuous_vrev hW (p.1 + p.2.1)) hs
  have hψm := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hu
  show (bindFc (flowNu W p) 0).map (fwdMapInv W p.1) = _
  rw [bindFc_zero_of_ae_H hαH]
  have e1 : (flowNu W p).map (fwdMapInv W p.1) =
      (flowNu W p).map (revMap (vrev W p.1) p.1) := by
    refine Measure.map_congr ?_
    filter_upwards [hαH] with x hx
    exact fwdMapInv_eq_revMap_vrev hW hW0 hu hx
  rw [e1]
  unfold flowNu
  rw [Measure.map_map hψm hRm]
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H p.2.2.1 hr] with z hz
  exact (revMap_vrev_split hW hu hu hs le_rfl hz).symm

/-- **FLOW-MECH: the admissibility node.** -/
theorem flowAdmStmt_holds : FlowAdmStmt := by
  intro W hW hW0 p hp ρ hρ
  obtain ⟨hu, hs, -, hr⟩ := hp
  have hT0 : 0 ≤ p.1 + p.2.1 := add_nonneg hu hs
  obtain ⟨Mw, hMw⟩ := exists_abs_le_on_Icc hW (p.1 + p.2.1)
  rcases hρ.1.eq_or_lt with h | h
  · rw [← h, flowMu_zero_eq hW hW0 hMw hu hs hr]
    have hV := continuous_vrev hW (p.1 + p.2.1)
    have hRm := TwoPoint.measurable_revMap hV hT0
    have hG : GoodM ((foldedCircle p.2.2.1 p.2.2.2).map
        (revMap (vrev W (p.1 + p.2.1)) (p.1 + p.2.1))) (1 / 3)
        (frostC (p.1 + p.2.1) p.2.2.2 (‖p.2.2.1‖ + p.2.2.2))
        (revBound (2 * Mw) (p.1 + p.2.1) (‖p.2.2.1‖ + p.2.2.2)) := by
      refine ⟨by infer_instance,
        isFrostman_pfc_frostC hV hT0 le_rfl hr le_rfl le_rfl, ?_⟩
      refine ae_iff.1 ((ae_map_iff hRm.aemeasurable (measurableSet_closedBall_inter_Hbar _)).2 ?_)
      filter_upwards [TwoPoint.foldedCircle_ae_mem_H _ hr,
        TwoPoint.foldedCircle_ae_norm_le _ hr.le] with z hz hzn
      exact ⟨mem_closedBall_zero_iff.2 (norm_revMap_le_revBound hV hT0
        (fun r _ => abs_vrev_le hMw ⟨hT0, le_rfl⟩ r) _ hzn),
        show (0 : ℝ) ≤ _ from le_of_lt (TwoPoint.im_revMap_pos hV hz hT0)⟩
    exact ⟨hG.admissible (by norm_num), hG.prob.measure_univ⟩
  · have := isProbabilityMeasure_flowNu hW hs
    have hψm := TwoPoint.measurable_revMap (continuous_vrev hW p.1) hu
    have hα := flowNu_ae_H_norm hW hMw hu hs hr
    have huT : p.1 ∈ Icc (0 : ℝ) (p.1 + p.2.1) := ⟨hu, by linarith⟩
    rw [flowMu_eq_map hW hW0 hMw hu hs hr h]
    have hG := goodM_map_bindFc hψm (ρ := ρ) (α := 1 / 3)
      (C := frostC (p.1 + p.2.1) ρ
        (revBound (2 * Mw) (p.1 + p.2.1) (‖p.2.2.1‖ + p.2.2.2) + 1))
      (B := revBound (2 * Mw) (p.1 + p.2.1)
        (revBound (2 * Mw) (p.1 + p.2.1) (‖p.2.2.1‖ + p.2.2.2) + 1))
      (by unfold frostC; positivity)
      (hα.mono fun z hz =>
        (goodM_pushed_circle hW hW0 hMw huT h le_rfl (by linarith [hz.2, hρ.2])).2)
    exact ⟨hG.admissible (by norm_num), hG.prob.measure_univ⟩

end F1
end QuantumZipper
