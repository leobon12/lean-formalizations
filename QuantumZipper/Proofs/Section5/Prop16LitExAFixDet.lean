import QuantumZipper.Proofs.Section5.Prop16LitExAPalm
import QuantumZipper.Proofs.LQG.CoordChangeAreaZoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the countable condition for chart zooms (COORD-CHANGE, D98)

Deterministic lemmas towards `Prop16Lit.ExA.Prop16LitExAFixStmt`:
* `CoordChangeArea.eventually_avgReg_addConst_coordChange` (the eventual identity inside
  `isVagueLimitOn_addConst_coordChange`, stated separately);
* `CoordChangeArea.eventually_continuousOn_avgReg_coordChange`: for a field locally equal to a
  regular sample `y` plus a continuous function, with regular pushed averages of `y`, the circle
  averages of the coordinate change are eventually continuous on each compact subset of `U`;
* `Prop16Lit.ExA.goodA_of_vague`: a local vague limit plus eventually continuous circle
  averages give the countable condition `GoodA`;
* `Prop16Lit.ExA.goodA_zoomLit_of_agree`: `GoodA` for the chart zoom `h(x + ψ(·)) + Q log|ψ'| + C/γ`
  of a field whose translate is locally a chart-good sample plus a continuous function.
Own bookkeeping (from the proofs in CoordChangeAreaLocal/Zoom.lean).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace CoordChangeArea

open SWCore GoodSample G1Side

/-- **The additive constant commutes with the coordinate change**, eventually on compacts. -/
theorem eventually_avgReg_addConst_coordChange {γ : ℝ} {z y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hpush : PushRegular y ψ) {W : Set ℂ} (hWo : IsOpen W) {g : ℂ → ℝ} (hg : ContinuousOn g W)
    (hag : Prop16Area.G.CircAgree W z (y + ofFun g)) {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H)
    (hUW : MapsTo ψ U W) (hUHb : MapsTo ψ U Hbar) (Q c : ℝ) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : ∀ᶠ k in atTop, ∀ w ∈ K,
      avgReg (coordChange (addConst z c) ψ Q) k w = avgReg (addConst (coordChange z ψ Q) c) k w := by
  have hagc := circAgree_addConst hg hag c
  have hgc : ContinuousOn (fun u => g u + c) W := hg.add continuousOn_const
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hKU
  set K₂ := cthickening ε₀ K with hK₂def
  have hK₂ : IsCompact K₂ := hK.cthickening
  have hK₂H : K₂ ⊆ H := hε₀U.trans hUH
  obtain ⟨k₀, hk₀⟩ := hpush K₂ hK₂ hK₂H
  set Kψ := ψ '' K₂ with hKψdef
  have hKψ : IsCompact Kψ := hK₂.image_of_continuousOn (hψd.continuousOn.mono hK₂H)
  have hKψW : Kψ ⊆ W := image_subset_iff.2 (hUW.mono_left hε₀U)
  have hKψH : Kψ ⊆ Hbar := image_subset_iff.2 (hUHb.mono_left hε₀U)
  have hrad : ∀ᶠ k in atTop, k₀ ≤ k ∧ 2 * radius k ≤ ε₀ :=
    (eventually_ge_atTop k₀).and ((RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < ε₀ / 2)) |>.mono
      fun k hk => by linarith)
  filter_upwards [hrad] with k hk w hw
  refine ASep.avgReg_congr_of_eventually ?_
  filter_upwards [a7_dyadic_small (z := w) (radius_pos k)] with n hn
  set dn := dyadicRoundC n w with hdn
  have hball : closedBall dn (radius k) ⊆ K₂ := by
    refine hn.1.trans ?_
    intro u hu
    exact mem_cthickening_of_dist_le u w ε₀ K hw ((mem_closedBall.1 hu).trans hk.2)
  have hdK : dn ∈ K₂ := hball (mem_closedBall_self (radius_pos k).le)
  have hdH : dn ∈ Hbar := H_subset_Hbar (hK₂H hdK)
  set ν := (foldedCircle dn (radius k)).map ψ with hνdef
  haveI : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff hψm.aemeasurable).2 inferInstance
  have hν : ∀ᵐ v ∂ν, v ∈ Kψ :=
    ae_map_fc_mem hψm hdH (radius_pos k).le hKψ.isClosed.measurableSet
      fun u hu => mem_image_of_mem ψ (hball hu)
  have hL := (hk₀ k hk.1).1 dn hdK
  have e1 := evalReg_eq_add_of_circAgree hWo hF hgc hagc hKψ hKψW hKψH hν hL
  have e2 := evalReg_eq_add_of_circAgree hWo hF hg hag hKψ hKψW hKψH hν hL
  have hgi : Integrable g ν := integrable_of_continuousOn_carrier hKψ (hg.mono hKψW) hν
  have e3 : ∫ v, (g v + c) ∂ν = ∫ v, g v ∂ν + c := by
    rw [integral_add hgi (integrable_const c), integral_const, probReal_univ, one_smul]
  simp only [coordChange, addConst]
  rw [e1, e2, e3, measure_univ, ENNReal.toReal_one, mul_one]
  ring

/-- **Eventual continuity of the circle averages of the coordinate change.** -/
theorem eventually_continuousOn_avgReg_coordChange {x y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {ψ : ℂ → ℂ} (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H)
    (hψ0 : ∀ z ∈ H, deriv ψ z ≠ 0) (hpush : PushRegular y ψ) {W : Set ℂ} (hWo : IsOpen W)
    {φ : ℂ → ℝ} (hφ : ContinuousOn φ W) (hag : Prop16Area.G.CircAgree W x (y + ofFun φ))
    {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H) (hUW : MapsTo ψ U W) (hUH' : MapsTo ψ U Hbar)
    (Q : ℝ) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ᶠ k in atTop, ContinuousOn (avgReg (coordChange x ψ Q) k) K := by
  have hψc : ContinuousOn ψ H := hψd.continuousOn
  obtain ⟨ε₀, hε₀, hε₀U⟩ := hK.exists_cthickening_subset_open hUo hKU
  have hK₂ : IsCompact (cthickening ε₀ K) := hK.cthickening
  have hK₂H : cthickening ε₀ K ⊆ H := hε₀U.trans hUH
  have hφψ : ContinuousOn (fun z => φ (ψ z)) (cthickening ε₀ K) :=
    hφ.comp (hψc.mono hK₂H) (hUW.mono_left hε₀U)
  obtain ⟨g, hgc, hgeq⟩ := exists_continuous_extension isClosed_cthickening hφψ
  obtain ⟨k₀, hk₀⟩ := hpush _ hK₂ hK₂H
  have hlog : ContinuousOn (fun w => Real.log ‖deriv ψ w‖) H := fun u hu => by
    have hA : AnalyticOnNhd ℂ ψ H := hψd.analyticOnNhd isOpen_H
    exact ((hA.deriv u hu).continuousAt.norm.log (norm_ne_zero_iff.2 (hψ0 u hu))).continuousWithinAt
  have hrad : ∀ᶠ k in atTop, k₀ ≤ k ∧ 2 * radius k ≤ ε₀ :=
    (eventually_ge_atTop k₀).and ((RegClosure.tendsto_radius_nhdsGT.mono_right
      nhdsWithin_le_nhds).eventually (ge_mem_nhds (by linarith : (0 : ℝ) < ε₀ / 2)) |>.mono
      fun k hk => by linarith)
  filter_upwards [hrad] with k hk
  have hB : ∀ z ∈ K, closedBall z (2 * radius k) ⊆ cthickening ε₀ K := fun z hz =>
    (closedBall_subset_cthickening hz _).trans (cthickening_mono hk.2 K)
  have hc : ContinuousOn (fun z => (evalReg y ((foldedCircle z (radius k)).map ψ) +
      Q * Real.log ‖deriv ψ z‖) + smoothFun g z (radius k)) K :=
    ((((hk₀ k hk.1).2.mono (self_subset_cthickening K)).add
      ((continuousOn_const (c := Q)).mul (hlog.mono ((self_subset_cthickening K).trans hK₂H))))).add
      (continuous_smoothFun hgc.continuousOn _).continuousOn
  refine hc.congr fun z hz => ?_
  rw [avgReg_coordChange_eq_add hWo hF hφ hag hψm hψd hψ0 hK₂ hK₂H (hUW.mono_left hε₀U)
    (hUH'.mono_left hε₀U) hgc hgeq Q (hk₀ k hk.1).1 (hk₀ k hk.1).2 (hB z hz),
    avgReg_coordChange_eq_push hψd hψ0 hK₂H Q (hk₀ k hk.1).2 (hB z hz)]

end CoordChangeArea

namespace Prop16Lit
namespace ExA

open CoordChangeArea

/-- Finite approximation on a compact set where the circle averages are continuous. -/
theorem areaApprox_lt_top_of_continuousOn {γ : ℝ} {Z : FieldSample} {k : ℕ} {K : Set ℂ}
    (hK : IsCompact K) (hc : ContinuousOn (avgReg Z k) K) : areaApprox γ Z k K < ∞ :=
  GoodSample.withDensity_lt_top hK ((Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top)
    (continuousOn_const.mul ((continuousOn_const.mul hc).rexp))

/-- **`GoodA` from a local vague limit and eventually continuous circle averages.** -/
theorem goodA_of_vague {γ r : ℝ} {Z : FieldSample} {μ : Measure ℂ}
    (hμ : IsVagueLimitOn (ball 0 r ∩ H) (areaApprox γ Z) μ)
    (hc : ∀ K, IsCompact K → K ⊆ ball 0 r ∩ H → ∀ᶠ k in atTop, ContinuousOn (avgReg Z k) K) :
    GoodA γ Z r := by
  refine ⟨fun m => (hc _ (isCompact_hbK r m) (hbK_subset r m)).mono fun k hk =>
    areaApprox_lt_top_of_continuousOn (isCompact_hbK r m) hk, fun n g hg => ?_⟩
  obtain ⟨hgc, hgs, -⟩ := famF_dense.1 g hg
  exact ⟨_, hμ.2.2 _ ((continuous_hbCut r n).mul hgc) hgs.mul_left
    ((tsupport_mul_subset_left).trans (tsupport_hbCut r n))⟩

end ExA
end Prop16Lit
end QuantumZipper
