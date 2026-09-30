import QuantumZipper.Proofs.Thm18.A1RSBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (15): inputs of the parameter coupling on a box

Supplies the hypotheses of `abs_kernelCov2_smear_param_le` (A1RSParamE.lean) on the parameter
boxes, in the angle representation `a1rfNu_eq_map_angles`:

* `norm_sidePush_le_unif`: `‖f_t(ψ(w))‖ ≤ R₁` for `w ∈ ℍ`, `‖w‖ ≤ ρ₀`, `t ∈ (0, T]`
  (`‖f_t z − z‖ ≤ 24 M + 8 √t`, `CoreArc.norm_fwdMap_sub_le_uniform`, and the bound of the
  continuous extension of `ψ` on a compact set);
* `circM_strip_le`: the side-circle strip `{θ : Im fold(d + s e^{iθ}) ≤ τ₁}` has `circM`-mass
  `≤ (3/2) √(τ₁/s)` (`A1R.foldedCircle_strip_le`);
* `ae_circM_mem_H`: `circM`-a.e. the side-circle point lies in `ℍ`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm Thm18Asm.G1RC TwoPoint

/-- **Uniform pointwise bound of the pushing maps.** -/
theorem norm_sidePush_le_unif {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {T : ℝ}
    (hT : 0 < T) (ρ₀ : ℝ) :
    ∃ R₁ : ℝ, 0 ≤ R₁ ∧ ∀ t ∈ Ioc (0 : ℝ) T, ∀ w ∈ H, ‖w‖ ≤ ρ₀ →
      ‖fwdMap W t (g1zSideMap left W w)‖ ≤ R₁ := by
  obtain ⟨ψe, -, hψc, hψeq, -⟩ := exists_sideMap_ext hG left
  have hK : IsCompact (Hbar ∩ closedBall (0 : ℂ) ρ₀) :=
    (isCompact_closedBall (0 : ℂ) ρ₀).inter_left isClosed_Hbar
  obtain ⟨Bψ, hBψ⟩ := hK.exists_bound_of_continuousOn (hψc.mono inter_subset_left)
  obtain ⟨MW, hMW⟩ := RegCont.exists_abs_le_on_Icc hG.1 T
  have hMW0 : 0 ≤ MW := (abs_nonneg _).trans (hMW 0 ⟨le_rfl, hT.le⟩)
  refine ⟨max Bψ 0 + 24 * MW + 8 * Real.sqrt T, by positivity, fun t ht w hw hwn => ?_⟩
  have hmem := sideMap_mem_compl_fwdHull hG ht.1.le left hw
  have h1 := CoreArc.norm_fwdMap_sub_le_uniform hG.1 hG.2.1 ht.1
    (fun r hr => hMW r ⟨hr.1, hr.2.trans ht.2⟩) hmem
  have h2 : ‖g1zSideMap left W w‖ ≤ Bψ := by
    rw [hψeq hw]
    exact hBψ w ⟨show 0 ≤ w.im from le_of_lt hw, by rwa [mem_closedBall, dist_zero_right]⟩
  have h3 : Real.sqrt t ≤ Real.sqrt T := Real.sqrt_le_sqrt ht.2
  have h4 := norm_sub_norm_le (fwdMap W t (g1zSideMap left W w)) (g1zSideMap left W w)
  have h5 := le_max_left Bψ 0
  linarith

/-- The side-circle strip in the angle parametrization. -/
theorem circM_strip_le (d : ℂ) {s τ₁ : ℝ} (hs : 0 < s) (hτ₁ : 0 ≤ τ₁) :
    (G1RC.circM.prod E6.XAreaPC.angMeas).real
        {q : ℝ × ℝ | (foldH (circleMap d s q.1)).im ≤ τ₁} ≤ 3 / 2 * Real.sqrt (τ₁ / s) := by
  have hc : Measurable fun θ : ℝ => foldH (circleMap d s θ) :=
    (CircleFubini.continuous_foldH'.measurable).comp (continuous_circleMap d s).measurable
  have e : {q : ℝ × ℝ | (foldH (circleMap d s q.1)).im ≤ τ₁} =
      {θ : ℝ | (foldH (circleMap d s θ)).im ≤ τ₁} ×ˢ (univ : Set ℝ) := by
    ext q; simp
  have hG : MeasurableSet {u : ℂ | |u.im| ≤ τ₁} :=
    measurableSet_le (Complex.continuous_im.abs.measurable) measurable_const
  have e2 : G1RC.circM {θ : ℝ | (foldH (circleMap d s θ)).im ≤ τ₁} =
      foldedCircle d s {u : ℂ | |u.im| ≤ τ₁} := by
    rw [G1RC.foldedCircle_eq_map_circM, Measure.map_apply hc hG]
    congr 1
    ext θ
    simp only [mem_setOf_eq, mem_preimage, TwoPoint.im_foldH, abs_abs]
  rw [e, measureReal_def, Measure.prod_prod, measure_univ, mul_one, e2]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (A1R.foldedCircle_strip_le d hs hτ₁)

/-- `circM`-a.e. the side-circle point lies in `ℍ`. -/
theorem ae_circM_mem_H (d : ℂ) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ θ ∂G1RC.circM, foldH (circleMap d s θ) ∈ H := by
  have hc : Measurable fun θ : ℝ => foldH (circleMap d s θ) :=
    (CircleFubini.continuous_foldH'.measurable).comp (continuous_circleMap d s).measurable
  have h := TwoPoint.foldedCircle_ae_mem_H d hs
  rw [G1RC.foldedCircle_eq_map_circM] at h
  exact (ae_map_iff hc.aemeasurable isOpen_H.measurableSet).1 h

/-- The pushed side circle in the angle parametrization, for any measurable version `g` of
`f_t ∘ ψ`. -/
theorem a1rMu_eq_map_circM {W : ℝ → ℝ} {t : ℝ} {left : Bool} {g : ℂ → ℂ} (hgm : Measurable g)
    (hEq : EqOn (fun w => fwdMap W t (g1zSideMap left W w)) g H) (d : ℂ) {s : ℝ} (hs : 0 < s) :
    a1rMu W t left d s = G1RC.circM.map (fun θ => g (foldH (circleMap d s θ))) := by
  have hc₁ : Measurable fun θ : ℝ => foldH (circleMap d s θ) :=
    (CircleFubini.continuous_foldH'.measurable).comp (continuous_circleMap d s).measurable
  unfold a1rMu
  rw [show (fun θ => g (foldH (circleMap d s θ))) = g ∘ fun θ => foldH (circleMap d s θ) from rfl,
    ← Measure.map_map hgm hc₁, ← G1RC.foldedCircle_eq_map_circM]
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hs] with u hu
  exact hEq hu

/-- The smeared measures in the angle parametrization, for any measurable version `g`. -/
theorem a1rfNu_eq_map_angles' {W : ℝ → ℝ} (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t)
    {left : Bool} {g : ℂ → ℂ} (hgm : Measurable g)
    (hEq : EqOn (fun w => fwdMap W t (g1zSideMap left W w)) g H) (d : ℂ) {s : ℝ} (hs : 0 < s)
    (ρ : ℝ) :
    a1rfNu W t left d s ρ = (G1RC.circM.prod E6.XAreaPC.angMeas).map (fun q : ℝ × ℝ =>
      fwdMapInv W t (foldH (circleMap (g (foldH (circleMap d s q.1))) ρ q.2))) := by
  have hc₁ : Measurable fun θ : ℝ => foldH (circleMap d s θ) :=
    (CircleFubini.continuous_foldH'.measurable).comp (continuous_circleMap d s).measurable
  have hgm' : Measurable fun θ : ℝ => g (foldH (circleMap d s θ)) := hgm.comp hc₁
  have hF : Measurable fun p : ℂ × ℝ => fwdMapInv W t (foldH (circleMap p.1 ρ p.2)) :=
    A1RF.measurable_smear (RTBeur.measurable_fwdMapInv_rt hG.1 hG.2.1 ht.le) ρ
  unfold a1rfNu
  rw [a1rMu_eq_map_circM hgm hEq d hs,
    show E6.XAreaPC.angMeas = E6.XAreaPC.angMeas.map id from Measure.map_id.symm,
    Measure.map_prod_map _ _ hgm' measurable_id, Measure.map_id, Measure.map_map hF
      (hgm'.prodMap measurable_id)]
  rfl

/-- The smoothing strip in the angle parametrization. -/
theorem angles_stripU_eq {W : ℝ → ℝ} {t : ℝ} {left : Bool} {g : ℂ → ℂ} (hgm : Measurable g)
    (hEq : EqOn (fun w => fwdMap W t (g1zSideMap left W w)) g H) (d : ℂ) {s : ℝ} (hs : 0 < s)
    (ρ τ : ℝ) :
    (G1RC.circM.prod E6.XAreaPC.angMeas).real
        {q : ℝ × ℝ | (foldH (circleMap (g (foldH (circleMap d s q.1))) ρ q.2)).im ≤ τ} =
      ((a1rMu W t left d s).prod E6.XAreaPC.angMeas).real (stripPar ρ τ) := by
  have hc₁ : Measurable fun θ : ℝ => foldH (circleMap d s θ) :=
    (CircleFubini.continuous_foldH'.measurable).comp (continuous_circleMap d s).measurable
  have hgm' : Measurable fun θ : ℝ => g (foldH (circleMap d s θ)) := hgm.comp hc₁
  rw [a1rMu_eq_map_circM hgm hEq d hs,
    show E6.XAreaPC.angMeas = E6.XAreaPC.angMeas.map id from Measure.map_id.symm,
    Measure.map_prod_map _ _ hgm' measurable_id, Measure.map_id, measureReal_def, measureReal_def,
    Measure.map_apply (hgm'.prodMap measurable_id) (measurableSet_stripPar ρ τ)]
  rfl

end A1RS
end R18
end QuantumZipper
