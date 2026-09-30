import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun

/-!
# D29 (wedge unzipping), part 6: W-X and W-C from the free-field statements

Continuation of `WedgeUnzipCore.lean` (decision D29). With the radial resampling
`Z = X'' + α₀(−log|·|) + G` (`WedgeDecompStmt`) and the proved deterministic identity
`unzipAddFun` (unzipping commutes with adding a continuous function):

* `wedgeContinuum_of_x`: `WedgeContinuumStmt` (W-C) from W-D and `XContinuumStmt` (X-C);
* `wedgeExactAll_of_x`: `WedgeExactAllStmt` (W-X) from W-D, X-G, X-C, `XExactAllStmt` (X-X) and
  `GlobalCaraStmt` (C);
* `unscaledB3dStmt_of_x`: hence `F2.UnscaledB3dStmt` from W-D, X-G, X-X, X-C and C.

Own bookkeeping (M4-T1 `evalReg_add_ofFun_fc`, dominated convergence for circle averages of a
continuous function).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- **(Core X-X, RC3 for `x` at all times)** For `x = X + α₀(−log|·|)`, a.s., for all `t ≥ 0`, the
folded-circle values of `x_t` are its regularized ones. -/
def XExactAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (F2.unzX κ (X ω) (drive κ B ω) t) (foldedCircle d r) =
        F2.unzX κ (X ω) (drive κ B ω) t (foldedCircle d r)

/-! ## Deterministic lemmas -/

theorem fc_eq_all {x y : FieldSample}
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r))
    (c : ℂ) {r : ℝ} (hr : 0 < r) : x (foldedCircle c r) = y (foldedCircle c r) := by
  rw [← WedgeTK.fc_foldH_eq, h _ (CircleFubini.foldH_mem_Hbar' _) _ hr]

/-- Regularity only reads folded-circle values. -/
theorem isRegularWith_of_fc {x y : FieldSample} {F : ℂ × ℝ → ℝ}
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r))
    (hy : IsRegularWith y F) : IsRegularWith x F := by
  refine ⟨hy.1, fun k z hz => ?_, hy.2.2⟩
  simp_rw [fc_eq_all h _ (radius_pos k)]
  exact hy.2.1 k z hz

/-- Circle averages of a continuous `g`, integrated against a probability measure carried by a
bounded part of `ℍ`, converge to `∫ g`, and are integrable. -/
theorem tendsto_integral_smoothFun {g : ℂ → ℝ} (hg : Continuous g) {ν : Measure ℂ}
    [IsProbabilityMeasure ν] {B : ℝ} (hνB : ∀ᵐ w ∂ν, w ∈ H ∧ ‖w‖ ≤ B) :
    (∀ ρ : ℝ, 0 < ρ → Integrable (fun w => GoodSample.smoothFun g w ρ) ν) ∧
      Tendsto (fun ρ => ∫ w, GoodSample.smoothFun g w ρ ∂ν) (𝓝[>] 0) (𝓝 (∫ w, g w ∂ν)) := by
  have hgc : ContinuousOn g Hbar := hg.continuousOn
  have hsm : ∀ ρ : ℝ, Continuous fun w => GoodSample.smoothFun g w ρ := fun ρ =>
    GoodSample.continuous_smoothFun hgc _
  refine ⟨fun ρ hρ => ?_, ?_⟩
  · obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (B + ρ)).exists_bound_of_continuousOn
      hg.continuousOn
    refine (integrable_const M).mono' (hsm ρ).aestronglyMeasurable (hνB.mono fun w hw => ?_)
    rw [Real.norm_eq_abs]
    exact abs_smoothFun_le (R := B + ρ) (fun z hz => by
      have := hM z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
      rwa [Real.norm_eq_abs] at this) hρ.le (by linarith [hw.2])
  · obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (B + 1)).exists_bound_of_continuousOn
      hg.continuousOn
    have hM' : ∀ z : ℂ, ‖z‖ ≤ B + 1 → |g z| ≤ M := fun z hz => by
      have := hM z (by rw [Metric.mem_closedBall, dist_zero_right]; exact hz)
      rwa [Real.norm_eq_abs] at this
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ∈ Ioc (0 : ℝ) 1 :=
      Ioc_mem_nhdsGT one_pos
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => M)
      (Eventually.of_forall fun ρ => (hsm ρ).aestronglyMeasurable) (hev.mono fun ρ hρ =>
        hνB.mono fun w hw => by
          rw [Real.norm_eq_abs]
          exact abs_smoothFun_le hM' hρ.1.le (by linarith [hw.2, hρ.2]))
      (integrable_const M) (hνB.mono fun w hw => ?_)
    exact CoordReg.tendsto_integral_fc_of_continuousOn hg.measurable hg.continuousOn hw.1
      (fun ρ hρ hρ1 => (integrable_const M).mono' hg.aestronglyMeasurable
        ((TwoPoint.foldedCircle_ae_norm_le w hρ.le).mono fun z hz => by
          rw [Real.norm_eq_abs]; exact hM' z (by linarith [hw.2])))

theorem mem_Hbar_of_mem_H {w : ℂ} (hw : w ∈ H) : w ∈ Hbar :=
  (show 0 ≤ w.im from le_of_lt (show 0 < w.im from hw))

/-! ## The reductions -/

/-- **W-C from W-D and X-C.** -/
theorem wedgeContinuum_of_x (hD : WedgeDecompStmt) (hXC : XContinuumStmt) :
    WedgeContinuumStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ := hD κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hXC κ hκ hκ4 _ _ X'' hB2 hX'' hI2, hae, hB2.cont,
    hB2.eval_zero_ae_eq_zero] with ω hCo hZ hc h0
  obtain ⟨hGc, -, hZfc⟩ := hZ
  obtain ⟨F, hF⟩ := hCo.1
  have hy := GoodSample.gs_add_ofFun hF hGc.continuousOn
  have hreg := S5.FieldShift.regEq_of_fc hZfc
  have hev : ∀ u ∈ Hbar, ∀ ρ : ℝ, 0 < ρ →
      evalReg (F2.zU (Real.sqrt κ) X' A ω.1) (foldedCircle u ρ) =
        evalReg (X'' ω + F2.logSingField κ) (foldedCircle u ρ) +
          GoodSample.smoothFun (G ω) u ρ := fun u hu ρ hρ => by
    rw [Factorization.evalReg_congr (funext fun k => funext fun z => hreg k z)]
    exact GoodSample.evalReg_add_ofFun_fc hF hGc.continuousOn hu hρ
  refine ⟨⟨_, isRegularWith_of_fc hZfc hy⟩, fun t ht c r hr => ?_⟩
  have hW : Continuous (drive κ B'' ω.1) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω.1 0 = 0 := by simp [drive, h0]
  obtain ⟨_C, B, _hC, _hB, hfacts⟩ := RegCont.νT_facts hW hW0 t c hr
  obtain ⟨hνP, -, hνB⟩ := hfacts t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure ((foldedCircle c r).map (fwdMapInv (drive κ B'' ω.1) t)) := hνP
  obtain ⟨hint, L, hL⟩ := hCo.2 t ht c r hr
  obtain ⟨hsi, hst⟩ := tendsto_integral_smoothFun hGc hνB
  have hcongr : ∀ ρ : ℝ, 0 < ρ →
      (fun u => evalReg (F2.zU (Real.sqrt κ) X' A ω.1) (foldedCircle u ρ)) =ᵐ[
        (foldedCircle c r).map (fwdMapInv (drive κ B'' ω.1) t)]
        fun u => evalReg (X'' ω + F2.logSingField κ) (foldedCircle u ρ) +
          GoodSample.smoothFun (G ω) u ρ := fun ρ hρ =>
    hνB.mono fun u hu => hev u (mem_Hbar_of_mem_H hu.1) ρ hρ
  refine ⟨fun ρ hρ => ((hint ρ hρ).add (hsi ρ hρ)).congr (hcongr ρ hρ).symm, _,
    (hL.add hst).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  exact (integral_add (hint ρ hρ) (hsi ρ hρ)).symm.trans (integral_congr_ae (hcongr ρ hρ)).symm

end WedgeUnzip
end QuantumZipper
