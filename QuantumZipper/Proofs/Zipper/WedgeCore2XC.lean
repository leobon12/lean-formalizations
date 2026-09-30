import QuantumZipper.Proofs.Zipper.WedgeCore2Y
import QuantumZipper.Proofs.Zipper.ZipLen2ContMain
import QuantumZipper.Proofs.Zipper.ScaleGeomIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# WEDGE-CORE: `XContinuumStmt` (X-C) proved from the continuous-radius `Γ⁰` flow node

X-C asks, a.s., that `x = X + α₀(−log|·|)` be a regular sample and that for all `t ≥ 0`, `c`,
`r > 0` the smoothed pairings `ρ ↦ ∫ evalReg x (fc(u, ρ)) d((f_t⁻¹)_* fc(c, r))(u)` be integrable
and converge as `ρ → 0⁺` (continuous radius).

The continuous-radius Kolmogorov–Čentsov statement for the `Γ⁰` field is proved
(`B3d.ZipLen.yFlowContStmt_holds`, ZipLen2Cont*.lean: Revuz–Yor, 3rd ed., Ch. I, Thm (2.1);
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1). Its case `u = 0` is the continuum
limit for the time-`0` unzipped `Γ⁰` field, which has the `avgReg` of `y = 𝔥₀ + X` (exactness at the
enumerated circles), hence the same smoothed pairings. Then (own bookkeeping, deterministic):

* `y = X + Lf(−2/√κ)` and `x = X + Lf(α₀)` (`α₀ = √κ − 2/√κ`), so for `u ∈ ℍ̄`, `ρ > 0`,
  `evalReg x fc(u, ρ) = evalReg (y + Lf(√κ)) fc(u, ρ)` (`LogSingGood.evalReg_add_Lf_fc`);
* the continuum limit survives adding `Lf(√κ)` (`F2.continuum_add_Lf`, Frostman rate).

Main result: `xContinuumStmt_holds : XContinuumStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- `α₀(−log|·|)` is the log function `Lf α₀`. -/
theorem add_logSingField_eq_Lf (κ : ℝ) (x : FieldSample) :
    x + F2.logSingField κ = x + ofFun (LogSingGood.Lf (Real.sqrt κ - 2 / Real.sqrt κ)) := rfl

/-- **Pathwise X-C at one pushed circle**, from the continuous-radius `Γ⁰` limit at `u = 0`. -/
theorem xCont_pathwise (κ : ℝ) {X : FieldSample} {FX : ℂ × ℝ → ℝ} (hFX : IsRegularWith X FX)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hfy : ∀ i : ℕ, evalReg (ofFun (h0rev κ) + X)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (ofFun (h0rev κ) + X) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    {t : ℝ} (ht : 0 ≤ t) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hY : ∃ L : ℝ, Tendsto (fun ρ => ∫ v, evalReg (F2.unzY κ X W 0) (foldedCircle v ρ)
        ∂((foldedCircle c r).map (fwdMapInv (F1.shiftDrv W 0) t))) (𝓝[>] 0) (𝓝 L)) :
    (∀ ρ : ℝ, 0 < ρ → Integrable (fun u => evalReg (X + F2.logSingField κ) (foldedCircle u ρ))
      ((foldedCircle c r).map (fwdMapInv W t))) ∧
    ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg (X + F2.logSingField κ) (foldedCircle u ρ)
      ∂((foldedCircle c r).map (fwdMapInv W t))) (𝓝[>] 0) (𝓝 L) := by
  set ν := (foldedCircle c r).map (fwdMapInv W t) with hν
  set β : ℝ := -(2 / Real.sqrt κ) with hβ
  have hWs : Continuous (F1.shiftDrv W 0) :=
    (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub continuous_const
  have hEq : EqOn (F1.shiftDrv W 0) W (Icc 0 t) := fun s hs => by
    simp [F1.shiftDrv, max_eq_left hs.1, hW0]
  have hsh : (foldedCircle c r).map (fwdMapInv (F1.shiftDrv W 0) t) = ν :=
    Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H c hr).mono fun z hz =>
      RegCont.fwdMapInv_congr hWs (F1.shiftDrv_zero W 0) hW hW0 hEq ⟨ht, le_rfl⟩ hz)
  have hy_eq : ofFun (h0rev κ) + X = X + ofFun (LogSingGood.Lf β) := F2.sgin_h0rev_add_eq_Lf κ X
  have hFy := LogSingGood.regular_add_Lf hFX β
  obtain ⟨_C, Bc, _hC, _hBc, hfacts⟩ := RegCont.νT_facts hW hW0 t c hr
  obtain ⟨hP, -, hνB⟩ := hfacts t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure ν := hP
  have hνH : ∀ᵐ w ∂ν, w ∈ Hbar ∧ ‖w‖ ≤ Bc :=
    hνB.mono fun w hw => ⟨show w ∈ Hbar from (show (0 : ℝ) < w.im from hw.1).le, hw.2⟩
  -- the `Γ⁰` limit, rewritten for `y = X + Lf β`
  have hLy : ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg (X + ofFun (LogSingGood.Lf β))
      (foldedCircle u ρ) ∂ν) (𝓝[>] 0) (𝓝 L) := by
    obtain ⟨L, hL⟩ := hY
    refine ⟨L, ?_⟩
    rw [hsh] at hL
    have e : ∀ (v : ℂ) (ρ : ℝ), evalReg (F2.unzY κ X W 0) (foldedCircle v ρ) =
        evalReg (X + ofFun (LogSingGood.Lf β)) (foldedCircle v ρ) := by
      intro v ρ
      rw [unzY_eq_h0, evalReg_unzip_zero_eq hW hW0 hfy, hy_eq]
    simpa only [e] using hL
  have hint_y : ∀ ρ : ℝ, 0 < ρ → Integrable
      (fun u => evalReg (X + ofFun (LogSingGood.Lf β)) (foldedCircle u ρ)) ν := by
    intro ρ hρ
    have hg : ContinuousOn (fun u : ℂ => (fun q => FX q + β * (CircleCont.circPot q.2 q.1 0 / 2))
        (u, ρ)) Hbar :=
      hFy.1.comp (Continuous.continuousOn (continuous_id.prodMk continuous_const))
        (fun u hu => ⟨hu, hρ⟩)
    refine (integrable_of_continuousOn_of_carried hg hνH).congr ?_
    filter_upwards [hνH] with u hu
    exact (hFy.evalReg_fc_of_mem hu.1 hρ).symm
  obtain ⟨hI, L, hL⟩ := F2.continuum_add_Lf hFy (Real.sqrt κ) hW hW0 ht c hr hint_y hLy
  have hev : ∀ ρ : ℝ, 0 < ρ →
      (fun u => evalReg ((X + ofFun (LogSingGood.Lf β)) + ofFun (LogSingGood.Lf (Real.sqrt κ)))
        (foldedCircle u ρ)) =ᵐ[ν] fun u => evalReg (X + F2.logSingField κ) (foldedCircle u ρ) := by
    intro ρ hρ
    filter_upwards [hνH] with u hu
    rw [LogSingGood.evalReg_add_Lf_fc hFy _ hu.1 hρ, LogSingGood.evalReg_add_Lf_fc hFX _ hu.1 hρ,
      add_logSingField_eq_Lf, LogSingGood.evalReg_add_Lf_fc hFX _ hu.1 hρ, hβ]
    ring
  refine ⟨fun ρ hρ => (hI ρ hρ).congr (hev ρ hρ), L, hL.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  exact integral_congr_ae (hev ρ hρ)

/-- **`XContinuumStmt` (X-C) holds.** -/
theorem xContinuumStmt_holds : XContinuumStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [ae_core2Y_inputs hκ hκ4 hB hX hind, ae_isRegularSample_xLogSing hX κ,
    RegSample.ae_isRegularSample hX, B3d.ZipLen.yFlowContStmt_holds κ hκ hκ4 P B X hB hX hind]
    with ω hin hx hXr hYC
  obtain ⟨hW, hW0, -, -, -, -, hfy⟩ := hin
  refine ⟨hx, fun t ht c r hr => ?_⟩
  obtain ⟨FX, hFX⟩ := hXr
  exact xCont_pathwise κ hFX hW hW0 hfy ht c hr (hYC 0 t le_rfl ht c r hr)

end WedgeUnzip
end QuantumZipper
