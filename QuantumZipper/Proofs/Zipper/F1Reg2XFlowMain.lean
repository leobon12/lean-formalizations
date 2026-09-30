import QuantumZipper.Proofs.Zipper.F1Reg2XFlowDet
import QuantumZipper.Proofs.Zipper.ZipLen2ContMain
import QuantumZipper.Proofs.Zipper.ZipLen2Flow
import QuantumZipper.Proofs.Zipper.WedgeFlowWDMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# F1-REG-XFLOW (part 2): the free-field flow continuum node `XFlowContStmt`

Main result `xFlowContStmt_holds : XFlowContStmt`.

Route (transfer from the `Γ⁰` node, as `WedgeUnzip.xContinuumStmt_holds` does at `u = 0`):
with `y = 𝔥₀ + X` and `x = X + α₀(−log|·|) = y − √κ log|·|`,

* at every time `u`, centre `v ∈ ℍ̄` and radius `ρ > 0`, the regularized sides satisfy
  `evalReg x_u fc(v, ρ) = evalReg y_u fc(v, ρ) − √κ ∫ log|f_u⁻¹| dfc(v, ρ)` (the identity
  `B3d.ZipLen.evalReg_unzY_flowNu` at the parameter `(u, 0, v, ρ)`, whose pushed circle is
  `fc(v, ρ)` itself), on the full event of `F1.xFlowUCStmt_holds`;
* the smoothed `y`-pairings converge (`B3d.ZipLen.yFlowContStmt_holds`: Duplantier–Sheffield,
  *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1; Revuz–Yor, 3rd ed.,
  Ch. I, Thm (2.1));
* the smoothed log part converges (`XFlowC.flowLogC_tendstoUniformlyOn`).

Own bookkeeping on top of the cited/proved results.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace F1
namespace XFlowC

open RegCont TwoPoint RegUnif

/-- **The free-field flow continuum node.** -/
theorem xFlowContStmt_holds : XFlowContStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [RegUnif.ae_drive_good hB κ,
    RegUnif.ae_forall_isRegularSample (κ := κ) (γ := Real.sqrt κ) hB hX hind,
    ae_all_iff.2 fun n : ℕ => RegUnif.gaugeRegDyStmt_holds (κ := κ) (T := (n : ℝ) + 1)
      hB hX hind (by positivity),
    xFlowUCStmt_holds κ hκ hκ4 P B X hB hX hind,
    B3d.ZipLen.yFlowContStmt_holds κ hκ hκ4 P B X hB hX hind] with ω hdr hreg hgau hUC hYC
  intro u t hu ht c r hr
  obtain ⟨hW, hW0⟩ := hdr
  set W := drive κ B ω with hWdef
  obtain ⟨Lx, hLx⟩ := hUC
  -- the pointwise identity at `fc(v, ρ)`
  have hid : ∀ v ∈ Hbar, ∀ ρ : ℝ, 0 < ρ →
      evalReg (F2.unzX κ (X ω) W u) (foldedCircle v ρ) =
        evalReg (F2.unzY κ (X ω) W u) (foldedCircle v ρ) -
          Real.sqrt κ * ∫ w, Real.log ‖fwdMapInv W u w‖ ∂foldedCircle v ρ := by
    intro v hv ρ hρ
    set p' : ℝ × ℝ × ℂ × ℝ := (u, 0, v, ρ) with hp'def
    have hp' : p' ∈ flowPar := ⟨hu, le_rfl, hv, hρ⟩
    have hν0 : flowNu W p' = foldedCircle v ρ := by
      show (foldedCircle v ρ).map (revMap (B2.vrev W (u + 0)) 0) = foldedCircle v ρ
      have hV := B2.continuous_vrev hW (u + 0)
      have hV0 : B2.vrev W (u + 0) 0 = 0 := by
        simp only [B2.vrev, add_zero, max_self, min_eq_left hu, sub_zero, sub_self]
      rw [Measure.map_congr ((foldedCircle_ae_mem_H v hρ).mono fun z hz =>
        CharFun.revMap_zero_eq hV hV0 hz), Measure.map_id']
    obtain ⟨F, hF⟩ := (hreg u hu).1
    have hR := (hgau ⌈u⌉₊ u ⟨hu, by linarith [Nat.le_ceil u]⟩).1
    have hΦ := hLx.tendsto_at hp'
    obtain ⟨m, hm⟩ := flowBox_mem_nhdsWithin hp'
    have hL := (xFlowLogUCStmt_holds W hW hW0 m).tendsto_at (mem_of_mem_nhdsWithin hp' hm)
    have e := B3d.ZipLen.evalReg_unzY_flowNu κ hW hW0 hp' hR hF hΦ hL
    have e2 : evalReg (F2.unzX κ (X ω) W p'.1) (flowNu W p') = Lx p' := hΦ.limUnder_eq
    rw [← e2, hν0, B3d.ZipLen.unzippedField_cfg_eq] at e
    rw [e]
    ring
  -- the target measure
  set ν := (foldedCircle c r).map (fwdMapInv (shiftDrv W u) t) with hνdef
  have hWs := shiftDrv_continuous hW u
  obtain ⟨_C, Bc, _hC, _hBc, hfacts⟩ := RegCont.νT_facts hWs (shiftDrv_zero W u) t c hr
  obtain ⟨hνP, -, hνB⟩ := hfacts t ⟨ht, le_rfl⟩
  have : IsProbabilityMeasure ν := hνP
  have hνH : ∀ᵐ w ∂ν, w ∈ Hbar ∧ ‖w‖ ≤ Bc :=
    hνB.mono fun w hw => ⟨mem_Hbar_of_H hw.1, hw.2⟩
  -- integrability
  have hYr : IsRegularSample (F2.unzY κ (X ω) W u) := by
    rw [← B3d.ZipLen.unzippedField_cfg_eq]; exact (hreg u hu).1
  have hIY : ∀ ρ : ℝ, 0 < ρ →
      Integrable (fun v => evalReg (F2.unzY κ (X ω) W u) (foldedCircle v ρ)) ν := fun ρ hρ =>
    integrable_smoothed_of_regular hYr hWs (shiftDrv_zero W u) ht c hr hρ
  have hIL : ∀ ρ : ℝ, 0 < ρ →
      Integrable (fun v => ∫ w, Real.log ‖fwdMapInv W u w‖ ∂foldedCircle v ρ) ν := fun ρ hρ =>
    WedgeUnzip.integrable_of_continuousOn_of_carried
      (continuous_integral_log_fwdMapInv hW hW0 hu hρ).continuousOn hνH
  -- the pushed circle is `ν_p`
  set p : ℝ × ℝ × ℂ × ℝ := (u, t, foldH c, r) with hpdef
  have hν : ν = flowNu W p := by
    rw [hνdef]
    unfold flowNu
    simp only [hpdef]
    rw [CoordReg.foldedCircle_foldH c r]
    refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H c hr).mono fun z hz => ?_)
    exact RegUnif.eqOn_fwdMapInv_shift hW hu ht hz
  have hpP : p ∈ flowPar := ⟨hu, ht, CircleFubini.foldH_mem_Hbar' c, hr⟩
  obtain ⟨m, hm⟩ := flowBox_mem_nhdsWithin hpP
  have hLog := (flowLogC_tendstoUniformlyOn hW hW0 m).tendsto_at (mem_of_mem_nhdsWithin hpP hm)
  obtain ⟨LY, hLY⟩ := hYC u t hu ht c r hr
  refine ⟨LY - Real.sqrt κ * ∫ w, Real.log ‖fwdMapInv W p.1 w‖ ∂flowNu W p, ?_⟩
  have hsum := hLY.sub (hLog.const_mul (Real.sqrt κ))
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ)
  have hae : (fun v => evalReg (F2.unzX κ (X ω) W u) (foldedCircle v ρ)) =ᵐ[ν]
      fun v => evalReg (F2.unzY κ (X ω) W u) (foldedCircle v ρ) -
        Real.sqrt κ * ∫ w, Real.log ‖fwdMapInv W u w‖ ∂foldedCircle v ρ :=
    hνH.mono fun v hv => hid v hv.1 ρ hρ
  show _ - Real.sqrt κ * flowLogC W p ρ = _
  rw [integral_congr_ae hae, integral_sub (hIY ρ hρ) ((hIL ρ hρ).const_mul _),
    integral_const_mul, flowLogC, ← hν]

end XFlowC
end F1
end QuantumZipper
