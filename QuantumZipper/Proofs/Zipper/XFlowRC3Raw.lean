import QuantumZipper.Proofs.Zipper.XFlowRC3Fix
import QuantumZipper.Proofs.Zipper.RegShiftUnifBasic
import QuantumZipper.Proofs.Zipper.WedgeXExact
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame
import QuantumZipper.Proofs.GFF.CoordRegLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X-FLOW-RC3: the raw-side continuity from the regularized side and a deterministic input

The raw side of the flow node is, by the definition of the unzipped field (`coordChange`) and the
flow of the inverse forward maps (`fwdMapInv_shiftDrv_comp`: `f_u⁻¹ ∘ R_{u,s} = f_{u+s}⁻¹` on `ℍ`),

`x_u(ν_p) = evalReg x ((f_{u+s}⁻¹)_* fc(d, r)) + Q ∫ log|(f_u⁻¹)'| dν_p`,

and the first term is the regularized side at the parameter `(0, u + s, d, r)` as soon as `x`
is exact at the enumerated folded circles (then `x_0` and `x` have the same `avgReg`,
`RegUnif.raw_unzip_zero_eq`), which holds a.s. at the countably many enumerated circles
(Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1, through
`CoordReg.ae_evalReg_logAdd_eq_frostman`). Hence (own bookkeeping):

* `flowRawSide_eq`: the pathwise identity;
* `xFlowRawContStmt_of_reg : XFlowRegContStmt → FlowLogDerContStmt → XFlowRawContStmt`, where
  `FlowLogDerContStmt` is the purely deterministic continuity of
  `p ↦ ∫ log|(f_u⁻¹)'| dν_p` on `flowPar` for every continuous driver with `W 0 = 0`;
* `xFlowRC3Stmt_of_regCont : XFlowRegContStmt → FlowLogDerContStmt → XFlowRC3Stmt` (with the
  proved fixed-parameter node `xFlowRC3FixStmt_holds`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- **(Deterministic input.)** For every continuous driver with `W 0 = 0`, the log-derivative
term `p ↦ ∫ log|(f_u⁻¹)'| dν_p` of the unzipped field at the pushed circle is continuous on
`flowPar`. -/
def FlowLogDerContStmt : Prop :=
  ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 →
    ContinuousOn (fun p : ℝ × ℝ × ℂ × ℝ =>
      ∫ z, Real.log ‖deriv (fwdMapInv W p.1) z‖ ∂flowNu W p) flowPar

/-- The time-`u` inverse forward map composed with `R_{u,s}` is `f_{u+s}⁻¹ = revMap _ (u+s)`
on `ℍ`. -/
theorem fwdMapInv_revMap_comp {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {u s : ℝ}
    (hu : 0 ≤ u) (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ H) :
    fwdMapInv W u (revMap (B2.vrev W (u + s)) s z) =
      revMap (B2.vrev W (0 + (u + s))) (u + s) z := by
  have hE : fwdMapInv (shiftDrv W u) s z = revMap (B2.vrev W (u + s)) s z :=
    RegUnif.eqOn_fwdMapInv_shift hW hu hs hz
  rw [← hE, (fwdMapInv_shiftDrv_comp hW hW0 hu hs hz).2,
    CoordReg.eqOn_fwdMapInv hW hW0 (add_nonneg hu hs) hz]
  refine ReverseFlow.revMap_congr_drive z fun q hq => ?_
  rw [B2.vrev_of_mem ⟨hq.1, by linarith [hq.2]⟩, zero_add]

/-- **Pathwise raw-side identity.** If `x = X + α₀(−log|·|)` is exact at the enumerated folded
circles, then at every `p ∈ flowPar` the raw side is the regularized side at `(0, u+s, d, r)` plus
`Q` times the log-derivative term. -/
theorem flowRawSide_eq (κ : ℝ) {X : FieldSample} {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hfix : ∀ i : ℕ, evalReg (X + F2.logSingField κ)
        (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (X + F2.logSingField κ) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2))
    {p : ℝ × ℝ × ℂ × ℝ} (hp : p ∈ flowPar) :
    flowRawSide κ X W p = flowRegSide κ X W (0, p.1 + p.2.1, p.2.2.1, p.2.2.2) +
      Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (fwdMapInv W p.1) z‖ ∂flowNu W p := by
  obtain ⟨u, s, d, r⟩ := p
  obtain ⟨hu, hs, -, hr⟩ := hp
  simp only at hu hs hr ⊢
  set x := X + F2.logSingField κ with hx
  have hV : Continuous (B2.vrev W (u + s)) := B2.continuous_vrev hW _
  have hRm : Measurable (revMap (B2.vrev W (u + s)) s) := TwoPoint.measurable_revMap hV hs
  set V' : ℝ → ℝ := fun q => W (u - q) - W u with hV'
  have hV'c : Continuous V' := by rw [hV']; fun_prop
  have hEu : EqOn (fwdMapInv W u) (revMap V' u) H := CoordReg.eqOn_fwdMapInv hW hW0 hu
  have hνH : ∀ᵐ z ∂flowNu W (u, s, d, r), z ∈ H :=
    (ae_map_iff hRm.aemeasurable isOpen_H.measurableSet).2
      ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => TwoPoint.im_revMap_pos hV hz hs)
  -- the pushed measure under `f_u⁻¹`
  have hmap : (flowNu W (u, s, d, r)).map (revMap V' u) =
      (foldedCircle d r).map (revMap (B2.vrev W (0 + (u + s))) (u + s)) := by
    unfold flowNu
    simp only
    rw [Measure.map_map (TwoPoint.measurable_revMap hV'c hu) hRm]
    refine Measure.map_congr ((TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz => ?_)
    have hRz : revMap (B2.vrev W (u + s)) s z ∈ H := TwoPoint.im_revMap_pos hV hz hs
    simp only [Function.comp_apply]
    rw [← hEu hRz, fwdMapInv_revMap_comp hW hW0 hu hs hz]
  -- raw side
  have hraw : flowRawSide κ X W (u, s, d, r) =
      evalReg x ((foldedCircle d r).map (revMap (B2.vrev W (0 + (u + s))) (u + s))) +
        Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (fwdMapInv W u) z‖ ∂flowNu W (u, s, d, r) := by
    have h1 : flowRawSide κ X W (u, s, d, r) =
        coordChange x (fwdMapInv W u) (Qc (Real.sqrt κ)) (flowNu W (u, s, d, r)) := rfl
    have h2 : coordChange x (revMap V' u) (Qc (Real.sqrt κ)) (flowNu W (u, s, d, r)) =
        evalReg x ((flowNu W (u, s, d, r)).map (revMap V' u)) +
          Qc (Real.sqrt κ) * ∫ z, Real.log ‖deriv (revMap V' u) z‖ ∂flowNu W (u, s, d, r) := rfl
    have hder : ∫ z, Real.log ‖deriv (revMap V' u) z‖ ∂flowNu W (u, s, d, r) =
        ∫ z, Real.log ‖deriv (fwdMapInv W u) z‖ ∂flowNu W (u, s, d, r) := by
      refine integral_congr_ae (hνH.mono fun z hz => ?_)
      have := Filter.EventuallyEq.deriv_eq
        (Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hz) hEu)
      simp only [this]
    rw [h1, CoordReg.coordChange_congr_of_eqOn_H x hEu _ hνH, h2, hmap, hder]
  -- regularized side at `(0, u + s, d, r)`
  have hreg : flowRegSide κ X W (0, u + s, d, r) =
      evalReg x ((foldedCircle d r).map (revMap (B2.vrev W (0 + (u + s))) (u + s))) := by
    have havg : ∀ k z, avgReg (unzippedField (Real.sqrt κ) (x, W) 0) k z = avgReg x k z := by
      intro k z
      unfold avgReg
      congr 1
      funext n
      exact (RegUnif.raw_unzip_zero_eq (Real.sqrt κ) hW hW0 hfix n k z).symm
    exact WedgeUnzip.evalReg_congr_avgReg havg _
  rw [hraw, hreg]

/-- **`XFlowRawContStmt` from `XFlowRegContStmt` and the deterministic input.** -/
theorem xFlowRawContStmt_of_reg (hR : XFlowRegContStmt) (hD : FlowLogDerContStmt) :
    XFlowRawContStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hfix : ∀ᵐ ω ∂P, ∀ i : ℕ, evalReg (X ω + F2.logSingField κ)
      (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) =
      (X ω + F2.logSingField κ) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2) := by
    refine ae_all_iff.2 fun i => ?_
    have hr := UnzipFull.fullIndex_radius_pos i
    have h := CoordReg.ae_evalReg_logAdd_eq_frostman hX
      (ν := foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)
      (CircleFubini.foldedCircle_support hr.le le_rfl)
      (Cor15Group.isFrostman_fc _ hr) one_pos (-(Real.sqrt κ - 2 / Real.sqrt κ))
      (g₁ := fun _ => (0 : ℝ)) continuousOn_const
    refine h.mono fun ω hω => ?_
    rw [logSing_eq_logAdd]
    exact hω
  filter_upwards [hR κ hκ hκ4 P B X hB hX hind, hfix, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hRω hfω hc h0
  have hW : Continuous (drive κ B ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  have hmaps : MapsTo (fun p : ℝ × ℝ × ℂ × ℝ => ((0 : ℝ), p.1 + p.2.1, p.2.2.1, p.2.2.2))
      flowPar flowPar := fun p hp => ⟨le_rfl, add_nonneg hp.1 hp.2.1, hp.2.2.1, hp.2.2.2⟩
  have hcomp : ContinuousOn (fun p : ℝ × ℝ × ℂ × ℝ =>
      flowRegSide κ (X ω) (drive κ B ω) ((0 : ℝ), p.1 + p.2.1, p.2.2.1, p.2.2.2)) flowPar :=
    hRω.comp (by fun_prop : Continuous fun p : ℝ × ℝ × ℂ × ℝ =>
      ((0 : ℝ), p.1 + p.2.1, p.2.2.1, p.2.2.2)).continuousOn hmaps
  refine (hcomp.add ((hD _ hW hW0).const_smul (Qc (Real.sqrt κ)))).congr fun p hp => ?_
  rw [flowRawSide_eq κ hW hW0 hfω hp]
  rfl

/-- **`XFlowRC3Stmt` from the regularized-side continuity and the deterministic input** (the
fixed-parameter node is proved, `xFlowRC3FixStmt_holds`). -/
theorem xFlowRC3Stmt_of_regCont (hR : XFlowRegContStmt) (hD : FlowLogDerContStmt) :
    XFlowRC3Stmt :=
  xFlowRC3Stmt_of_fix_cont xFlowRC3FixStmt_holds hR (xFlowRawContStmt_of_reg hR hD)

/-- **X-X from the same two inputs.** -/
theorem xExactAll_of_regCont (hR : XFlowRegContStmt) (hD : FlowLogDerContStmt) :
    WedgeUnzip.XExactAllStmt :=
  xExactAll_of_xFlowRC3 (xFlowRC3Stmt_of_regCont hR hD)

end F1
end QuantumZipper
