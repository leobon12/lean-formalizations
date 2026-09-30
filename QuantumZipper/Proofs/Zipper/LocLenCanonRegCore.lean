import QuantumZipper.Proofs.Zipper.LocLenF1Flow
import QuantumZipper.Proofs.Zipper.LocLenPStarGood
import QuantumZipper.Proofs.Zipper.WedgeCocycleCanon
import QuantumZipper.Proofs.Zipper.WedgeFlowWDMain
import QuantumZipper.Proofs.Zipper.PStarAreaCoord
import QuantumZipper.Proofs.Zipper.AreaCoord
import QuantumZipper.Proofs.Zipper.SWCoreA8Main
import QuantumZipper.Proofs.Zipper.F1Reg2XFlowMain
import QuantumZipper.Proofs.Zipper.XFlowClose

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6b-2 (part 1): the wedge flow core with goodness off the root images

Sheffield arXiv:1012.4797 §1.4 and pp. 69–72 (the canonical description of the unzipped field
at every time; goodness is only needed away from the tip and the root images); Berestycki–Powell
arXiv:2404.16642 Def 6.41 p. 229 (boundary length on open arcs).

Local copies (global goodness `IsLQGGood` replaced by `IsLQGGoodOff … (offSet W t)`; where the
old proof only used regularity, `.1` of the local version is used):
* `isLQGGoodOff_of_fc_Hbar` (copy of `F1.isLQGGood_of_fc_Hbar`);
* `scaleParam_rescale_off` (copy of `GoodTransforms.scaleParam_rescale`: only regularity and the
  area limit are used);
* `wedgeFlowContStmt_of_xOff`, `wedgeFlowRC3Stmt_of_xOff` (copies of `F1.wedgeFlowContStmt_of_x`,
  `F1.wedgeFlowRC3Stmt_of_x`: X-G enters only through regularity);
* `FlowScaleCoreOff`, `UnscaledFlowCoreOffStmt`, `unscaledFlowCoreOff_of_wedgeFlow`
  (copy of `F1.unscaledFlowCoreStmt_of_wedgeFlow`), `unscaledFlowCoreOff_of_yMergeOffTip`;
* `pstar_flow_fc_off` (copy of `F1.pstar_flow_fc`, which reads only the first two clauses);
* **`wedgeUnzipScalePos_holds : F1.WedgeUnzipScalePosStmt`**, proved outright: the unscaled
  unzipped wedge field has finite area near `0` and infinite total area (`AreaAll`, from the
  proved area-coordinate node), hence a positive scale (`E6.scaleParam_pos_of_area`); no goodness.
Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal Pointwise

namespace QuantumZipper
namespace LocLen

open F1

/-- Raw agreement on folded circles transfers goodness off `S` (copy of
`F1.isLQGGood_of_fc_Hbar`). -/
theorem isLQGGoodOff_of_fc_Hbar {γ : ℝ} {x y : FieldSample} {S : Set ℝ}
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r))
    (hy : IsLQGGoodOff γ y S) : IsLQGGoodOff γ x S := by
  have hav : avgReg x = avgReg y :=
    funext fun k => funext fun z => regEq_of_fc_Hbar h k z
  have he := Factorization.evalReg_congr hav
  have ha : areaR γ x = areaR γ y := by
    funext r; unfold areaR areaDens; rw [he]
  obtain ⟨hreg, ⟨ν, hν⟩, ⟨μ, hμ⟩⟩ := hy
  refine ⟨isRegularSample_of_fc_Hbar h hreg, ⟨ν, (hasBdryLimitOn_congr_avg hav).2 hν⟩, ⟨μ, ?_⟩⟩
  unfold HasAreaLimit at hμ ⊢; rw [ha]; exact hμ

/-- `scaleParam γ (rescale x Q b) = scaleParam γ x / b` from regularity and the area limit only
(copy of `GoodTransforms.scaleParam_rescale`). -/
theorem scaleParam_rescale_off {γ : ℝ} {x : FieldSample} (hx : IsRegularSample x)
    {μ : Measure ℂ} (hμ : HasAreaLimit γ x μ) (hγ : 0 < γ) {b : ℝ} (hb : 0 < b) :
    scaleParam γ (rescale x (Qc γ) b) = scaleParam γ x / b := by
  have hq : qAreaMeasure γ (rescale x (Qc γ) b) =
      (qAreaMeasure γ x).map fun z : ℂ => z / (b : ℂ) := by
    rw [GoodSample.qAreaMeasure_eq_of_hasAreaLimit (hx.rescale' (Qc γ) hb)
      (GoodTransforms.hasAreaLimit_rescale hx hγ hμ hb),
      GoodSample.qAreaMeasure_eq_of_hasAreaLimit hx hμ]
  unfold scaleParam
  rw [hq]
  have hmeas : Measurable (fun z : ℂ => z / (b : ℂ)) := measurable_id.div_const _
  have e : {a : ℝ | 0 < a ∧ 1 ≤ ((qAreaMeasure γ x).map fun z : ℂ => z / (b : ℂ))
      (Metric.ball (0 : ℂ) a ∩ H)} =
      b⁻¹ • {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ x (Metric.ball (0 : ℂ) a ∩ H)} := by
    ext a
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hb.ne'), inv_inv, smul_eq_mul]
    simp only [mem_setOf_eq]
    rw [Measure.map_apply hmeas (Metric.isOpen_ball.inter isOpen_H).measurableSet,
      GoodTransforms.preimage_div_ball_inter_H hb, mul_comm b a]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨mul_pos h1 hb, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨pos_of_mul_pos_left h1 hb.le, h2⟩
  rw [e, Real.sInf_smul_of_nonneg (inv_nonneg.2 hb.le), smul_eq_mul, div_eq_inv_mul]

/-- **`WedgeFlowRC3Stmt` from X-G off the root images** (copy of `F1.wedgeFlowRC3Stmt_of_x`). -/
theorem wedgeFlowRC3Stmt_of_xOff (hXG : XGoodOffAllStmt)
    (hXC : WedgeUnzip.XContinuumStmt) (hXR : XFlowRC3Stmt) (hXF : XFlowContStmt) :
    WedgeFlowRC3Stmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hXG κ hκ hκ4 _ _ X'' hB2 hX'' hI2, hXC κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    hXR κ hκ hκ4 _ _ X'' hB2 hX'' hI2, hXF κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 _ _ hB2, hae, hB2.cont,
    hB2.eval_zero_ae_eq_zero] with ω hGo hCo hRo hFo hCa hZ hc h0
  obtain ⟨hGc, -, hZfc⟩ := hZ
  intro u s hu hs d hd r hr
  have hW : Continuous (drive κ B'' ω.1) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω.1 0 = 0 := by simp [drive, h0]
  exact flow_rc3_transfer (Real.sqrt κ) hW hW0 hGc hCo.1 hZfc hu hs (hCa u hu)
    (fun d _ r hr => hCo.2 u hu d r hr) (fun d _ r hr => hCo.2 (u + s) (add_nonneg hu hs) d r hr)
    (hGo u hu).1 (fun d _ r hr => ⟨fun ρ hρ => integrable_smoothed_of_regular (hGo u hu).1
      (shiftDrv_continuous hW u) (shiftDrv_zero _ u) hs d hr hρ, hFo u s hu hs d r hr⟩)
    hd hr (hRo u s hu hs d hd r hr)

/-- **`WedgeFlowContStmt` from X-G off the root images** (copy of `F1.wedgeFlowContStmt_of_x`). -/
theorem wedgeFlowContStmt_of_xOff (hXG : XGoodOffAllStmt)
    (hXC : WedgeUnzip.XContinuumStmt) (hXF : XFlowContStmt) : WedgeFlowContStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ :=
    WedgeUnzip.WDec.wedgeDecompStmt_holds κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hXG κ hκ hκ4 _ _ X'' hB2 hX'' hI2, hXC κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    hXF κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 _ _ hB2, hae, hB2.cont,
    hB2.eval_zero_ae_eq_zero] with ω hGo hCo hFo hCa hZ hc h0
  obtain ⟨hGc, -, hZfc⟩ := hZ
  intro u t hu ht c r hr
  have hW : Continuous (drive κ B'' ω.1) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω.1 0 = 0 := by simp [drive, h0]
  exact flow_cont_transfer (Real.sqrt κ) hW hW0 hGc hCo.1 hZfc hu (hCa u hu)
    (fun d _ r hr => hCo.2 u hu d r hr) (hGo u hu).1 ht c hr
    ⟨fun ρ hρ => integrable_smoothed_of_regular (hGo u hu).1 (shiftDrv_continuous hW u)
      (shiftDrv_zero _ u) ht c hr hρ, hFo u t hu ht c r hr⟩

/-- `F1.FlowScaleCore` with goodness off the root images of the full time. -/
def FlowScaleCoreOff (γ : ℝ) (y : FieldSample) (W : ℝ → ℝ) (u s : ℝ) : Prop :=
  (∀ (d : ℂ) (r : ℝ), 0 < r → Thm18Asm.G1.ScaleConsistentAt
      (zipCapDown γ (scaleParam γ y ^ 2 * u) (y, W)).1 (Qc γ) (scaleParam γ y)
      ((foldedCircle d r).map (fwdMapInv (fun r =>
        (zipCapDown γ (scaleParam γ y ^ 2 * u) (y, W)).2 (scaleParam γ y ^ 2 * r) /
          scaleParam γ y) s))) ∧
  (∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField γ (zipCapDown γ (scaleParam γ y ^ 2 * u) (y, W))
          (scaleParam γ y ^ 2 * s)) (foldedCircle d r) =
        unzippedField γ (zipCapDown γ (scaleParam γ y ^ 2 * u) (y, W))
          (scaleParam γ y ^ 2 * s) (foldedCircle d r)) ∧
  IsLQGGoodOff γ (unzippedField γ (zipCapDown γ (scaleParam γ y ^ 2 * u) (y, W))
      (scaleParam γ y ^ 2 * s)) (offSet W (scaleParam γ y ^ 2 * u + scaleParam γ y ^ 2 * s))

/-- `F1.UnscaledFlowCoreStmt` with `FlowScaleCoreOff`. -/
def UnscaledFlowCoreOffStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
      FlowScaleCoreOff (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) (drive κ B'' ω) u s

/-- **The wedge flow core off the root images** (copy of `F1.unscaledFlowCoreStmt_of_wedgeFlow`). -/
theorem unscaledFlowCoreOff_of_wedgeFlow (hG : WedgeGoodOffAllStmt)
    (hE : WedgeUnzip.WedgeExactAllStmt) (hR : WedgeFlowRC3Stmt) (hC : WedgeFlowContStmt) :
    UnscaledFlowCoreOffStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  filter_upwards [hG κ hκ hκ4 P X' A B'' hX hA hI hB hIB, hE κ hκ hκ4 P X' A B'' hX hA hI hB hIB,
    hR κ hκ hκ4 P X' A B'' hX hA hI hB hIB, hC κ hκ hκ4 P X' A B'' hX hA hI hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hI,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hGω hEω hRω hCω hspec hc h0 u s hu hs
  set γ := Real.sqrt κ
  set y := F2.zU γ X' A ω
  set W := drive κ B'' ω
  set a := scaleParam γ y
  have ha : 0 < a := hspec.1
  have hW : Continuous W := by
    show Continuous (drive κ B'' ω)
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [W, drive, h0]
  have hU : 0 ≤ a ^ 2 * u := mul_nonneg (sq_nonneg a) hu
  have hS : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) hs
  have hraw : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      unzippedField γ (zipCapDown γ (a ^ 2 * u) (y, W)) (a ^ 2 * s) (foldedCircle d r) =
        unzippedField γ (y, W) (a ^ 2 * u + a ^ 2 * s) (foldedCircle d r) :=
    fun d hd r hr => flow_raw_cocycle_of_rc3 γ y hW hW0 hU hS d hr
      (hRω _ _ hU hS d hd r hr)
  have hUS : 0 ≤ a ^ 2 * u + a ^ 2 * s := add_nonneg hU hS
  refine ⟨fun d r hr => ?_, fun d hd r hr => ?_, isLQGGoodOff_of_fc_Hbar hraw (hGω _ hUS)⟩
  · set c'' := zipCapDown γ (a ^ 2 * u) (y, W)
    have hW'' : Continuous c''.2 :=
      (hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub
        continuous_const
    have hW''0 : c''.2 0 = 0 := by simp [c'', zipCapDown]
    have hC' := hCω _ _ hU (mul_nonneg (sq_nonneg a) hs) ((a : ℂ) * d) (a * r) (mul_pos ha hr)
    exact WedgeUnzip.scaleConsistent_of_continuum (hGω _ hU).1 _ hW'' hW''0 ha hs d hr
      hC'.1 hC'.2
  · have hreg := regEq_of_fc_Hbar hraw
    have hav : avgReg (unzippedField γ (zipCapDown γ (a ^ 2 * u) (y, W)) (a ^ 2 * s)) =
        avgReg (unzippedField γ (y, W) (a ^ 2 * u + a ^ 2 * s)) :=
      funext fun k => funext fun z => hreg k z
    rw [Factorization.evalReg_congr hav, hEω _ hUS d hd r hr, hraw d hd r hr]

/-- **The wedge flow core off the root images, closed form** (no TipCore, no TIP-X). -/
theorem unscaledFlowCoreOff_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    UnscaledFlowCoreOffStmt :=
  unscaledFlowCoreOff_of_wedgeFlow (wedgeGoodOffAll_of_yMergeOffTip hYO)
    (wedgeExactAll_of_yMergeOffTip hYO)
    (wedgeFlowRC3Stmt_of_xOff (xGoodOffAll_of_yMergeOffTip hYO) WedgeUnzip.xContinuumStmt_holds
      xFlowRC3Stmt_holds XFlowC.xFlowContStmt_holds)
    (wedgeFlowContStmt_of_xOff (xGoodOffAll_of_yMergeOffTip hYO) WedgeUnzip.xContinuumStmt_holds
      XFlowC.xFlowContStmt_holds)

/-- **Positive scale of the unzipped wedge fields, proved outright** (no goodness): the
area-coordinate node (from the proved uniform area merge) gives `AreaAll` of the unscaled
unzipped field at all times, and `E6.scaleParam_pos_of_area`. -/
theorem wedgeUnzipScalePos_holds : F1.WedgeUnzipScalePosStmt := by
  have hAU := SWCore.wedgeAreaMergeUnifStmt_of_continuum
    (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
      WedgeUnzip.xContinuumStmt_holds)
  have hK : E6.WedgeAreaCoordStmt := E6.wedgeAreaCoordStmt_of_split
    (E6.wedgeAreaMergeFixStmt_of_unif hAU) (E6.wedgeAreaEquiStmt_of_unif hAU)
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  filter_upwards [E6.ae_areaAll_unzipped_of_coord hK hκ hκ4 P X' A B'' hX hA hI hB hIB]
    with ω h t ht
  exact E6.scaleParam_pos_of_area (h t ht).1 (h t ht).2

end LocLen
end QuantumZipper
