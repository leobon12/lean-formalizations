import QuantumZipper.Proofs.Zipper.LocLenCanonRegCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5e: `E6.PStarAreaAllStmt` without global boundary goodness (D75)

Theorem 1.3, node E6 area (`HitScaleZip.lean`): a.s., for all `t ≥ 0`, the quantum area measure
of the unzipped `P_*` field is finite on every half-disc `B_a(0) ∩ ℍ` and infinite on `ℍ`.
Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §5.4, pp. 70–72; the area
coordinate-change rule is Duplantier–Sheffield, *Liouville quantum gravity and KPZ*
(arXiv:0808.1560), Prop. 2.1, and the area side of the welding is Sheffield–Wang
(arXiv:1605.06171), Thm 1.4.

This is a copy of `E6.pStarAreaAllStmt_of_core` (`PStarAreaAll.lean`) in which the only use of
global goodness `IsLQGGood` of the unscaled unzipped fields (through `E6.areaAll_rescale_iff`)
is replaced by the area-only data: regularity and the area limit, which are the `.1` and `.2.2`
components of `LocLen.IsLQGGoodOff` (the boundary part is not used for an area statement).
The wedge area nodes come from the proved area coordinate-change rule (as in
`LocLen.wedgeUnzipScalePos_holds`), and the remaining D29 inputs are the proved off-tip closed
forms `LocLen.wedgeGoodOffAll_of_yMergeOffTip`, `LocLen.wedgeExactAll_of_yMergeOffTip`, and
`WedgeUnzip.wedgeContinuum_of_x`.
-/

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open D3Plus MeasUnzip E6

/-- The area measure of a regular sample with an area limit is its area limit. -/
theorem qAreaMeasure_spec_of_area {γ : ℝ} {x : FieldSample} (hr : IsRegularSample x)
    (hμ : ∃ μ, HasAreaLimit γ x μ) : HasAreaLimit γ x (qAreaMeasure γ x) := by
  obtain ⟨μ, hμ⟩ := hμ
  rwa [GoodSample.qAreaMeasure_eq_of_hasAreaLimit hr hμ]

/-- `GoodTransforms.qAreaMeasure_rescale` from regularity and the area limit only. -/
theorem qAreaMeasure_rescale_of_area {γ : ℝ} {x : FieldSample} (hr : IsRegularSample x)
    (hμ : ∃ μ, HasAreaLimit γ x μ) (hγ : 0 < γ) {b : ℝ} (hb : 0 < b) :
    qAreaMeasure γ (rescale x (Qc γ) b) = (qAreaMeasure γ x).map fun z : ℂ => z / (b : ℂ) :=
  GoodSample.qAreaMeasure_eq_of_hasAreaLimit (hr.rescale' (Qc γ) hb)
    (GoodTransforms.hasAreaLimit_rescale hr hγ (qAreaMeasure_spec_of_area hr hμ) hb)

/-- **`AreaAll` is rescaling invariant** (`E6.areaAll_rescale_iff` with `IsLQGGood` weakened to
regularity and the area limit). -/
theorem areaAll_rescale_iff_of_area {γ : ℝ} {x : FieldSample} (hr : IsRegularSample x)
    (hμ : ∃ μ, HasAreaLimit γ x μ) (hγ : 0 < γ) {b : ℝ} (hb : 0 < b) :
    AreaAll γ (rescale x (Qc γ) b) ↔ AreaAll γ x := by
  have hmeas : Measurable fun z : ℂ => z / (b : ℂ) := measurable_id.div_const _
  have hball : ∀ a : ℝ, qAreaMeasure γ (rescale x (Qc γ) b) (Metric.ball 0 a ∩ H) =
      qAreaMeasure γ x (Metric.ball 0 (a * b) ∩ H) := fun a => by
    rw [qAreaMeasure_rescale_of_area hr hμ hγ hb,
      Measure.map_apply hmeas (AreaProfile.measurableSet_ball_inter_H a),
      GoodTransforms.preimage_div_ball_inter_H hb]
  have hH : qAreaMeasure γ (rescale x (Qc γ) b) H = qAreaMeasure γ x H := by
    rw [qAreaMeasure_rescale_of_area hr hμ hγ hb, Measure.map_apply hmeas isOpen_H.measurableSet]
    congr 1
    ext z
    show 0 < (z / (b : ℂ)).im ↔ 0 < z.im
    rw [Complex.div_ofReal_im]
    exact div_pos_iff_of_pos_right hb
  have hfin : (∀ a : ℝ, qAreaMeasure γ (rescale x (Qc γ) b) (Metric.ball 0 a ∩ H) < ⊤) ↔
      (∀ a : ℝ, qAreaMeasure γ x (Metric.ball 0 a ∩ H) < ⊤) := by
    constructor
    · intro h a
      have h1 := h (a / b)
      rwa [hball (a / b), div_mul_cancel₀ a hb.ne'] at h1
    · intro h a
      rw [hball a]
      exact h (a * b)
  simp only [AreaAll, hfin, hH]

/-- **`E6.PStarAreaAllStmt` from the off-tip goodness core** (copy of
`E6.pStarAreaAllStmt_of_core` with `WedgeGoodAllStmt ↦ WedgeGoodOffAllStmt`). -/
theorem pStarAreaAll_of_off (hR : WedgeUnzip.PStarRealizeStmt) (hG : WedgeGoodOffAllStmt)
    (hE : WedgeUnzip.WedgeExactAllStmt) (hC : WedgeUnzip.WedgeContinuumStmt)
    (hAf : WedgeAreaFinStmt) (hAi : WedgeAreaHStmt) : PStarAreaAllStmt := by
  intro κ Ω' _ P' _ Y B' hP
  obtain ⟨hκ, hκ4, -⟩ := id hP
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hInd, hB, hIB, hae⟩ := hR κ P' Y B' hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hG κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    hE κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    hC κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    hAf κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    hAi κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hInd,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hRω hGω hEω hCω hFω hNω hspec hc h0
  obtain ⟨havg, hcfg⟩ := hRω
  intro t ht
  set Z := F2.zU (Real.sqrt κ) X' A ω
  have ha : 0 < scaleParam (Real.sqrt κ) Z := hspec.1
  have hWc : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  have hWmax := F2.drive_max κ B'' ω
  have has : 0 ≤ scaleParam (Real.sqrt κ) Z ^ 2 * t := mul_nonneg (sq_nonneg _) ht
  have hraw := WedgeUnzip.unzippedField_canonConfig_fc hWc hW0 hWmax ha ht (fun d r hr => by
      rw [B3d.canonConfig_snd_of_max hWmax]
      have hC' := hCω.2 _ has ((scaleParam (Real.sqrt κ) Z : ℂ) * d) _ (mul_pos ha hr)
      exact WedgeUnzip.scaleConsistent_of_continuum hCω.1 _ hWc hW0 ha ht d hr hC'.1 hC'.2)
    (hEω _ has)
  have hfield : unzippedField (Real.sqrt κ) (Y ω.1, drive κ B' ω.1) t =
      unzippedField (Real.sqrt κ) (canonConfig (Real.sqrt κ) (Z, drive κ B'' ω)) t := by
    rw [hcfg]
    exact Factorization.coordChange_congr havg _ _
  have hq : qAreaMeasure (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω.1, drive κ B' ω.1) t) =
      qAreaMeasure (Real.sqrt κ)
        (rescale (unzippedField (Real.sqrt κ) (Z, drive κ B'' ω)
          (scaleParam (Real.sqrt κ) Z ^ 2 * t)) (Qc (Real.sqrt κ)) (scaleParam (Real.sqrt κ) Z)) := by
    rw [hfield]
    exact Factorization.qAreaMeasure_congr (avgReg_eq_of_coords_eq'
      (WedgeUnzip.coords_eq_of_fc fun d _ r hr => hraw d r hr)) _
  exact (areaAll_congr hq).2 ((areaAll_rescale_iff_of_area (hGω _ has).1 (hGω _ has).2.2 hγ ha).2
    ⟨hFω _ has, hNω _ has⟩)

/-- **`E6.PStarAreaAllStmt` from the offset merge statement only** (no TipCore, no TIP-X, no
global boundary goodness). -/
theorem pStarAreaAll_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) : PStarAreaAllStmt := by
  have hAU := SWCore.wedgeAreaMergeUnifStmt_of_continuum
    (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
      WedgeUnzip.xContinuumStmt_holds)
  have hK : E6.WedgeAreaCoordStmt := E6.wedgeAreaCoordStmt_of_split
    (E6.wedgeAreaMergeFixStmt_of_unif hAU) (E6.wedgeAreaEquiStmt_of_unif hAU)
  exact pStarAreaAll_of_off WedgeUnzip.pStarRealizeStmt_holds (wedgeGoodOffAll_of_yMergeOffTip hYO)
    (wedgeExactAll_of_yMergeOffTip hYO)
    (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
      WedgeUnzip.xContinuumStmt_holds)
    (E6.wedgeAreaFinStmt_of_coord hK) (E6.wedgeAreaHStmt_of_coord hK)

end LocLen
end QuantumZipper
