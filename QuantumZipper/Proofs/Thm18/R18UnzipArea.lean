import QuantumZipper.Proofs.Zipper.LocLenPStarArea
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.Zipper.SWCoreB8FAll
import QuantumZipper.Proofs.Thm18.R18Nodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T3: the area coordinate change in the unzipping direction, for the Theorem 1.8 wedge

Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop 2.1
(`literature/0808.1560.txt` lines 488–495): `μ_{h∘ψ+Q log|ψ'|} = ψ⁻¹_* μ_h`; for all unzipping
maps simultaneously, Sheffield–Wang, arXiv:1605.06171, Thm 1.4. For the unscaled wedge this is the
proved node `E6.WedgeAreaCoordStmt` (`PStarAreaCoord.lean:55`, via
`E6.wedgeAreaCoordStmt_of_split` and the SW merge statements). This file transfers it to the
canonical (`P_*`) wedge and to the Theorem 1.8 variables, following the transfer of
`LocLen.pStarAreaAll_of_off` (`LocLenPStarArea.lean`): realization `WedgeUnzip.pStarRealizeStmt_holds`,
the unzipped canonical field is the rescaled unzipped unscaled field
(`WedgeUnzip.unzippedField_canonConfig_fc`), the rescaling rule of the area
(`LocLen.qAreaMeasure_rescale_of_area`) and the Loewner scaling `RS.fwdMapInv_scale`.

Main results: `R18.pStarUnzipArea_holds : R18.PStarUnzipAreaStmt`,
`R18.unzipArea_holds : R18.UnzipAreaStmt` (task T3 of `handoff/R18-PLAN.md`). Wiring of proved
nodes plus own elementary set bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Unzipping area rule, `P_*` form**: a.s., for all `t ≥ 0` and Borel `S ⊆ ℍ`, the quantum area
of the unzipped field at `S` is the quantum area of the field at `f_t⁻¹(S)`. -/
def PStarUnzipAreaStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t → ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) S =
        qAreaMeasure (Real.sqrt κ) (Y ω) (fwdMapInv (drive κ B' ω) t '' S)

/-- **Unzipping area rule, Theorem 1.8 variables** (T3). -/
def UnzipAreaStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ S : Set ℂ, MeasurableSet S → S ⊆ H →
      qAreaMeasure γ (unzippedField γ (wedgeConfig γ B Y ω) t) S =
        qAreaMeasure γ (Y ω) (fwdMapInv (drive (γ ^ 2) B ω) t '' S)

/-- `z ↦ z / a` is a measurable embedding of `ℂ` (`a > 0`). -/
theorem measurableEmbedding_div_ofReal {a : ℝ} (ha : 0 < a) :
    MeasurableEmbedding fun z : ℂ => z / (a : ℂ) := by
  have hc : ((a : ℂ))⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 ha.ne')
  have h := measurableEmbedding_mulRight₀ hc
  convert h using 1
  funext z
  simp [div_eq_mul_inv]

/-- The set bookkeeping of the scaling: `{z | z/a ∈ φ '' S} = ψ '' {w | w/a ∈ S}` when
`a · φ w = ψ (a w)` on `S`. -/
theorem preimage_div_image_eq {a : ℝ} (ha : 0 < a) {φ ψ : ℂ → ℂ} {S : Set ℂ}
    (hsc : ∀ w ∈ S, (a : ℂ) * φ w = ψ ((a : ℂ) * w)) :
    (fun z : ℂ => z / (a : ℂ)) ⁻¹' (φ '' S) = ψ '' ((fun z : ℂ => z / (a : ℂ)) ⁻¹' S) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  ext z
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨w, hw, hwz⟩
    refine ⟨(a : ℂ) * w, by rwa [mul_div_cancel_left₀ _ ha'], ?_⟩
    rw [← hsc w hw, hwz, mul_div_cancel₀ _ ha']
  · rintro ⟨w', hw', hwz⟩
    refine ⟨w' / (a : ℂ), hw', ?_⟩
    have h := hsc _ hw'
    rw [mul_div_cancel₀ _ ha', hwz] at h
    rw [← h, mul_div_cancel_left₀ _ ha']

/-- **T3, `P_*` form.** -/
theorem pStarUnzipArea_holds : PStarUnzipAreaStmt := by
  intro κ Ω' _ P' _ Y B' hP
  obtain ⟨hκ, hκ4, -⟩ := id hP
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hAU := SWCore.wedgeAreaMergeUnifStmt_of_continuum
    (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
      WedgeUnzip.xContinuumStmt_holds)
  have hK : E6.WedgeAreaCoordStmt := E6.wedgeAreaCoordStmt_of_split
    (E6.wedgeAreaMergeFixStmt_of_unif hAU) (E6.wedgeAreaEquiStmt_of_unif hAU)
  have hG := LocLen.wedgeGoodOffAll_of_yMergeOffTip hYO
  have hE := LocLen.wedgeExactAll_of_yMergeOffTip hYO
  have hC := WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
    WedgeUnzip.xContinuumStmt_holds
  obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hInd, hB, hIB, hae⟩ :=
    WedgeUnzip.pStarRealizeStmt_holds κ P' Y B' hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα := F2.alpha_lt_Qc' hγ hγ2
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hae, hG κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    hE κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    hC κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    hK κ hκ hκ4 _ X' A B'' hX hA hInd hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hInd,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα _ _ _ X' A inferInstance hX hA hInd,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hRω hGω hEω hCω hKω hspec hZg hc h0
  obtain ⟨havg, hcfg⟩ := hRω
  intro t ht S hSm hSH
  set Z := F2.zU (Real.sqrt κ) X' A ω with hZ
  set a := scaleParam (Real.sqrt κ) Z with ha_def
  have ha : 0 < a := hspec.1
  have hWc : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  have hWmax := F2.drive_max κ B'' ω
  have has : 0 ≤ a ^ 2 * t := mul_nonneg (sq_nonneg _) ht
  -- the unzipped field of the canonical configuration is the rescaled unzipped unscaled field
  have hraw := WedgeUnzip.unzippedField_canonConfig_fc hWc hW0 hWmax ha ht (fun d r hr => by
      rw [B3d.canonConfig_snd_of_max hWmax]
      have hC' := hCω.2 _ has ((a : ℂ) * d) _ (mul_pos ha hr)
      exact WedgeUnzip.scaleConsistent_of_continuum hCω.1 _ hWc hW0 ha ht d hr hC'.1 hC'.2)
    (hEω _ has)
  have hfield : unzippedField (Real.sqrt κ) (Y ω.1, drive κ B' ω.1) t =
      unzippedField (Real.sqrt κ) (canonConfig (Real.sqrt κ) (Z, drive κ B'' ω)) t := by
    rw [hcfg]
    exact Factorization.coordChange_congr havg _ _
  have hq : qAreaMeasure (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω.1, drive κ B' ω.1) t) =
      qAreaMeasure (Real.sqrt κ)
        (rescale (unzippedField (Real.sqrt κ) (Z, drive κ B'' ω) (a ^ 2 * t))
          (Qc (Real.sqrt κ)) a) := by
    rw [hfield]
    exact Factorization.qAreaMeasure_congr (E6.avgReg_eq_of_coords_eq'
      (WedgeUnzip.coords_eq_of_fc fun d _ r hr => hraw d r hr)) _
  -- the driver of `Y` is the Brownian rescaling of the unscaled driver
  have hdrv : drive κ B' ω.1 = fun r => drive κ B'' ω (a ^ 2 * r) / a := by
    have h2 := congrArg Prod.snd hcfg
    simp only at h2
    rw [← h2, B3d.canonConfig_snd_of_max hWmax]
  have hemb := measurableEmbedding_div_ofReal ha
  have hdivH : (fun z : ℂ => z / (a : ℂ)) ⁻¹' S ⊆ H := by
    intro z hz
    have h1 : 0 < (z / (a : ℂ)).im := hSH hz
    rw [Complex.div_ofReal_im] at h1
    exact (div_pos_iff_of_pos_right ha).1 h1
  have hdivm : MeasurableSet ((fun z : ℂ => z / (a : ℂ)) ⁻¹' S) :=
    (measurable_id.div_const _) hSm
  -- left side
  rw [hq, LocLen.qAreaMeasure_rescale_of_area (hGω _ has).1 (hGω _ has).2.2 hγ ha,
    hemb.map_apply, hKω _ has _ hdivm hdivH]
  -- right side
  have hY : qAreaMeasure (Real.sqrt κ) (Y ω.1) =
      (qAreaMeasure (Real.sqrt κ) Z).map fun z : ℂ => z / (a : ℂ) := by
    rw [Factorization.qAreaMeasure_congr havg]
    exact LocLen.qAreaMeasure_rescale_of_area hZg.1 hZg.2.2 hγ ha
  rw [hY, hemb.map_apply, hdrv]
  congr 1
  refine (preimage_div_image_eq ha fun w hw => ?_).symm
  rw [RS.fwdMapInv_scale hWc hW0 ha ht (hSH hw)]
  exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 ha.ne')

/-- **T3, Theorem 1.8 variables.** -/
theorem unzipArea_holds : UnzipAreaStmt := by
  intro γ Ω _ P _ B Y hS
  have h := pStarUnzipArea_holds (γ ^ 2) P Y B (isPStarSample_of_setting hS)
  rw [Real.sqrt_sq hS.1.le] at h
  exact h

end R18
end QuantumZipper
