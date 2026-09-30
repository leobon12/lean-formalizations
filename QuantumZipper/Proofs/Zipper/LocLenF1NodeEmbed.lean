import QuantumZipper.Proofs.Zipper.LocLenStmtsF1Node
import QuantumZipper.Proofs.Zipper.F1Embed
import QuantumZipper.Proofs.Zipper.LocLenF1NodeAB
import QuantumZipper.Proofs.Zipper.LocLenF2Unscaled
import QuantumZipper.Proofs.Zipper.LocLenF2Loc
import QuantumZipper.Proofs.Zipper.LocLenR6cCap
import QuantumZipper.Proofs.Zipper.LocLenR2bRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6e-C: the embedding step `F1EmbedArcStmt`

Open-arc copy (`unzipLengths ↦ unzipLengthsArc`) of `F1.f1EmbedStmt_of` (F1Embed.lean:50) and of
its helpers `F1.pstar_ratio_law`, `F1.ae_unzipLengths_transfer`, `F1.pstar_pos_all`
(F1EmbedBasic.lean).

Source: Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, §5.4 p. 71 (F1c: the 0-1 law is run on the unscaled wedge) and §5.1 pp. 60–62
(B3(d): the canonical description is the unscaled one rescaled by the random scale `a`).
Positivity of the left open-arc length at positive times is Sheffield p. 56 (the boundary
measure charges every nonempty open boundary arc), `PStarBdryPosAllArcStmt`.

Inputs: `WedgeUnzip.YMergeOffTipStmt` (B3(d) locally, the measurable reader, goodness,
positivity), and the open Arc statements `LenPairCocycleArcStmt` (R6a), `LenFiniteArcStmt` (X1),
which give finiteness of the left open-arc length at all times (`ae_unzipLengthsArc_lt_top_all`);
finiteness is needed at the random times `1/((m+1) a²)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- The open-arc length ratio `L⁺₁/L⁻₁` of the configuration `(Y, √κ B)`. -/
abbrev ratio1Arc (κ : ℝ) {Ω : Type} (Y : Ω → FieldSample) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  lenRatio (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B ω) 1)

theorem ratio1Arc_ae_eq_read {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ratio1Arc κ Y B =ᵐ[P] fun ω =>
      lenRatio (readLenArc (Real.sqrt κ) (cfgData (Y ω, drive κ B ω))) := by
  filter_upwards [hB.cont] with ω hω
  simp only [ratio1Arc]
  rw [unzipLengthsArc_eq_readCfg _ (continuous_drive_of κ hω) (fun s => drive_toNNReal κ B ω s)]
  rfl

/-- Open-arc copy of `F1.pstar_ratio_law`: the ratio of a `P_*` sample is read from the
configuration law. -/
theorem pstar_ratio_lawArc {κ : ℝ}
    (hR : ReadLenAEMeasArcStmt (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) κ) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {Y : Ω → FieldSample}
    {B : ℝ≥0 → Ω → ℝ} (h : Thm13Asm.IsPStarSample κ P Y B) :
    AEMeasurable (ratio1Arc κ Y B) P ∧
      P.map (ratio1Arc κ Y B) =
        (configLawFull (pcfg κ Y B) P).map fun d => lenRatio (readLenArc (Real.sqrt κ) d) := by
  obtain ⟨hκ, hκ4, hW, hB, hI⟩ := h
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα := F2.alpha_lt_Qc' hγ hγ2
  have hY : AEMeasurable (fun ω => dataH (Y ω)) P :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW
  have hBm := IsBrownianReal.aemeasurable_pathOf hB
  have hc : AEMeasurable (fun ω => cfgData (Y ω, drive κ B ω)) P :=
    aemeasurable_cfgData_drive κ hY hBm
  have hr : AEMeasurable (readLenArc (Real.sqrt κ)) (configLawFull (pcfg κ Y B) P) :=
    hR hκ hκ4 rfl hα Ω P Y B inferInstance hW hB hY hBm hI.symm
  have hF : AEMeasurable (fun d => lenRatio (readLenArc (Real.sqrt κ) d))
      (P.map fun ω => cfgData (Y ω, drive κ B ω)) :=
    measurable_lenRatio.comp_aemeasurable hr
  refine ⟨(hF.comp_aemeasurable hc).congr (ratio1Arc_ae_eq_read hB).symm, ?_⟩
  rw [Measure.map_congr (ratio1Arc_ae_eq_read hB), configLawFull_eq_map_cfgData,
    AEMeasurable.map_map_of_aemeasurable hF hc]
  rfl

/-- Open-arc copy of `F1.ae_unzipLengths_transfer` (B3(d), from the local input
`UnscaledB3dLocStmt`): the open-arc lengths of the canonical `P_*` sample at time `s` are those
of the unscaled configuration at time `a² s`. -/
theorem ae_unzipLengthsArc_transfer (hD : UnscaledB3dLocStmt) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X' : Ω → FieldSample} {A : ℝ → Ω → ℝ} {B'' : ℝ≥0 → Ω → ℝ}
    (hX : IsFreeGFFModConstH X' P)
    (hA : IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P)
    (hI : IndepFun X' (fun ω t => A t ω) P) (hB : IsBrownianReal B'' P)
    (hIB : IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P) :
    ∀ᵐ ω ∂P, 0 < scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ∧ ∀ s, 0 ≤ s →
      unzipLengthsArc (Real.sqrt κ) ((FSMeas.xiU (Real.sqrt κ) X' A ω).1,
          drive κ (F2.rscale (F2.sqScale ∘ FSMeas.xiU (Real.sqrt κ) X' A) B'') ω) s =
        unzipLengthsArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)
          (scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2 * s) := by
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  obtain ⟨-, hcfgae⟩ := FSMeas.pstar_of_unscaled_fs hκ hκ4 hX hA hI hB hIB
  filter_upwards [hcfgae, hD κ hκ hκ4 P X' A B'' hX hA hI hB hIB,
    RS.ae_real_alive hB hκ hκ4.le, B5.ae_forall_sideImages_sign hκ hκ4 hB]
    with ω hcfg hDω halive hsign
  obtain ⟨ha, hY, hdr⟩ := hcfg
  refine ⟨ha, fun s hs => ?_⟩
  set Z := F2.zU γ X' A with hZ
  set a := scaleParam γ (Z ω) with ha_def
  have hsf : ∀ (x : FieldSample) (W : ℝ → ℝ) (r : ℝ),
      unzipLengthsArc γ (FSMeas.sfTrunc x, W) r = unzipLengthsArc γ (x, W) r := fun x W r =>
    unzipLengthsArc_congr_avgReg γ (FSMeas.avgReg_sfTrunc x) W r
  have hcc2 : (canonConfig γ (Z ω, drive κ B'' ω)).2 =
      fun r => drive κ B'' ω (a ^ 2 * r) / a :=
    B3d.canonConfig_snd_of_max (F1.drive_max κ B'' ω)
  rw [hY, hdr, hsf, hcc2]
  obtain ⟨l₁, l₂, hl₁, hl₂⟩ := F1.exists_tendsto_sideImages_of_alive (W := drive κ B'' ω)
    (t := a ^ 2 * s) (by positivity) fun x hx => halive x hx _ (by positivity)
  have hfield := hDω.2 s hs
  have hcc : canonConfig γ (Z ω, drive κ B'' ω) =
      (canonical γ (Z ω), fun r => drive κ B'' ω (a ^ 2 * r) / a) :=
    Prod.ext rfl hcc2
  rw [hcc] at hfield
  exact unzipLengthsArc_scale_off hγ ha hs ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ (hsign _ (by positivity))
    (hDω.1 _ (by positivity)) hfield

/-- Open-arc copy of `F1.pstar_pos_all`: `0 < L⁻_t < ⊤` at all positive times for `P_*`
samples. Positivity: the left open arc `(O⁻_t, 0)` is nonempty and the boundary measure charges
it (Sheffield p. 56, `PStarBdryPosAllArcStmt`); finiteness: `ae_unzipLengthsArc_lt_top_all`. -/
theorem pstar_pos_allArc (hPG : PStarGoodOffAllStmt) (hPos : PStarBdryPosAllArcStmt)
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) {κ : ℝ} {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → FieldSample}
    {B' : ℝ≥0 → Ω' → ℝ} (h : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', ∀ t : ℝ, 0 < t → 0 < (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).1 ∧
      (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).1 < ⊤ := by
  filter_upwards [hPG κ P' Y B' h, hPos κ P' Y B' h, ae_pstar_zeroMinus_facts h,
    ae_unzipLengthsArc_lt_top_all hC hF κ P' Y B' h, h.2.2.2.1.cont,
    h.2.2.2.1.eval_zero_ae_eq_zero] with ω hg hpos hz hf hcB h0 t ht
  refine ⟨?_, (hf t ht.le).1⟩
  have hW : Continuous (drive κ B' ω) := continuous_drive_of κ hcB
  have hW0 : drive κ B' ω 0 = 0 := by simp [drive, h0]
  obtain ⟨-, hanti, hz0, hO, -⟩ := hz t ht
  obtain ⟨hr, ⟨ν, hν⟩, -⟩ := hg t ht.le
  have hl0 : (sideImages (drive κ B' ω) t).1 < 0 := by
    have := hanti ⟨le_rfl, ht.le⟩ ⟨ht.le, le_rfl⟩ ht
    rwa [hz0, ← hO] at this
  have hsub : Ioo (sideImages (drive κ B' ω) t).1 0 ⊆ (offSet (drive κ B' ω) t)ᶜ :=
    fun u hu hu' => disjoint_left.1
      (Ioo_left_disjoint_offSet _ t (sideImages_snd_nonneg_of_cont hW hW0 ht.le)) hu hu'
  have hp := hpos t ht _ 0 le_rfl hl0 le_rfl
  rw [qBoundaryMeasureOn_eq_of_hasBdryLimitOn hr (isClosed_offSet _ t).isOpen_compl hν] at hp
  show 0 < arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t)
    (sideImages (drive κ B' ω) t).1 0
  rw [arcLen_eq_of_hasBdryLimitOn hr hν hsub]
  exact hp

/-- **The embedding step of F1c with open arcs** (`F1EmbedArcStmt`; open-arc copy of
`F1.f1EmbedStmt_of`, Sheffield arXiv:1012.4797 §5.4 p. 71 and §5.1 pp. 60–62), from the offset
merging input and finiteness of the open-arc lengths (`LenPairCocycleArcStmt`,
`LenFiniteArcStmt`). -/
theorem f1EmbedArc_of (hYO : WedgeUnzip.YMergeOffTipStmt) (hC : LenPairCocycleArcStmt)
    (hF : LenFiniteArcStmt) : F1EmbedArcStmt := by
  have hD : UnscaledB3dLocStmt := unscaledB3dLoc_of_yMergeOffTip hYO
  have hR := readLenAEMeasArc_of_yMergeOffTip hYO
  have hPG : PStarGoodOffAllStmt := pStarGoodOffAll_of_yMergeOffTip hYO
  have hPos : PStarBdryPosAllArcStmt :=
    pStarBdryPosAllArc_of_core WedgeUnzip.pStarRealizeStmt_holds (yGoodOffAll_of_yMergeOffTip hYO)
      (wedgeGoodOffAll_of_yMergeOffTip hYO) (wedgeExactAll_of_yMergeOffTip hYO)
      (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
        WedgeUnzip.xContinuumStmt_holds) hPG
  intro hall κ Ω' _ P' _ Y B' h
  obtain ⟨hφ, hlawY⟩ := pstar_ratio_lawArc (hR κ) h
  refine ⟨hφ, ?_⟩
  have hP := h
  obtain ⟨hκ, hκ4, hW, hB', hIY⟩ := h
  set γ := Real.sqrt κ with hγdef
  have hγ : 0 < γ := Real.sqrt_pos.2 hκ
  have hγ2 : γ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hα : γ - 2 / γ < Qc γ := F2.alpha_lt_Qc' hγ hγ2
  obtain ⟨-, Ω₁, _, P₁, X, A, hP₁, hX, hA, hI, hlaw⟩ := hW
  obtain ⟨C₁, C₂, hC₁, hC₂, hC₁₂, hAC⟩ := hA
  obtain ⟨b₁, hb₁m, hb₁c, hb₁B, hb₁e⟩ := exists_meas_brownian_version hC₁
  obtain ⟨b₂, hb₂m, hb₂c, hb₂B, hb₂e⟩ := exists_meas_brownian_version hC₂
  obtain ⟨b, hbm, -, hbB, -⟩ := exists_meas_brownian_version hB'
  set A₀ : ℝ → Ω₁ → ℝ := fun t ω =>
    wedgePath (γ - 2 / γ) (Qc γ) (fun s => b₁ s ω) (fun s => b₂ s ω) t with hA₀def
  have hA₀m : ∀ t, Measurable (A₀ t) := fun t =>
    (WedgeMeas.measurable_wedgePath_joint (γ - 2 / γ) (Qc γ) hb₁c hb₂c hb₁m hb₂m).comp
      (measurable_id.prodMk measurable_const)
  have hb₁₂ : IndepFun (pathOf b₁) (pathOf b₂) P₁ := hC₁₂.congr hb₁e.symm hb₂e.symm
  have hA₀ : IsWedgeProcess (γ - 2 / γ) (Qc γ) A₀ P₁ := ⟨b₁, b₂, hb₁B, hb₂B, hb₁₂, fun ω t => rfl⟩
  have hAA₀ : (fun ω t => A t ω) =ᵐ[P₁] fun ω t => A₀ t ω := by
    filter_upwards [hb₁e, hb₂e] with ω h1 h2
    funext t
    rw [hAC ω t]
    exact congrArg₂ (fun u v => wedgePath (γ - 2 / γ) (Qc γ) u v t) h1.symm h2.symm
  have hI₀ : IndepFun X (fun ω t => A₀ t ω) P₁ := hI.congr (ae_eq_refl _) hAA₀
  have hlaw₀ : fieldLawFull H Y P' =
      fieldLawFull H (fun ω => canonical γ (F2.zU γ X A₀ ω)) P₁ := by
    rw [hlaw]
    unfold fieldLawFull
    refine Measure.map_congr ?_
    filter_upwards [hAA₀] with ω h
    have h' : (fun t => A t ω) = fun t => A₀ t ω := h
    rw [h']
  set Xp : Ω₁ × Ω' → FieldSample := fun ω => X ω.1 with hXpdef
  set Ap : ℝ → Ω₁ × Ω' → ℝ := fun t ω => A₀ t ω.1 with hApdef
  set Bp : ℝ≥0 → Ω₁ × Ω' → ℝ := fun t ω => b t ω.2 with hBpdef
  have hXp : IsFreeGFFModConstH Xp (P₁.prod P') := NonVacuity.nv_freeGFF measurePreserving_fst hX
  have hAp : IsWedgeProcess (γ - 2 / γ) (Qc γ) Ap (P₁.prod P') :=
    ⟨fun t ω => b₁ t ω.1, fun t ω => b₂ t ω.1,
      NonVacuity.nv_isBrownianReal measurePreserving_fst hb₁B,
      NonVacuity.nv_isBrownianReal measurePreserving_fst hb₂B,
      NonVacuity.nv_indepFun_fst hb₁₂, fun ω t => rfl⟩
  have hBp : IsBrownianReal Bp (P₁.prod P') :=
    NonVacuity.nv_isBrownianReal measurePreserving_snd hbB
  have hApm : ∀ t, Measurable (Ap t) := fun t => (hA₀m t).comp measurable_fst
  have hBpm : ∀ t, Measurable (Bp t) := fun t => (hbm t).comp measurable_snd
  have hIp : IndepFun Xp (fun ω t => Ap t ω) (P₁.prod P') := NonVacuity.nv_indepFun_fst hI₀
  have hIBp : IndepFun (fun ω => (Xp ω, fun t => Ap t ω)) (pathOf Bp) (P₁.prod P') :=
    NonVacuity.nv_indepFun_prod (fun ω₁ => (X ω₁, fun t => A₀ t ω₁)) (pathOf b)
  obtain ⟨hPS, hcfg⟩ := FSMeas.pstar_of_unscaled_fs hκ hκ4 hXp hAp hIp hBp hIBp
  set Y₀ : Ω₁ × Ω' → FieldSample := fun ω => (FSMeas.xiU γ Xp Ap ω).1 with hY₀def
  set B₀ := F2.rscale (F2.sqScale ∘ FSMeas.xiU γ Xp Ap) Bp with hB₀def
  obtain ⟨f₀, hf₀⟩ := hall κ (P₁.prod P') Y₀ B₀ hPS
  have htr := ae_unzipLengthsArc_transfer hD hκ hκ4 hXp hAp hIp hBp hIBp
  have hpos₀ := pstar_pos_allArc hPG hPos hC hF hPS
  refine ⟨Ω₁ × Ω', inferInstance, P₁.prod P', Xp, Ap, Bp, f₀, inferInstance, hXp, hAp, hBp,
    hApm, hBpm, iIndep_srcSigma_of hIp hIBp, ?_, ?_, ?_⟩
  · filter_upwards [htr, hf₀] with ω hω hf t ht
    obtain ⟨ha, hω⟩ := hω
    have ha2 : 0 < scaleParam γ (F2.zU γ Xp Ap ω) ^ 2 := by positivity
    have hs : 0 ≤ t / scaleParam γ (F2.zU γ Xp Ap ω) ^ 2 := div_nonneg ht ha2.le
    have e : scaleParam γ (F2.zU γ Xp Ap ω) ^ 2 * (t / scaleParam γ (F2.zU γ Xp Ap ω) ^ 2) = t :=
      mul_div_cancel₀ _ ha2.ne'
    have key := hω _ hs
    rw [e] at key
    show (unzipLengthsArc γ (F2.zU γ Xp Ap ω, drive κ Bp ω) t).2 =
      f₀ ω * (unzipLengthsArc γ (F2.zU γ Xp Ap ω, drive κ Bp ω) t).1
    rw [← key]
    exact hf _ hs
  · filter_upwards [htr, hpos₀] with ω hω hp m
    obtain ⟨ha, hω⟩ := hω
    have ht : (0 : ℝ) < (GermZeroOne.epsSeq m : ℝ) := NNReal.coe_pos.2 (GermZeroOne.epsSeq_pos m)
    have ha2 : 0 < scaleParam γ (F2.zU γ Xp Ap ω) ^ 2 := by positivity
    have hs : 0 < (GermZeroOne.epsSeq m : ℝ) / scaleParam γ (F2.zU γ Xp Ap ω) ^ 2 :=
      div_pos ht ha2
    have e : scaleParam γ (F2.zU γ Xp Ap ω) ^ 2 *
        ((GermZeroOne.epsSeq m : ℝ) / scaleParam γ (F2.zU γ Xp Ap ω) ^ 2) =
        (GermZeroOne.epsSeq m : ℝ) :=
      mul_div_cancel₀ _ ha2.ne'
    have key := hω _ hs.le
    rw [e] at key
    show 0 < (unzipLengthsArc γ (F2.zU γ Xp Ap ω, drive κ Bp ω) (GermZeroOne.epsSeq m : ℝ)).1 ∧
      (unzipLengthsArc γ (F2.zU γ Xp Ap ω, drive κ Bp ω) (GermZeroOne.epsSeq m : ℝ)).1 < ⊤
    rw [← key]
    exact hp _ hs
  · have hg : (P₁.prod P').map f₀ = (P₁.prod P').map (ratio1Arc κ Y₀ B₀) := by
      refine Measure.map_congr ?_
      filter_upwards [hf₀, hpos₀] with ω hf hp
      exact (lenRatio_eq_of (hf 1 zero_le_one) (hp 1 one_pos).1 (hp 1 one_pos).2).symm
    have hW₀ : IsQuantumWedge γ (γ - 2 / γ) (fun ω => canonical γ (F2.zU γ X A₀ ω)) P₁ :=
      ⟨hα, Ω₁, _, P₁, X, A₀, hP₁, hX, hA₀, hI₀, rfl⟩
    have hfl : fieldLawFull H Y₀ (P₁.prod P') = fieldLawFull H Y P' := by
      rw [FSMeas.fieldLawFull_congr_sfTrunc (Y := Y₀)
        (Y' := fun ω => canonical γ (F2.zU γ Xp Ap ω)) (hcfg.mono fun ω h => h.2.1) H, hlaw₀]
      exact NonVacuity.nv_map_comp measurePreserving_fst
        (Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hW₀)
    calc P'.map (ratio1Arc κ Y B') = (configLawFull (pcfg κ Y B') P').map
          (fun d => lenRatio (readLenArc γ d)) := hlawY
      _ = (configLawFull (pcfg κ Y₀ B₀) (P₁.prod P')).map
          (fun d => lenRatio (readLenArc γ d)) := by
          rw [configLawFull_pstar_eq hP hPS hfl.symm]
      _ = (P₁.prod P').map (ratio1Arc κ Y₀ B₀) := (pstar_ratio_lawArc (hR κ) hPS).2.symm
      _ = (P₁.prod P').map f₀ := hg.symm

end LocLen
end QuantumZipper
