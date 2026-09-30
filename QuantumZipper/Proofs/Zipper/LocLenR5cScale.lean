import QuantumZipper.Proofs.Zipper.LocLenR5cPStar
import QuantumZipper.Proofs.Zipper.LocLenStmtsF1Node
import QuantumZipper.Proofs.Zipper.LocLenF1Flow
import QuantumZipper.Proofs.Zipper.LocLenF2Step4
import QuantumZipper.Proofs.Zipper.LocLenPStarGood
import QuantumZipper.Proofs.Zipper.LocLenPosMain
import QuantumZipper.Proofs.Zipper.HitScaleZipScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5c (D75): the open-arc left-length nodes from scaling, and `HitScaleZipArcStmt`

Open-arc copy (`handoff/FOLLOW-PAPER-13.md`, task R5c) of `HitScaleZipScale.lean`
(`E6.pStarLenInfStmt_of`, `E6.pStarLenStartStmt_of`, `E6.hitScaleZipStmt_of_scaling`), with
`unzipLengths ↦ unzipLengthsArc`, `F1.PStarZipLenInputsStmt ↦ PStarZipLenInputsLocStmt`,
`F1.LenReadTimeStmt ↦ LenReadTimeArcStmt`, `F1.LenStrictMonoStmt ↦ LenStrictMonoArcStmt`,
`Thm18Asm.UnzipBdryPosStmt ↦ UnzipBdryPosArcStmt`. The only new input is `LenFiniteArcStmt`
(X1, `P_*` form): the old proof used that closed-arc lengths are finite by construction
(`F1.unzipLengths_fst_lt_top`); open-arc lengths are finite by X1 (B-P p. 285 "L(1) < ∞").

Sheffield arXiv:1012.4797, §5.4, p. 71 ("by scaling"); the zero–infinity argument from scale
invariance in law is own elementary work, as for the originals.

Local copies (distinct names, to avoid clashes with the parallel R6e files):
`unzipLengthsArc_eq_readCfg_r5c`, `unzipLengthsArc_canon_addConst_r5c`, `pstar_pos_one_arc_r5c`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen
namespace R5c

section Copies

open F1

/-- Copy of `F1.unzipLengths_eq_readCfg` for open arcs. -/
theorem unzipLengthsArc_eq_readCfg_r5c (γ : ℝ) {c : FieldSample × (ℝ → ℝ)}
    (hW : Continuous c.2) (hW0 : ∀ s, c.2 s = c.2 (s.toNNReal : ℝ)) :
    unzipLengthsArc γ c = unzipLengthsArc γ (readCfg (cfgData c)) := by
  funext t
  unfold readCfg cfgData
  simp only
  rw [WedgeCan4.piC_coordsFull, readDrv_eq hW hW0,
    unzipLengthsArc_congr_avgReg γ (Factorization.avgReg_reconstruct_coords c.1) _ t]

/-- Copy of `F1.unzipLengths_canon_addConst` for open arcs (goodness only off `offSet`). -/
theorem unzipLengthsArc_canon_addConst_r5c {γ k : ℝ} {x : FieldSample} {W : ℝ → ℝ}
    (hγ : 0 < γ)
    (ha : 0 < scaleParam γ (addConst x k)) (hW : Continuous W) (hW0 : W 0 = 0)
    (hWmax : ∀ s, W (max s 0) = W s) {s : ℝ} (hs : 0 ≤ s)
    (hL : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (scaleParam γ (addConst x k) ^ 2 * s) r).re)
      (𝓝[<] (0 : ℝ)) (𝓝 l))
    (hR : ∃ l, Tendsto (fun r : ℝ => (fwdMap W (scaleParam γ (addConst x k) ^ 2 * s) r).re)
      (𝓝[>] (0 : ℝ)) (𝓝 l))
    (hgood : IsLQGGoodOff γ (unzippedField γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s))
      (offSet W (scaleParam γ (addConst x k) ^ 2 * s)))
    (hfield : RegEq (unzippedField γ (canonConfig γ (addConst x k, W)) s)
      (rescale (addConst (unzippedField γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)) k)
        (Qc γ) (scaleParam γ (addConst x k)))) :
    (unzipLengthsArc γ (canonConfig γ (addConst x k, W)) s).1 =
        ENNReal.ofReal (Real.exp (γ * k / 2)) *
          (unzipLengthsArc γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)).1 ∧
      (unzipLengthsArc γ (canonConfig γ (addConst x k, W)) s).2 =
        ENNReal.ofReal (Real.exp (γ * k / 2)) *
          (unzipLengthsArc γ (x, W) (scaleParam γ (addConst x k) ^ 2 * s)).2 := by
  set a := scaleParam γ (addConst x k) with ha_def
  set t := a ^ 2 * s with ht_def
  have ht : 0 ≤ t := mul_nonneg (sq_nonneg _) hs
  obtain ⟨l, hl⟩ := hL
  obtain ⟨m, hm'⟩ := hR
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hgood
  have hm0 := sideImages_fst_nonpos_of_cont hW hW0 ht
  have hp0 := sideImages_snd_nonneg_of_cont hW hW0 ht
  have hsubL : Ioo (sideImages W t).1 0 ⊆ (offSet W t)ᶜ := fun u hu =>
    disjoint_left.1 (Ioo_left_disjoint_offSet W t hp0) hu
  have hsubR : Ioo 0 (sideImages W t).2 ⊆ (offSet W t)ᶜ := fun u hu =>
    disjoint_left.1 (Ioo_right_disjoint_offSet W t hm0) hu
  have e1 : (sideImages W t).1 = l := hl.limUnder_eq
  have e2 : (sideImages W t).2 = m := hm'.limUnder_eq
  rw [e1] at hsubL
  rw [e2] at hsubR
  have hνk := hν.addConst hreg k
  have hregk := hreg.addConst' k
  have havg := B3d.avgReg_eq_of_regEq hfield
  have hsub1 : Ioo (a * (l / a)) (a * 0) ⊆ (offSet W t)ᶜ := by
    rw [mul_div_cancel₀ _ ha.ne', mul_zero]; exact hsubL
  have hsub2 : Ioo (a * 0) (a * (m / a)) ⊆ (offSet W t)ᶜ := by
    rw [mul_div_cancel₀ _ ha.ne', mul_zero]; exact hsubR
  unfold unzipLengthsArc
  simp only
  rw [B3d.canonConfig_snd_of_max hWmax, B3d.sideImages_fst_scale W ha hs hl,
    B3d.sideImages_snd_scale W ha hs hm', e1, e2]
  rw [arcLen_congr havg, arcLen_congr havg,
    arcLen_rescale_of_hasBdryLimitOn hregk hγ ha hνk hsub1,
    arcLen_rescale_of_hasBdryLimitOn hregk hγ ha hνk hsub2,
    arcLen_eq_of_hasBdryLimitOn hreg hν hsubL,
    arcLen_eq_of_hasBdryLimitOn hreg hν hsubR,
    mul_div_cancel₀ _ ha.ne', mul_div_cancel₀ _ ha.ne', mul_zero,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact ⟨rfl, rfl⟩

/-- Copy of `F1.pstar_pos_one` for open arcs: `0 < L⁻₁ < ⊤`. -/
theorem pstar_pos_one_arc_r5c (hPG : PStarGoodOffAllStmt) (hbd : UnzipBdryPosArcStmt)
    (hF : LenFiniteArcStmt) {κ : ℝ} {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → FieldSample}
    {B' : ℝ≥0 → Ω' → ℝ} (h : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', 0 < (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) 1).1 ∧
      (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) 1).1 < ⊤ := by
  have hS := thm18Setting_of_pstar h
  have hIn := Thm18Asm.thm18Inputs_of_setting hS
  have hk : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt h.1.le
  filter_upwards [hPG κ P' Y B' h, hbd _ P' B' Y hS hIn,
    Thm18Asm.lenSideNegStmt_holds _ P' B' Y hS hIn, hF κ P' Y B' h 1 zero_le_one,
    h.2.2.2.1.cont, h.2.2.2.1.eval_zero_ae_eq_zero] with ω hg hb hn hf hc h0
  refine ⟨?_, hf.1⟩
  simp only [wedgeConfig, hk] at hb hn
  obtain ⟨hr, ⟨ν, hν⟩, -⟩ := hg 1 zero_le_one
  have hW0 : drive κ B' ω 0 = 0 := by simp [drive, h0]
  have hp : 0 ≤ (sideImages (drive κ B' ω) 1).2 :=
    sideImages_snd_nonneg_of_cont (continuous_drive_of κ hc) hW0 zero_le_one
  have hdisj := Ioo_left_disjoint_offSet (drive κ B' ω) 1 hp
  have e1 := arcLen_eq_of_hasBdryLimitOn hr hν (fun u hu hs => disjoint_left.1 hdisj hu hs)
  have e2 := IsLQGGoodOff.qBoundaryMeasureOn_eq hr hν
    (isClosed_offSet (drive κ B' ω) 1).isOpen_compl disjoint_compl_left
  have hpos := hb 1 one_pos _ _ le_rfl (hn 1 one_pos) le_rfl
  rw [e2] at hpos
  show 0 < arcLen _ _ _ _
  rw [e1]
  exact hpos.trans_le (Measure.restrict_apply_le _ _)

end Copies

section Assembly

open E6

variable {κ : ℝ} {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Y : Ω' → FieldSample} {B' : ℝ≥0 → Ω' → ℝ}

/-- Copy of `E6.ae_scCfg_lenMinus`: a.s. `L⁻_{c'}(u) = e^{γk/2} L⁻_c(b u)` for all `u ≥ 0`. -/
theorem ae_scCfg_lenMinusArc (hin : PStarZipLenInputsLocStmt)
    (hP : Thm13Asm.IsPStarSample κ P' Y B') (k : ℝ) :
    ∀ᵐ ω ∂P', ∃ b : ℝ, 0 < b ∧ ∀ u, 0 ≤ u →
      (unzipLengthsArc (Real.sqrt κ) (F1.scCfg κ k Y B' ω) u).1 =
        ENNReal.ofReal (Real.exp (Real.sqrt κ * k / 2)) *
          (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) (b * u)).1 := by
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hP.1
  filter_upwards [hin κ P' Y B' hP k, hP.2.2.2.1.cont, hP.2.2.2.1.eval_zero_ae_eq_zero]
    with ω hω hc h0
  obtain ⟨ha, hL, hR, hg, hf⟩ := hω
  have hW0 : drive κ B' ω 0 = 0 := by simp [drive, h0]
  refine ⟨_, pow_pos ha 2, fun u hu => ?_⟩
  exact (unzipLengthsArc_canon_addConst_r5c hγ ha (F1.continuous_drive_of κ hc) hW0
    (F1.drive_max κ B' ω) hu
    (hL _ (mul_nonneg (sq_nonneg _) hu)) (hR _ (mul_nonneg (sq_nonneg _) hu))
    (hg _ (mul_nonneg (sq_nonneg _) hu)) (hf u hu)).1

omit [IsProbabilityMeasure P'] in
theorem ae_read_pcfgArc (hP : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) =
      unzipLengthsArc (Real.sqrt κ) (F1.readCfg (F1.cfgData (Y ω, drive κ B' ω))) := by
  filter_upwards [hP.2.2.2.1.cont] with ω hc
  exact unzipLengthsArc_eq_readCfg_r5c (c := (Y ω, drive κ B' ω)) _
    (F1.continuous_drive_of κ hc) (F1.drive_toNNReal κ B' ω)

omit [IsProbabilityMeasure P'] in
theorem ae_read_scCfgArc (hP : Thm13Asm.IsPStarSample κ P' Y B') (k : ℝ) :
    ∀ᵐ ω ∂P', unzipLengthsArc (Real.sqrt κ) (F1.scCfg κ k Y B' ω) =
      unzipLengthsArc (Real.sqrt κ) (F1.readCfg (F1.cfgData (F1.scCfg κ k Y B' ω))) := by
  filter_upwards [hP.2.2.2.1.cont] with ω hc
  have hW := F1.continuous_drive_of κ hc
  refine unzipLengthsArc_eq_readCfg_r5c (c := F1.scCfg κ k Y B' ω) _ ?_ fun s => ?_
  · simp only [F1.scCfg, canonConfig]
    exact (hW.comp (continuous_const.mul (continuous_id.max continuous_const))).div_const _
  · simp only [F1.scCfg, canonConfig, Real.coe_toNNReal', max_eq_left (le_max_right s 0)]

/-- The reader `d ↦ G (L⁻_{τ n}(readCfg d))_n` (open arcs). -/
def lenReaderArc (γ : ℝ) (G : (ℕ → ℝ≥0∞) → ℝ≥0∞) (τ : ℕ → ℝ)
    (d : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  G fun n => (unzipLengthsArc γ (F1.readCfg d) (τ n)).1

theorem aemeasurable_lenReaderArc (hrd : LenReadTimeArcStmt)
    (hP : Thm13Asm.IsPStarSample κ P' Y B')
    {G : (ℕ → ℝ≥0∞) → ℝ≥0∞} (hG : Measurable G) {τ : ℕ → ℝ} (hτ : ∀ n, 0 ≤ τ n) :
    AEMeasurable (lenReaderArc (Real.sqrt κ) G τ) (configLawFull (F1.pcfg κ Y B') P') :=
  hG.comp_aemeasurable (AEMeasurable.of_eval fun n => (hrd κ P' Y B' hP (τ n) (hτ n)).fst)

theorem aemeasurable_lenGArc (hrd : LenReadTimeArcStmt) (hP : Thm13Asm.IsPStarSample κ P' Y B')
    {G : (ℕ → ℝ≥0∞) → ℝ≥0∞} (hG : Measurable G) {τ : ℕ → ℝ} (hτ : ∀ n, 0 ≤ τ n) :
    AEMeasurable
      (fun ω => G fun n => (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) (τ n)).1) P' := by
  have hS := F1.thm18Setting_of_pstar hP
  have hIn := Thm18Asm.thm18Inputs_of_setting hS
  refine ((aemeasurable_lenReaderArc hrd hP hG hτ).comp_aemeasurable
    (F1.aemeasurable_cfgData_drive_bm κ hIn.2.1 hP.2.2.2.1)).congr ?_
  filter_upwards [ae_read_pcfgArc hP] with ω h
  simp only [Function.comp, lenReaderArc, h]
  rfl

theorem map_scCfg_lenGArc (hlaw : F1.PStarCanonLawStmt) (hrd : LenReadTimeArcStmt)
    (hP : Thm13Asm.IsPStarSample κ P' Y B') (k : ℝ) {G : (ℕ → ℝ≥0∞) → ℝ≥0∞} (hG : Measurable G)
    {τ : ℕ → ℝ} (hτ : ∀ n, 0 ≤ τ n) :
    P'.map (fun ω => G fun n => (unzipLengthsArc (Real.sqrt κ) (F1.scCfg κ k Y B' ω) (τ n)).1) =
      P'.map
        (fun ω => G fun n => (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) (τ n)).1) := by
  obtain ⟨hl, hm⟩ := hlaw κ P' Y B' hP k
  have hS := F1.thm18Setting_of_pstar hP
  have hIn := Thm18Asm.thm18Inputs_of_setting hS
  refine map_eq_of_read_ennreal (c₁ := F1.pcfg κ Y B') (c₂ := F1.scCfg κ k Y B') hl
    (F1.aemeasurable_cfgData_drive_bm κ hIn.2.1 hP.2.2.2.1) hm
    (aemeasurable_lenReaderArc hrd hP hG hτ) ?_ ?_
  · filter_upwards [ae_read_pcfgArc hP] with ω h
    simp only [lenReaderArc, h]
  · filter_upwards [ae_read_scCfgArc hP k] with ω h
    simp only [lenReaderArc, h]

end Assembly

/-- **`PStarLenInfArcStmt` from scaling** (copy of `E6.pStarLenInfStmt_of`). -/
theorem pStarLenInfArc_of (hlaw : F1.PStarCanonLawStmt) (hin : PStarZipLenInputsLocStmt)
    (hrd : LenReadTimeArcStmt) (hM : LenStrictMonoArcStmt) (hPG : PStarGoodOffAllStmt)
    (hbd : UnzipBdryPosArcStmt) (hF : LenFiniteArcStmt) : PStarLenInfArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hP.1
  have hG : Measurable fun s : ℕ → ℝ≥0∞ => ⨆ n, s n :=
    Measurable.iSup fun n => measurable_pi_apply n
  have hτ : ∀ n : ℕ, (0 : ℝ) ≤ n := fun n => Nat.cast_nonneg n
  have hX := aemeasurable_lenGArc hrd hP hG hτ
  have hmain := E6.ae_eq_top_of_map_mul hX ?_ ?_
  · filter_upwards [hmain] with ω hω
    refine le_antisymm le_top (hω ▸ iSup_le fun n => ?_)
    exact le_iSup₂_of_le (f := fun t (_ : t ∈ Ici (0 : ℝ)) =>
      (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).1) (n : ℝ) (hτ n) le_rfl
  · filter_upwards [pstar_pos_one_arc_r5c hPG hbd hF hP] with ω h
    exact h.1.trans_le (le_iSup_of_le 1 (by simp))
  · intro n hn
    refine Eq.trans ?_ (map_scCfg_lenGArc hlaw hrd hP ((2 / Real.sqrt κ) * Real.log n) hG hτ)
    refine Measure.map_congr ?_
    filter_upwards [ae_scCfg_lenMinusArc hin hP ((2 / Real.sqrt κ) * Real.log n),
      hM κ P' Y B' hP] with ω ⟨b, hb, hω⟩ hm
    simp only [hω _ (hτ _), ← ENNReal.mul_iSup, E6.ofReal_exp_scale_up hγ hn]
    rw [E6.iSup_nat_scale hm.monotoneOn hb]

/-- **`PStarLenStartArcStmt` from scaling** (copy of `E6.pStarLenStartStmt_of`; finiteness of
`L⁻_1` from `LenFiniteArcStmt` replaces `F1.unzipLengths_fst_lt_top`). -/
theorem pStarLenStartArc_of (hlaw : F1.PStarCanonLawStmt) (hin : PStarZipLenInputsLocStmt)
    (hrd : LenReadTimeArcStmt) (hM : LenStrictMonoArcStmt) (hF : LenFiniteArcStmt) :
    PStarLenStartArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hP.1
  have hG : Measurable fun s : ℕ → ℝ≥0∞ => (⨅ n, s n)⁻¹ :=
    (Measurable.iInf fun n => measurable_pi_apply n).inv
  have hτ : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hX := aemeasurable_lenGArc hrd hP hG hτ
  have hmain := E6.ae_eq_top_of_map_mul hX ?_ ?_
  · filter_upwards [hmain, hM κ P' Y B' hP] with ω hω hm
    have h0 : ⨅ n : ℕ,
        (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) (1 / ((n : ℝ) + 1))).1 = 0 :=
      ENNReal.inv_eq_top.1 hω
    refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
    obtain ⟨n, hn⟩ := iInf_lt_iff.1 (h0 ▸ hε)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)] with t ht
    exact (hm.monotoneOn (mem_Ici.2 ht.1.le) (mem_Ici.2 (hτ n)) ht.2.le).trans hn.le
  · filter_upwards [hF κ P' Y B' hP 1 zero_le_one] with ω hf
    have e : (1 : ℝ) / (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
    refine ENNReal.inv_pos.2 (ne_top_of_le_ne_top ?_ (iInf_le _ 0))
    show (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) (1 / (((0 : ℕ) : ℝ) + 1))).1 ≠ ⊤
    rw [e]; exact hf.1.ne
  · intro n hn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    refine Eq.trans ?_ (map_scCfg_lenGArc hlaw hrd hP (-(2 / Real.sqrt κ) * Real.log n) hG hτ)
    refine Measure.map_congr ?_
    filter_upwards [ae_scCfg_lenMinusArc hin hP (-(2 / Real.sqrt κ) * Real.log n),
      hM κ P' Y B' hP] with ω ⟨b, hb, hω⟩ hm
    simp only [hω _ (hτ _), F1.ofReal_exp_scale hγ hn]
    rw [← ENNReal.mul_iInf_of_ne (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
      (ENNReal.inv_ne_top.2 hn0), E6.iInf_nat_scale hm.monotoneOn hb,
      ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)))
        (Or.inl (ENNReal.inv_ne_top.2 hn0)), inv_inv]

/-- **`HitScaleZipArcStmt` from goodness off the tip, B4(c), B3(d), reading, monotonicity,
positivity, X1 and the area node** (copy of `E6.hitScaleZipStmt_of_scaling`,
HitScaleZipScale.lean:282). -/
theorem hitScaleZipArcStmt_of_scaling (hG : PStarGoodOffAllStmt)
    (hlaw : F1.PStarCanonLawStmt) (hin : PStarZipLenInputsLocStmt) (hrd : LenReadTimeArcStmt)
    (hM : LenStrictMonoArcStmt) (hbd : UnzipBdryPosArcStmt) (hF : LenFiniteArcStmt)
    (hA : E6.PStarAreaAllStmt) : HitScaleZipArcStmt :=
  hitScaleZipArcStmt_of hG hM (pStarLenStartArc_of hlaw hin hrd hM hF)
    (pStarLenInfArc_of hlaw hin hrd hM hG hbd hF) hA

/-- **`HitScaleZipArcStmt` with the proved inputs discharged** (`hYO` gives goodness off the
tip, the field inputs and boundary positivity; B4(c) is `F1.pStarCanonLawStmt_of
F1.wedgeAddConstLawStmt_holds`, as in `E6.hitScaleZipStmt_of_frontier`). -/
theorem hitScaleZipArcStmt_of_frontier (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hrd : LenReadTimeArcStmt) (hM : LenStrictMonoArcStmt) (hF : LenFiniteArcStmt)
    (hA : E6.PStarAreaAllStmt) : HitScaleZipArcStmt :=
  hitScaleZipArcStmt_of_scaling (pStarGoodOffAll_of_yMergeOffTip hYO)
    (F1.pStarCanonLawStmt_of F1.wedgeAddConstLawStmt_holds)
    (pStarZipLenInputsLoc_of_yMergeOffTip hYO) hrd hM (unzipBdryPosArc_of_yMergeOffTip hYO) hF hA

end R5c
end LocLen
end QuantumZipper
