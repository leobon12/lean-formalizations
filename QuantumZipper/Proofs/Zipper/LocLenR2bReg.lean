import QuantumZipper.Proofs.Zipper.LocLenStmtsR2b
import QuantumZipper.Proofs.Zipper.LocLenR2bRead
import QuantumZipper.Proofs.Thm18.G4CMeas4Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R2b: `LenReadRegMeasArcStmt` from `PStarGoodOffAllStmt`

Open-arc copy of `Thm18Asm.G4Core.lenReadRegMeasStmt_of_gated_goodAll` (G4CMeas4Good.lean) and
its chain (`lenReadRegMeasStmt_of_gated`, `ae_bCertAll_map_of_gated`, G4CMeas3Gate.lean;
`jointGatedReaderStmt_holds`, G4CMeas4Main.lean):

* the gate `gArcSet γ ⊆ code × time` is the countable open-arc certificate of the code field
  `Zc γ q` (finite windows, `R2b.LCert` on every rational window inside each open arc given by the
  code side images `sideC q`); it is Borel (`measurableSet_gArcSet`);
* on the gate, the open-arc lengths of the read configuration are the jointly measurable
  `g1A, g2A` (`unzipLengthsArc_eq_code`);
* a field good off `{O⁻_t, 0, O⁺_t}` at time `t` puts `(code, t)` in the gate (`mem_gArcSet`);
* Lusin transfer (Kechris Thm 21.10 via `nullMeasurableSet_forall`) of the all-times gate
  membership to the data law (`ae_gArcAll_map`);
* **`lenReadRegMeasArc_of_pStarGoodOff : PStarGoodOffAllStmt → LenReadRegMeasArcStmt`**, by
  `nullMeasurableSet_regSet_of_reader`.

Own bookkeeping, as for the copied files.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open Thm18Asm.G4Core (Zc measurable_Zc sideC measurable_sideC lcode measurable_lcode LCode
  coordsFull_Zc_lcode unzippedField_readCfg_cfgData nullMeasurableSet_regSet_of_reader
  nullMeasurableSet_forall sideImages_eq_sideR)

/-- **The open-arc gate** on `code × time`. -/
def gArcSet (γ : ℝ) : Set (LCode × ℝ) :=
  {q | (∀ k N : ℕ, bdryApprox γ (Zc γ q) k (Icc (-(N : ℝ)) N) < ⊤) ∧
    (∀ n : ℕ, (sideC q).1 < (E1.winPQ n).1 → ((E1.winPQ n).2 : ℝ) < 0 →
      ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox γ (Zc γ q)) (E1.winPQ n).1 (E1.winPQ n).2) ∧
    (∀ n : ℕ, (0 : ℝ) < (E1.winPQ n).1 → ((E1.winPQ n).2 : ℝ) < (sideC q).2 →
      ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox γ (Zc γ q)) (E1.winPQ n).1 (E1.winPQ n).2)}

theorem measurableSet_gArcSet (γ : ℝ) : MeasurableSet (gArcSet γ) := by
  have h3 : Measurable fun q : LCode × ℝ =>
      ∀ k N : ℕ, bdryApprox γ (Zc γ q) k (Icc (-(N : ℝ)) N) < ⊤ :=
    Measurable.forall fun k => Measurable.forall fun N => measurableSet_setOfPred.1
      (measurableSet_lt ((Measure.measurable_coe measurableSet_Icc).comp
        ((measurable_bdryApprox _ k).comp (measurable_Zc γ))) measurable_const)
  have hC : ∀ p q : ℝ, Measurable fun r : LCode × ℝ =>
      R2b.LCert (bdryApprox γ (Zc γ r)) p q := fun p q =>
    measurableSet_setOfPred.1 ((R2b.measurableSet_lCert _ p q).preimage (measurable_Zc γ))
  have hs := measurable_sideC
  have h4 : Measurable fun r : LCode × ℝ => ∀ n : ℕ, (sideC r).1 < (E1.winPQ n).1 →
      ((E1.winPQ n).2 : ℝ) < 0 → ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox γ (Zc γ r)) (E1.winPQ n).1 (E1.winPQ n).2 :=
    Measurable.forall fun n => (measurableSet_setOfPred.1
      (measurableSet_lt hs.fst measurable_const)).imp
      (measurable_const.imp (measurable_const.imp (hC _ _)))
  have h5 : Measurable fun r : LCode × ℝ => ∀ n : ℕ, (0 : ℝ) < (E1.winPQ n).1 →
      ((E1.winPQ n).2 : ℝ) < (sideC r).2 → ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox γ (Zc γ r)) (E1.winPQ n).1 (E1.winPQ n).2 :=
    Measurable.forall fun n => measurable_const.imp ((measurableSet_setOfPred.1
      (measurableSet_lt measurable_const hs.snd)).imp (measurable_const.imp (hC _ _)))
  exact measurableSet_setOfPred.2 (h3.and (h4.and h5))

/-- The left open-arc length read from the code. -/
def g1A (γ : ℝ) (q : LCode × ℝ) : ℝ≥0∞ := arcRd γ (Zc γ q) (sideC q).1 0

/-- The right open-arc length read from the code (real-valued). -/
def g2A (γ : ℝ) (q : LCode × ℝ) : ℝ := (arcRd γ (Zc γ q) 0 (sideC q).2).toReal

theorem measurable_g1A (γ : ℝ) : Measurable (g1A γ) :=
  measurable_arcRd_comp γ (measurable_Zc γ) measurable_sideC.fst measurable_const

theorem measurable_g2A (γ : ℝ) : Measurable (g2A γ) :=
  (measurable_arcRd_comp γ (measurable_Zc γ) measurable_const measurable_sideC.snd).ennreal_toReal

/-- **On the gate, the open-arc lengths are read from the code.** -/
theorem unzipLengthsArc_eq_code {γ : ℝ} {d : E6.FullData} (hp : F1.PathGoodAll d.2) {t : ℝ}
    (ht : 0 ≤ t) (hG : (lcode d, t) ∈ gArcSet γ) :
    unzipLengthsArc γ (F1.readCfg d) t = (arcRd γ (Zc γ (lcode d, t)) (sideC (lcode d, t)).1 0,
      arcRd γ (Zc γ (lcode d, t)) 0 (sideC (lcode d, t)).2) := by
  have hb : bdryApprox γ (unzippedField γ (F1.readCfg d) t) = bdryApprox γ (Zc γ (lcode d, t)) :=
    NuMeas.bdryApprox_congr_coordsFull γ (coordsFull_Zc_lcode γ hp ht).symm
  have hs : sideImages (F1.readCfg d).2 t = sideC (lcode d, t) := sideImages_eq_sideR hp ht
  obtain ⟨hfin, hL, hR⟩ := hG
  have hfin' : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (Zc γ (lcode d, t)) k) :=
    fun k => BdryVague.isFiniteMeasureOnCompacts_of_Icc (hfin k)
  obtain ⟨ν₁, h₁⟩ := R2b.exists_lim_of_windows hfin' hL
  obtain ⟨ν₂, h₂⟩ := R2b.exists_lim_of_windows hfin' hR
  unfold unzipLengthsArc
  rw [hs, arcLen_congr_bdry hb, arcLen_congr_bdry hb, arcRd_eq_arcLen isOpen_Ioo h₁ subset_rfl,
    arcRd_eq_arcLen isOpen_Ioo h₂ subset_rfl]

/-- **A field good off `{O⁻_t, 0, O⁺_t}` puts `(code, t)` in the gate.** -/
theorem mem_gArcSet {γ : ℝ} {d : E6.FullData} (hp : F1.PathGoodAll d.2) {t : ℝ} (ht : 0 ≤ t)
    (hreg : IsRegularSample (unzippedField γ (F1.readCfg d) t)) {ν : Measure ℝ}
    (hν : HasBdryLimitOn γ (unzippedField γ (F1.readCfg d) t) (offSet (F1.readDrv d.2) t)ᶜ ν) :
    (lcode d, t) ∈ gArcSet γ := by
  have hb : bdryApprox γ (unzippedField γ (F1.readCfg d) t) = bdryApprox γ (Zc γ (lcode d, t)) :=
    NuMeas.bdryApprox_congr_coordsFull γ (coordsFull_Zc_lcode γ hp ht).symm
  have hs : sideImages (F1.readDrv d.2) t = sideC (lcode d, t) := sideImages_eq_sideR hp ht
  have hc := F1.continuous_readDrv_of_dyUC hp.1
  have hsnd : 0 ≤ (sideImages (F1.readDrv d.2) t).2 :=
    sideImages_snd_nonneg_of_cont hc hp.2.1 ht
  have hfst : (sideImages (F1.readDrv d.2) t).1 ≤ 0 :=
    sideImages_fst_nonpos_of_cont hc hp.2.1 ht
  have hcert : ∀ p q : ℝ, p < q → Ioo p q ⊆ (offSet (F1.readDrv d.2) t)ᶜ →
      R2b.LCert (bdryApprox γ (Zc γ (lcode d, t))) p q := fun p q hpq hsub => by
    rw [← hb]
    exact R2b.lCert_of_lim hpq (HasBdryLimitOn.isVagueLimitOnR hreg (hν.mono isOpen_Ioo hsub))
  refine ⟨fun k N => ?_, fun n h1 h2 h3 => hcert _ _ h3 ?_, fun n h1 h2 h3 => hcert _ _ h3 ?_⟩
  · rw [← hb]
    exact (LogSing.isFiniteMeasureOnCompacts_bdryApprox hreg _ k).lt_top_of_isCompact isCompact_Icc
  · rw [← hs] at h1
    intro y hy
    simp only [offSet, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> intro e <;> linarith [hy.1, hy.2]
  · rw [← hs] at h2
    intro y hy
    simp only [offSet, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    refine ⟨?_, ?_, ?_⟩ <;> intro e <;> linarith [hy.1, hy.2]

/-- **Lusin transfer of the all-times gate membership to an image law** (copy of
`ae_bCertAll_map_of_gated`). -/
theorem ae_gArcAll_map {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → E6.FullData} (hf : AEMeasurable f P)
    (hS : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (lcode (f ω), t) ∈ gArcSet γ) :
    ∀ᵐ d ∂(P.map f), ∀ t : ℝ, 0 ≤ t → (lcode d, t) ∈ gArcSet γ := by
  set R : Set (LCode × ℝ) := {q | q.2 < 0} ∪ gArcSet γ with hRdef
  have hRm : MeasurableSet R :=
    (measurableSet_lt measurable_snd measurable_const).union (measurableSet_gArcSet γ)
  have hT' : NullMeasurableSet {k : LCode | ∀ t : ℝ, (k, t) ∈ R} ((P.map f).map lcode) :=
    nullMeasurableSet_forall hRm _
  have hT : NullMeasurableSet (lcode ⁻¹' {k : LCode | ∀ t : ℝ, (k, t) ∈ R}) (P.map f) :=
    hT'.preimage ⟨measurable_lcode, Measure.AbsolutelyContinuous.rfl⟩
  have hmem : ∀ᵐ d ∂(P.map f), d ∈ lcode ⁻¹' {k : LCode | ∀ t : ℝ, (k, t) ∈ R} := by
    refine F1.ae_map_of_nullMeasurableSet hf hT ?_
    filter_upwards [hS] with ω hb
    intro t
    by_cases ht : t < 0
    · exact Or.inl ht
    · exact Or.inr (hb t (not_lt.1 ht))
  filter_upwards [hmem] with d hd t ht
  rcases hd t with h | h
  · exact absurd h (not_lt.2 ht)
  · exact h

/-- **`LenReadRegMeasArcStmt` from `PStarGoodOffAllStmt`.** -/
theorem lenReadRegMeasArc_of_pStarGoodOff (hG : PStarGoodOffAllStmt) : LenReadRegMeasArcStmt := by
  intro κ Ω' _ P' _ Y B' hPs
  obtain ⟨hκ, hκ4, hW, hB, -⟩ := id hPs
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hY :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hW
  have hBm := IsBrownianReal.aemeasurable_pathOf hB
  have hf : AEMeasurable (fun ω => F1.cfgData (F1.pcfg κ Y B' ω)) P' :=
    F1.aemeasurable_cfgData_drive_bm κ hY hB
  have hlaw : configLawFull (F1.pcfg κ Y B') P' = P'.map fun ω => F1.cfgData (F1.pcfg κ Y B' ω) :=
    F1.configLawFull_eq_map_cfgData _
  have hpath : ∀ᵐ d ∂(configLawFull (F1.pcfg κ Y B') P'), F1.PathGoodAll d.2 := by
    have h := F1.ae_pathGoodAll (κ := κ) hκ hκ4.le hB
    rw [← F1.map_snd_configLawFull κ hY hBm] at h
    exact ae_of_ae_map measurable_snd.aemeasurable h
  have hpathP : ∀ᵐ ω ∂P', F1.PathGoodAll (F1.drivePath κ (pathOf B' ω)) :=
    ae_of_ae_map ((F1.measurable_drivePath κ).comp_aemeasurable hBm)
      (F1.ae_pathGoodAll (κ := κ) hκ hκ4.le hB)
  have hS : ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t →
      (lcode (F1.cfgData (F1.pcfg κ Y B' ω)), t) ∈ gArcSet (Real.sqrt κ) := by
    filter_upwards [hG κ P' Y B' hPs, hB.cont, hpathP] with ω hg hc hp t ht
    have hd2 : (F1.cfgData (F1.pcfg κ Y B' ω)).2 = F1.drivePath κ (pathOf B' ω) :=
      congrArg Prod.snd (F1.cfgData_drive κ Y B' ω)
    have hp' : F1.PathGoodAll (F1.cfgData (F1.pcfg κ Y B' ω)).2 := hd2 ▸ hp
    have hU : unzippedField (Real.sqrt κ) (F1.readCfg (F1.cfgData (F1.pcfg κ Y B' ω))) t =
        unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t :=
      unzippedField_readCfg_cfgData _ (F1.continuous_drive_of κ hc) (F1.drive_toNNReal κ B' ω) t
    have hW' : F1.readDrv (F1.cfgData (F1.pcfg κ Y B' ω)).2 = drive κ B' ω :=
      F1.readDrv_eq (F1.continuous_drive_of κ hc) (F1.drive_toNNReal κ B' ω)
    obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hg t ht
    exact mem_gArcSet hp' ht (by rw [hU]; exact hreg) (ν := ν) (by rw [hU, hW']; exact hν)
  have hGa : ∀ᵐ d ∂(configLawFull (F1.pcfg κ Y B') P'), ∀ t : ℝ, 0 ≤ t →
      (lcode d, t) ∈ gArcSet (Real.sqrt κ) := by
    rw [hlaw]; exact ae_gArcAll_map hf hS
  have : IsFiniteMeasure (configLawFull (F1.pcfg κ Y B') P') := by
    unfold configLawFull; infer_instance
  refine nullMeasurableSet_regSet_of_reader (configLawFull (F1.pcfg κ Y B') P') measurable_lcode
    (L₁ := fun d t => (unzipLengthsArc (Real.sqrt κ) (F1.readCfg d) t).1)
    (L₂ := fun d t => (unzipLengthsArc (Real.sqrt κ) (F1.readCfg d) t).2.toReal)
    (measurable_g1A (Real.sqrt κ)) (measurable_g2A (Real.sqrt κ))
    (G := {d | F1.PathGoodAll d.2 ∧ ∀ t : ℝ, 0 ≤ t → (lcode d, t) ∈ gArcSet (Real.sqrt κ)})
    (ae_iff.1 (hpath.and hGa)) ?_
  rintro d ⟨hp, hb⟩ t ht
  have h := unzipLengthsArc_eq_code hp ht (hb t ht)
  exact ⟨by simp only [h]; rfl, by simp only [h]; rfl⟩

/-- **`LenReadRegMeasArcStmt` from `YMergeOffTipStmt`.** -/
theorem lenReadRegMeasArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    LenReadRegMeasArcStmt :=
  lenReadRegMeasArc_of_pStarGoodOff (pStarGoodOffAll_of_yMergeOffTip hYO)

end LocLen
end QuantumZipper
