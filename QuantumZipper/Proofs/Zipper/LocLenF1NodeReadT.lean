import QuantumZipper.Proofs.Zipper.LocLenR2bRead
import QuantumZipper.Proofs.Zipper.F1ReadTimeRed
import QuantumZipper.Proofs.Zipper.LocLenStmtsF1Node

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6e-T: `LenReadTimeArcStmt` from `PStarGoodOffAllStmt`

Time-`t` copy of the time-`1` reading argument of `LocLenR2bRead.lean`
(`rdSide`, `rdGArc`, `goodSetArc`, `mem_goodSetArc_cfgData`,
`readLenArc_eq_rdGArc`, `readLenAEMeasArc_of_pStarGoodOff`), with the time-`t` path surrogate of
`F1ReadTimeRd.lean` / `F1ReadTimeRed.lean` (`rdTimeD`, `rdZT`, `PathGoodAll`, `ae_pathGoodAll`,
`coordsFull_unzip_eq_sur_t`) in place of the time-`1` one.

* `rdGArcT`: the measurable open-arc reader at time `t` on the data space.
* `goodSetArcT`: the measurable good event at time `t` (finite windows and the countable
  certificate `R2b.LCert` on every rational window inside each open arc).
* **`lenReadTimeArc_of_pStarGoodOff`**: `PStarGoodOffAllStmt → LenReadTimeArcStmt`.
* **`lenReadTimeArc_of_yMergeOffTip`**: `YMergeOffTipStmt → LenReadTimeArcStmt`.

Own bookkeeping (Sheffield arXiv:1012.4797 §5.4 p. 72 states the intrinsic property of the
lengths without proof); the argument is the time-`t` version of the one of `LocLenR2bRead.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1 ESM CharFun CoordsFull

/-- The side images at time `t` read from the data. -/
def rdSideT (κ t : ℝ) (ht : 0 ≤ t) (d : RdData) : ℝ × ℝ := sideReader κ t ht (rdTimeD κ t d.2)

theorem measurable_rdSideT (κ t : ℝ) (ht : 0 ≤ t) : Measurable (rdSideT κ t ht) :=
  (measurable_sideReader κ t ht).comp ((measurable_rdTimeD κ t).comp measurable_snd)

/-- **The measurable open-arc reader at time `t`** on the data space. -/
def rdGArcT (κ t : ℝ) (ht : 0 ≤ t) (d : RdData) : ℝ≥0∞ × ℝ≥0∞ :=
  (arcRd (Real.sqrt κ) (rdZT κ t ht d) (rdSideT κ t ht d).1 0,
    arcRd (Real.sqrt κ) (rdZT κ t ht d) 0 (rdSideT κ t ht d).2)

theorem measurable_rdGArcT (κ t : ℝ) (ht : 0 ≤ t) : Measurable (rdGArcT κ t ht) :=
  (measurable_arcRd_comp _ (measurable_rdZT κ t ht) (measurable_rdSideT κ t ht).fst
    measurable_const).prodMk
    (measurable_arcRd_comp _ (measurable_rdZT κ t ht) measurable_const
      (measurable_rdSideT κ t ht).snd)

/-- **The measurable good event at time `t`** of the data space. -/
def goodSetArcT (κ t : ℝ) (ht : 0 ≤ t) : Set RdData :=
  {d | (∀ k N : ℕ, bdryApprox (Real.sqrt κ) (rdZT κ t ht d) k (Icc (-(N : ℝ)) N) < ⊤) ∧
    (∀ n : ℕ, (rdSideT κ t ht d).1 < (E1.winPQ n).1 → ((E1.winPQ n).2 : ℝ) < 0 →
      ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZT κ t ht d)) (E1.winPQ n).1 (E1.winPQ n).2) ∧
    (∀ n : ℕ, (0 : ℝ) < (E1.winPQ n).1 → ((E1.winPQ n).2 : ℝ) < (rdSideT κ t ht d).2 →
      ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZT κ t ht d)) (E1.winPQ n).1 (E1.winPQ n).2)}

theorem measurableSet_goodSetArcT (κ t : ℝ) (ht : 0 ≤ t) :
    MeasurableSet (goodSetArcT κ t ht) := by
  have h3 : Measurable fun d : RdData =>
      ∀ k N : ℕ, bdryApprox (Real.sqrt κ) (rdZT κ t ht d) k (Icc (-(N : ℝ)) N) < ⊤ :=
    Measurable.forall fun k => Measurable.forall fun N => measurableSet_setOfPred.1
      (measurableSet_lt ((Measure.measurable_coe measurableSet_Icc).comp
        ((measurable_bdryApprox _ k).comp (measurable_rdZT κ t ht))) measurable_const)
  have hC : ∀ p q : ℝ, Measurable fun d : RdData =>
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZT κ t ht d)) p q := fun p q =>
    measurableSet_setOfPred.1 ((R2b.measurableSet_lCert _ p q).preimage (measurable_rdZT κ t ht))
  have hs := measurable_rdSideT κ t ht
  have h4 : Measurable fun d : RdData => ∀ n : ℕ, (rdSideT κ t ht d).1 < (E1.winPQ n).1 →
      ((E1.winPQ n).2 : ℝ) < 0 → ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZT κ t ht d)) (E1.winPQ n).1 (E1.winPQ n).2 :=
    Measurable.forall fun n => (measurableSet_setOfPred.1
      (measurableSet_lt hs.fst measurable_const)).imp
      (measurable_const.imp (measurable_const.imp (hC _ _)))
  have h5 : Measurable fun d : RdData => ∀ n : ℕ, (0 : ℝ) < (E1.winPQ n).1 →
      ((E1.winPQ n).2 : ℝ) < (rdSideT κ t ht d).2 → ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZT κ t ht d)) (E1.winPQ n).1 (E1.winPQ n).2 :=
    Measurable.forall fun n => measurable_const.imp ((measurableSet_setOfPred.1
      (measurableSet_lt measurable_const hs.snd)).imp (measurable_const.imp (hC _ _)))
  exact measurableSet_setOfPred.2 (h3.and (h4.and h5))

/-- On good paths: the side images at time `t` are read by `rdSideT`, and the field unzipped at
time `t` has the boundary approximations of the surrogate `rdZT`. -/
theorem sides_bdryT {κ t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t) {d : RdData} (hd : PathGoodAll d.2) :
    sideImages (readDrv d.2) t = rdSideT κ t ht d ∧
      bdryApprox (Real.sqrt κ) (unzippedField (Real.sqrt κ)
        (Factorization.reconstruct (WedgeCan4.piC d.1.1), readDrv d.2) t) =
        bdryApprox (Real.sqrt κ) (rdZT κ t ht d) := by
  obtain ⟨hUC, h0, halive⟩ := hd
  have hc := continuous_readDrv_of_dyUC hUC
  set f := rdTimeD κ t d.2 with hfdef
  have hf : ∀ r ∈ Icc (0 : ℝ) t, Wof κ t ht f r = readDrv d.2 r :=
    fun _ hr => Wof_rdTimeD ht hκ hUC hr
  refine ⟨?_, ?_⟩
  · refine (sideImages_congr_drive ht fun r hr => (hf r hr).symm).trans ?_
    refine sideImages_Wof_eq_sideReader κ t ht f fun x hx => ?_
    obtain ⟨u, hu⟩ := halive x hx t ht
    exact ⟨u, isForwardSol_congr_drive (fun r hr => (hf r hr).symm) hu⟩
  · exact Factorization.bdryApprox_congr
      (avgReg_congr_full (coordsFull_unzip_eq_sur_t ht hc h0 hf d.1.1)) _

/-- **The deterministic reading identity at time `t`** on good data. -/
theorem unzipLengthsArc_readCfg_eq_rdGArcT {κ t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t) {d : RdData}
    (hp : PathGoodAll d.2) (hG : d ∈ goodSetArcT κ t ht) :
    unzipLengthsArc (Real.sqrt κ) (readCfg d) t = rdGArcT κ t ht d := by
  obtain ⟨hs, hb⟩ := sides_bdryT hκ ht hp
  obtain ⟨hfin, hL, hR⟩ := hG
  have hfin' : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox (Real.sqrt κ) (rdZT κ t ht d) k) :=
    fun k => BdryVague.isFiniteMeasureOnCompacts_of_Icc (hfin k)
  obtain ⟨ν₁, h₁⟩ := R2b.exists_lim_of_windows hfin' hL
  obtain ⟨ν₂, h₂⟩ := R2b.exists_lim_of_windows hfin' hR
  unfold readCfg unzipLengthsArc rdGArcT
  rw [hs, arcLen_congr_bdry hb, arcLen_congr_bdry hb, arcRd_eq_arcLen isOpen_Ioo h₁ subset_rfl,
    arcRd_eq_arcLen isOpen_Ioo h₂ subset_rfl]

/-- **Good data at time `t` from a good sample**: regularity and a local boundary limit off
`{O⁻ₜ, 0, O⁺ₜ}` of the field unzipped at time `t`. -/
theorem mem_goodSetArcT {κ t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t) {d : RdData} (hp : PathGoodAll d.2)
    {X : FieldSample}
    (hX : unzippedField (Real.sqrt κ)
      (Factorization.reconstruct (WedgeCan4.piC d.1.1), readDrv d.2) t = X)
    (hreg : IsRegularSample X) {ν : Measure ℝ}
    (hν : HasBdryLimitOn (Real.sqrt κ) X (offSet (readDrv d.2) t)ᶜ ν) :
    d ∈ goodSetArcT κ t ht := by
  obtain ⟨hs, hb⟩ := sides_bdryT hκ ht hp
  rw [hX] at hb
  have hc := continuous_readDrv_of_dyUC hp.1
  have hsnd : 0 ≤ (sideImages (readDrv d.2) t).2 :=
    sideImages_snd_nonneg_of_cont hc hp.2.1 ht
  have hfst : (sideImages (readDrv d.2) t).1 ≤ 0 :=
    sideImages_fst_nonpos_of_cont hc hp.2.1 ht
  have hcert : ∀ p q : ℝ, p < q → Ioo p q ⊆ (offSet (readDrv d.2) t)ᶜ →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZT κ t ht d)) p q := fun p q hpq hsub => by
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

/-- The data of a configuration whose unzipped field at time `t` is good off
`{O⁻ₜ, 0, O⁺ₜ}` are good at time `t`. -/
theorem mem_goodSetArcT_cfgData {Ω : Type*} {κ t : ℝ} (hκ : 0 < κ) (ht : 0 ≤ t)
    {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hc : Continuous fun t => B t ω) (hp : PathGoodAll (drivePath κ (pathOf B ω)))
    (hg : IsLQGGoodOff (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω, drive κ B ω) t)
      (offSet (drive κ B ω) t)) :
    cfgData (Y ω, drive κ B ω) ∈ goodSetArcT κ t ht := by
  have hW : readDrv (drivePath κ (pathOf B ω)) = drive κ B ω := by
    rw [← drive_nnreal]; exact readDrv_eq (continuous_drive_of κ hc) (drive_toNNReal κ B ω)
  rw [cfgData_drive]
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hg
  have hX : unzippedField (Real.sqrt κ) (Factorization.reconstruct (WedgeCan4.piC
      (dataH (Y ω)).1), readDrv (drivePath κ (pathOf B ω))) t =
      unzippedField (Real.sqrt κ) (Y ω, drive κ B ω) t := by
    rw [hW]; exact unzippedField_reconstruct_coords _ _ _ _
  exact mem_goodSetArcT hκ ht hp hX hreg (by rw [hW]; exact hν)

/-- **`LenReadTimeArcStmt` from `PStarGoodOffAllStmt`**: time-`t` version of
`readLenAEMeasArc_of_pStarGoodOff` (LocLenR2bRead.lean). -/
theorem lenReadTimeArc_of_pStarGoodOff (hG : PStarGoodOffAllStmt) : LenReadTimeArcStmt := by
  intro κ Ω' _ P' _ Y B' hP t ht
  have hgood := hG κ P' Y B' hP
  obtain ⟨hκ, hκ4, hW, hB, hI⟩ := hP
  have hBm := IsBrownianReal.aemeasurable_pathOf hB
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hY : AEMeasurable (fun ω => dataH (Y ω)) P' :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hW
  have hφ := aemeasurable_cfgData_drive κ hY hBm
  have hpathP : ∀ᵐ ω ∂P', PathGoodAll (drivePath κ (pathOf B' ω)) :=
    ae_of_ae_map ((measurable_drivePath κ).comp_aemeasurable hBm)
      (ae_pathGoodAll (κ := κ) hκ hκ4.le hB)
  have hpath : ∀ᵐ d ∂(configLawFull (fun ω => (Y ω, drive κ B' ω)) P'), PathGoodAll d.2 := by
    have h := ae_pathGoodAll (κ := κ) hκ hκ4.le hB
    rw [← map_snd_configLawFull κ hY hBm] at h
    exact ae_of_ae_map measurable_snd.aemeasurable h
  have hS : ∀ᵐ d ∂(configLawFull (fun ω => (Y ω, drive κ B' ω)) P'),
      d ∈ goodSetArcT κ t ht := by
    rw [configLawFull_eq_map_cfgData]
    refine (ae_map_iff hφ (measurableSet_goodSetArcT κ t ht)).2 ?_
    filter_upwards [hpathP, hgood, hB.cont] with ω hp hg hc
    exact mem_goodSetArcT_cfgData hκ ht hc hp (hg t ht)
  refine ⟨rdGArcT κ t ht, measurable_rdGArcT κ t ht, ?_⟩
  filter_upwards [hpath, hS] with d h1 h2
  exact unzipLengthsArc_readCfg_eq_rdGArcT hκ ht h1 h2

/-- **`LenReadTimeArcStmt` from `YMergeOffTipStmt`**. -/
theorem lenReadTimeArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    LenReadTimeArcStmt :=
  lenReadTimeArc_of_pStarGoodOff (pStarGoodOffAll_of_yMergeOffTip hYO)

end LocLen
end QuantumZipper
