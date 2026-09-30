import QuantumZipper.Proofs.Zipper.LocLenStmtsRead
import QuantumZipper.Proofs.Zipper.LocLenR2bCert
import QuantumZipper.Proofs.Zipper.LocLenMeasArc
import QuantumZipper.Proofs.Zipper.LocLenPStarGood
import QuantumZipper.Proofs.Zipper.LocLenF1FlowDet
import QuantumZipper.Proofs.Zipper.F1ReadMeasRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R2b: `ReadLenAEMeasArcStmt` from `PStarGoodOffAllStmt`

Open-arc copy of `F1.readLenAEMeasStmt_of_wedgeUnzipFin` (F1ReadMeasRed.lean) and of
`WedgeUnzip.readLenAEMeasStmt_of_core_all` (WedgeUnzipFin.lean): at the zipper parameter
`α = √κ − 2/√κ`, the open-arc lengths recomputed from the law data, `readLenArc √κ`, are
a.e.-measurable for the data law.

* `rdGArc`: the measurable reader (open-arc reader `arcRd` of the coordinate-rebuilt path
  surrogate `F1.rdZ`, arcs given by the side-image reader).
* `goodSetArc`: a **measurable** good event of the data space: path certificate, finite windows,
  and the countable certificate `R2b.LCert` on every rational window inside each open arc.
* `readLenArc_eq_rdGArc` (deterministic): on good data the reading is `rdGArc`; the local limit
  on each open arc is glued from the rational windows (`R2b.exists_lim_of_windows`).
* `mem_goodSetArc_cfgData`: a sample whose field unzipped at time `1` is good off
  `{O⁻₁, 0, O⁺₁}` gives good data.
* **`readLenAEMeasArc_of_pStarGoodOff`**: `PStarGoodOffAllStmt → ReadLenAEMeasArcStmt`.

Own bookkeeping (Sheffield arXiv:1012.4797 §5.4 p. 72 states the intrinsic property without
proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1 ESM CharFun CoordsFull

/-- The side images read from the data. -/
def rdSide (κ : ℝ) (d : RdData) : ℝ × ℝ := sideReader κ 1 zero_le_one (rdPathD κ d.2)

theorem measurable_rdSide (κ : ℝ) : Measurable (rdSide κ) :=
  (measurable_sideReader κ 1 zero_le_one).comp ((measurable_rdPathD κ).comp measurable_snd)

/-- **The measurable open-arc reader** on the data space. -/
def rdGArc (κ : ℝ) (d : RdData) : ℝ≥0∞ × ℝ≥0∞ :=
  (arcRd (Real.sqrt κ) (rdZ κ d) (rdSide κ d).1 0, arcRd (Real.sqrt κ) (rdZ κ d) 0 (rdSide κ d).2)

theorem measurable_rdGArc (κ : ℝ) : Measurable (rdGArc κ) :=
  (measurable_arcRd_comp _ (measurable_rdZ κ) (measurable_rdSide κ).fst measurable_const).prodMk
    (measurable_arcRd_comp _ (measurable_rdZ κ) measurable_const (measurable_rdSide κ).snd)

/-- **The measurable good event** of the data space. -/
def goodSetArc (κ : ℝ) : Set RdData :=
  {d | DyUC d.2 ∧ readDrv d.2 0 = 0 ∧
    (∀ k N : ℕ, bdryApprox (Real.sqrt κ) (rdZ κ d) k (Icc (-(N : ℝ)) N) < ⊤) ∧
    (∀ n : ℕ, (rdSide κ d).1 < (E1.winPQ n).1 → ((E1.winPQ n).2 : ℝ) < 0 →
      ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZ κ d)) (E1.winPQ n).1 (E1.winPQ n).2) ∧
    (∀ n : ℕ, (0 : ℝ) < (E1.winPQ n).1 → ((E1.winPQ n).2 : ℝ) < (rdSide κ d).2 →
      ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZ κ d)) (E1.winPQ n).1 (E1.winPQ n).2)}

theorem measurableSet_goodSetArc (κ : ℝ) : MeasurableSet (goodSetArc κ) := by
  have h1 : Measurable fun d : RdData => DyUC d.2 :=
    measurableSet_setOfPred.1 (measurableSet_dyUC.preimage measurable_snd)
  have h2 : Measurable fun d : RdData => readDrv d.2 0 = 0 :=
    measurableSet_setOfPred.1
      (measurableSet_eq_fun ((measurable_readDrv_apply 0).comp measurable_snd) measurable_const)
  have h3 : Measurable fun d : RdData =>
      ∀ k N : ℕ, bdryApprox (Real.sqrt κ) (rdZ κ d) k (Icc (-(N : ℝ)) N) < ⊤ :=
    Measurable.forall fun k => Measurable.forall fun N => measurableSet_setOfPred.1
      (measurableSet_lt ((Measure.measurable_coe measurableSet_Icc).comp
        ((measurable_bdryApprox _ k).comp (measurable_rdZ κ))) measurable_const)
  have hC : ∀ p q : ℝ, Measurable fun d : RdData =>
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZ κ d)) p q := fun p q =>
    measurableSet_setOfPred.1 ((R2b.measurableSet_lCert _ p q).preimage (measurable_rdZ κ))
  have hs := measurable_rdSide κ
  have h4 : Measurable fun d : RdData => ∀ n : ℕ, (rdSide κ d).1 < (E1.winPQ n).1 →
      ((E1.winPQ n).2 : ℝ) < 0 → ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZ κ d)) (E1.winPQ n).1 (E1.winPQ n).2 :=
    Measurable.forall fun n => (measurableSet_setOfPred.1
      (measurableSet_lt hs.fst measurable_const)).imp
      (measurable_const.imp (measurable_const.imp (hC _ _)))
  have h5 : Measurable fun d : RdData => ∀ n : ℕ, (0 : ℝ) < (E1.winPQ n).1 →
      ((E1.winPQ n).2 : ℝ) < (rdSide κ d).2 → ((E1.winPQ n).1 : ℝ) < (E1.winPQ n).2 →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZ κ d)) (E1.winPQ n).1 (E1.winPQ n).2 :=
    Measurable.forall fun n => measurable_const.imp ((measurableSet_setOfPred.1
      (measurableSet_lt measurable_const hs.snd)).imp (measurable_const.imp (hC _ _)))
  exact measurableSet_setOfPred.2 (h1.and (h2.and (h3.and (h4.and h5))))

/-- The open-arc length only reads the dyadic boundary approximations. -/
theorem arcLen_congr_bdry {γ : ℝ} {x x' : FieldSample} (h : bdryApprox γ x = bdryApprox γ x')
    (a b : ℝ) : arcLen γ x a b = arcLen γ x' a b := by
  unfold arcLen qBoundaryMeasureOn; rw [h]

/-- On good paths: the side images are read by `rdSide`, and the unzipped field has the
boundary approximations of the surrogate `rdZ`. -/
theorem sides_bdry {κ : ℝ} (hκ : 0 < κ) {d : RdData} (hd : PathGood d.2) :
    sideImages (readDrv d.2) 1 = rdSide κ d ∧
      bdryApprox (Real.sqrt κ) (unzippedField (Real.sqrt κ)
        (Factorization.reconstruct (WedgeCan4.piC d.1.1), readDrv d.2) 1) =
        bdryApprox (Real.sqrt κ) (rdZ κ d) := by
  obtain ⟨hUC, h0, halive⟩ := hd
  have hc := continuous_readDrv_of_dyUC hUC
  set f := rdPathD κ d.2 with hfdef
  have hf : ∀ r ∈ Icc (0 : ℝ) 1, Wof κ 1 zero_le_one f r = readDrv d.2 r :=
    fun _ hr => Wof_rdPathD hκ hUC hr
  refine ⟨?_, ?_⟩
  · refine (sideImages_congr_drive zero_le_one fun r hr => (hf r hr).symm).trans ?_
    refine sideImages_Wof_eq_sideReader κ 1 zero_le_one f fun x hx => ?_
    obtain ⟨u, hu⟩ := halive x hx
    exact ⟨u, isForwardSol_congr_drive (fun r hr => (hf r hr).symm) hu⟩
  · exact Factorization.bdryApprox_congr
      (avgReg_congr_full (coordsFull_unzip_eq_sur hc h0 hf d.1.1)) _

/-- **The deterministic reading identity** on good data. -/
theorem readLenArc_eq_rdGArc {κ : ℝ} (hκ : 0 < κ) {d : RdData} (hp : PathGood d.2)
    (hG : d ∈ goodSetArc κ) : readLenArc (Real.sqrt κ) d = rdGArc κ d := by
  obtain ⟨hs, hb⟩ := sides_bdry hκ hp
  obtain ⟨-, -, hfin, hL, hR⟩ := hG
  have hfin' : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox (Real.sqrt κ) (rdZ κ d) k) :=
    fun k => BdryVague.isFiniteMeasureOnCompacts_of_Icc (hfin k)
  obtain ⟨ν₁, h₁⟩ := R2b.exists_lim_of_windows hfin' hL
  obtain ⟨ν₂, h₂⟩ := R2b.exists_lim_of_windows hfin' hR
  unfold readLenArc unzipLengthsArc rdGArc
  rw [hs, arcLen_congr_bdry hb, arcLen_congr_bdry hb, arcRd_eq_arcLen isOpen_Ioo h₁ subset_rfl,
    arcRd_eq_arcLen isOpen_Ioo h₂ subset_rfl]

/-- **Good data from a good sample**: regularity and a local boundary limit off
`{O⁻₁, 0, O⁺₁}` of the field unzipped at time `1`. -/
theorem mem_goodSetArc {κ : ℝ} (hκ : 0 < κ) {d : RdData} (hp : PathGood d.2) {X : FieldSample}
    (hX : unzippedField (Real.sqrt κ)
      (Factorization.reconstruct (WedgeCan4.piC d.1.1), readDrv d.2) 1 = X)
    (hreg : IsRegularSample X) {ν : Measure ℝ}
    (hν : HasBdryLimitOn (Real.sqrt κ) X (offSet (readDrv d.2) 1)ᶜ ν) : d ∈ goodSetArc κ := by
  obtain ⟨hs, hb⟩ := sides_bdry hκ hp
  rw [hX] at hb
  have hc := continuous_readDrv_of_dyUC hp.1
  have hsnd : 0 ≤ (sideImages (readDrv d.2) 1).2 :=
    sideImages_snd_nonneg_of_cont hc hp.2.1 zero_le_one
  have hfst : (sideImages (readDrv d.2) 1).1 ≤ 0 :=
    sideImages_fst_nonpos_of_cont hc hp.2.1 zero_le_one
  have hcert : ∀ p q : ℝ, p < q → Ioo p q ⊆ (offSet (readDrv d.2) 1)ᶜ →
      R2b.LCert (bdryApprox (Real.sqrt κ) (rdZ κ d)) p q := fun p q hpq hsub => by
    rw [← hb]
    exact R2b.lCert_of_lim hpq (HasBdryLimitOn.isVagueLimitOnR hreg (hν.mono isOpen_Ioo hsub))
  refine ⟨hp.1, hp.2.1, fun k N => ?_, fun n h1 h2 h3 => hcert _ _ h3 ?_,
    fun n h1 h2 h3 => hcert _ _ h3 ?_⟩
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

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The data of a configuration whose unzipped field at time `1` is good off
`{O⁻₁, 0, O⁺₁}` are good. -/
theorem mem_goodSetArc_cfgData {κ : ℝ} (hκ : 0 < κ) {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ}
    {ω : Ω} (hc : Continuous fun t => B t ω) (hp : PathGood (drivePath κ (pathOf B ω)))
    (hg : IsLQGGoodOff (Real.sqrt κ) (unzippedField (Real.sqrt κ) (Y ω, drive κ B ω) 1)
      (offSet (drive κ B ω) 1)) :
    cfgData (Y ω, drive κ B ω) ∈ goodSetArc κ := by
  have hW : readDrv (drivePath κ (pathOf B ω)) = drive κ B ω := by
    rw [← drive_nnreal]; exact readDrv_eq (continuous_drive_of κ hc) (drive_toNNReal κ B ω)
  rw [cfgData_drive]
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hg
  have hX : unzippedField (Real.sqrt κ) (Factorization.reconstruct (WedgeCan4.piC
      (dataH (Y ω)).1), readDrv (drivePath κ (pathOf B ω))) 1 =
      unzippedField (Real.sqrt κ) (Y ω, drive κ B ω) 1 := by
    rw [hW]; exact unzippedField_reconstruct_coords _ _ _ _
  exact mem_goodSetArc hκ hp hX hreg (by rw [hW]; exact hν)

/-- **`ReadLenAEMeasArcStmt` at the zipper parameter from `PStarGoodOffAllStmt`.** -/
theorem readLenAEMeasArc_of_pStarGoodOff (hG : PStarGoodOffAllStmt) (κ : ℝ) :
    ReadLenAEMeasArcStmt (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) κ := by
  intro hκ hκ4 _ _ Ω _ P Y B hPr hW hB hY hBm hind
  have := hPr
  have hφ := aemeasurable_cfgData_drive κ hY hBm
  have hpathP : ∀ᵐ ω ∂P, PathGood (drivePath κ (pathOf B ω)) :=
    ae_of_ae_map ((measurable_drivePath κ).comp_aemeasurable hBm)
      (readPathGoodStmt_holds κ hκ hκ4.le Ω P B hPr hB)
  have hpath : ∀ᵐ d ∂(configLawFull (fun ω => (Y ω, drive κ B ω)) P), PathGood d.2 := by
    have h := readPathGoodStmt_holds κ hκ hκ4.le Ω P B hPr hB
    rw [← map_snd_configLawFull κ hY hBm] at h
    exact ae_of_ae_map measurable_snd.aemeasurable h
  have hgood := hG κ P Y B ⟨hκ, hκ4, hW, hB, hind.symm⟩
  have hS : ∀ᵐ d ∂(configLawFull (fun ω => (Y ω, drive κ B ω)) P), d ∈ goodSetArc κ := by
    rw [configLawFull_eq_map_cfgData]
    refine (ae_map_iff hφ (measurableSet_goodSetArc κ)).2 ?_
    filter_upwards [hpathP, hgood, hB.cont] with ω hp hg hc
    exact mem_goodSetArc_cfgData hκ hc hp (hg 1 zero_le_one)
  refine ⟨rdGArc κ, measurable_rdGArc κ, ?_⟩
  filter_upwards [hpath, hS] with d h1 h2
  exact readLenArc_eq_rdGArc hκ h1 h2

/-- The zipper-parameter statement for every `κ`, from `YMergeOffTipStmt`. -/
theorem readLenAEMeasArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) (κ : ℝ) :
    ReadLenAEMeasArcStmt (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) κ :=
  readLenAEMeasArc_of_pStarGoodOff (pStarGoodOffAll_of_yMergeOffTip hYO) κ

end LocLen
end QuantumZipper
