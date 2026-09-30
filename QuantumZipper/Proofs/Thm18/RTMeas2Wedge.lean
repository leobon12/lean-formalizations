import QuantumZipper.Proofs.Thm18.RTMeas2Off
import QuantumZipper.Proofs.Thm18.R18Arc
import QuantumZipper.Proofs.Thm18.RTHmpMain
import QuantumZipper.Proofs.Thm18.RTBeurMain
import QuantumZipper.Proofs.Zipper.FieldLawler4Final
import QuantumZipper.Proofs.Thm18.R18RTZipMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS2, part 3: the unzipped pieces of the wedge have the lengths of the unzipped wedge

A.s., for every capacity time `t ≥ 0`, the field of the pieces (`readOffField`, junk at circles
meeting the curve) and the wedge field unzipped by `t` agree (regularized) off the remaining
unzipped curve (RT2 core `MaskPullCoreStmt`, from the Hu–Miller–Peres log growth
`circAvgLogGrowthStmt_holds` and the Beurling mass bound `RTBeur.pullMassBoundStmt_holds`), and
that curve does not meet `(-∞, 0)` (`unzCurveNegStmt_holds`). Hence on the arc `(O⁻_t, 0)` they
have the same boundary approximations eventually on compacts and the same local limit
(`isVagueLimitOnR_congr_off`), which exists for the wedge (`LocLen.pStarGoodOffAll_of_yMergeOffTip`),
and the same open-arc lengths, which are strictly increasing in `t` for the wedge
(`LocLen.lenStrictMonoArc_of_yMergeOffTip_x1`). This is Sheffield's "well defined by unzipping"
(arXiv:1012.4797, p. 26) for the pieces; Berestycki–Powell arXiv:2404.16642 Thm 8.16 (the
unzipped field only sees `h` off `η`).

Own bookkeeping on the proved RT2 core.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm18Asm.G4Core CoordsFull

/-- The masked data of the wedge. -/
abbrev wd (γ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (ω : Ω) : E6.FullData :=
  offData (wedgeAConfig γ B Y ω).toPair

theorem X1_holds : BaseFin.BaseFiniteStmt :=
  BaseFin2.baseFinite_of_yMerge_tail SWCore.yMergeOffTipStmt_holds
    (BaseFin2.sleBaseTail_of_fieldLawler FieldLawler.fieldLawlerReturn_holds)

theorem wd_snd (γ : ℝ) {Ω : Type} (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample) (ω : Ω) :
    (wd γ B Y ω).2 = F1.drivePath (γ ^ 2) (pathOf B ω) :=
  F1.drive_nnreal (γ ^ 2) B ω

/-- **The wedge facts for the pieces**: a.s. the driver of the pieces is continuous with the path
certificate, and at every time `t ≥ 0` the unzipped pieces carry the window certificate on
`(O⁻_t, 0)`; their open-arc lengths are nondecreasing in `t`. -/
theorem ae_wedge_pieces {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, Continuous (wd γ B Y ω).2 ∧ F1.PathGoodAll (wd γ B Y ω).2 ∧
      (∀ t : ℝ, 0 ≤ t → WinCert
        (bdryApprox γ (unzippedField γ (configOfData γ (wd γ B Y ω)).toPair t))
        (sideImages (drvOfData (wd γ B Y ω)) t).1 0) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        (unzipLengthsOpen γ (configOfData γ (wd γ B Y ω)).toPair s).1 ≤
          (unzipLengthsOpen γ (configOfData γ (wd γ B Y ω)).toPair t).1 := by
  have hγ : 0 < γ := hS.1
  have hsq : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hγ.le
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hPs := isPStarSample_of_setting hS
  have hcore := maskPullCoreStmt_of_growth_mass circAvgLogGrowthStmt_holds
    RTBeur.pullMassBoundStmt_holds γ P B Y hS hIn
  have hneg := unzCurveNegStmt_holds γ P B Y hS hIn
  have hgood := LocLen.pStarGoodOffAll_of_yMergeOffTip hYO (γ ^ 2) P Y B hPs
  have hmono := LocLen.lenStrictMonoArc_of_yMergeOffTip_x1 hYO X1_holds (γ ^ 2) P Y B hPs
  have hBm := IsBrownianReal.aemeasurable_pathOf hS.2.2.1
  have hpathP : ∀ᵐ ω ∂P, F1.PathGoodAll (F1.drivePath (γ ^ 2) (pathOf B ω)) :=
    ae_of_ae_map ((F1.measurable_drivePath (γ ^ 2)).comp_aemeasurable hBm)
      (F1.ae_pathGoodAll (κ := γ ^ 2) (by positivity) (by nlinarith [hS.2.1]) hS.2.2.1)
  filter_upwards [hcore, hneg, hgood, hmono, hpathP, D74.ae_wedgeConfig_snd_good hS]
    with ω hc hn hg hm hp hW
  rw [hsq] at hg hm
  set W := drive (γ ^ 2) B ω with hWdef
  have hWc : Continuous W := hW.1
  have hW0 : W 0 = 0 := hW.2
  have hdrv : drvOfData (wd γ B Y ω) = W := drvOfData_offData_wedge γ B Y ω
  have hconf : (configOfData γ (wd γ B Y ω)).toPair = (readOffField (wd γ B Y ω), W) := by
    show (readOffField (wd γ B Y ω), drvOfData (wd γ B Y ω)) = _
    rw [hdrv]
  -- agreement off the unzipped remaining curve
  have hoff : ∀ t : ℝ, 0 ≤ t → RegEqOff (unzCurve W t 1) (unzippedField γ (Y ω, W) t)
      (unzippedField γ (readOffField (wd γ B Y ω), W) t) := fun t ht =>
    regEqOff_unzippedField_of_pullOff hc ht one_pos
  have hI : ∀ t : ℝ, 0 ≤ t → ∀ u ∈ Ioo (sideImages W t).1 0, (u : ℂ) ∉ unzCurve W t 1 := by
    intro t ht u hu hmem
    apply hn t ht u hu.2
    simpa [unzCurve] using hmem
  have hcont : Continuous (wd γ B Y ω).2 := by
    rw [wd_snd, ← F1.drive_nnreal]; exact hWc.comp NNReal.continuous_coe
  refine ⟨hcont, by rw [wd_snd]; exact hp, fun t ht => ?_, fun s t hs hst => ?_⟩
  · -- the window certificate
    obtain ⟨hreg, ⟨ν, hν⟩, -⟩ := hg t ht
    have hsnd : 0 ≤ (sideImages W t).2 := LocLen.sideImages_snd_nonneg_of_cont hWc hW0 ht
    have hsub : Ioo (sideImages W t).1 0 ⊆ (LocLen.offSet W t)ᶜ := by
      intro u hu
      simp only [LocLen.offSet, mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      refine ⟨?_, ?_, ?_⟩ <;> intro e <;> linarith [hu.1, hu.2]
    have hlim0 := (hν.mono isOpen_Ioo hsub).isVagueLimitOnR hreg
    have hlim1 := isVagueLimitOnR_congr_off (isClosed_unzCurve W t 1) (hoff t ht) γ (hI t ht) hlim0
    rw [hconf, hdrv]
    refine winCert_of_lim hlim1 fun n h1 h2 h3 => ?_
    have hC : ∀ u ∈ Icc (wp n) (wq n), (u : ℂ) ∉ unzCurve W t 1 := fun u hu =>
      hI t ht u ⟨h1.trans_le hu.1, hu.2.trans_lt h2⟩
    obtain ⟨K, hK⟩ := (eventually_restrict_bdryApprox_eq (isClosed_unzCurve W t 1) (hoff t ht) γ
      isCompact_Icc hC).exists_forall_of_atTop
    refine ⟨K, fun k hk => ?_⟩
    have e := congrArg (fun m : Measure ℝ => m (Icc (wp n) (wq n))) (hK k hk)
    simp only [Measure.restrict_apply measurableSet_Icc, inter_self] at e
    rw [← e]
    exact (LogSing.isFiniteMeasureOnCompacts_bdryApprox hreg γ k).lt_top_of_isCompact isCompact_Icc
  · -- the lengths
    have hlen : ∀ r : ℝ, 0 ≤ r → (unzipLengthsOpen γ (configOfData γ (wd γ B Y ω)).toPair r).1 =
        (LocLen.unzipLengthsArc γ (Y ω, W) r).1 := by
      intro r hr
      rw [hconf]
      show qBoundaryMeasureOn γ (unzippedField γ (readOffField (wd γ B Y ω), W) r)
          (Ioo (sideImages W r).1 0) (Ioo (sideImages W r).1 0) =
        qBoundaryMeasureOn γ (unzippedField γ (Y ω, W) r)
          (Ioo (sideImages W r).1 0) (Ioo (sideImages W r).1 0)
      rw [qBoundaryMeasureOn_congr_off (isClosed_unzCurve W r 1) (hoff r hr) γ (hI r hr)]
    rw [hlen s hs, hlen t (hs.trans hst)]
    exact hm.monotoneOn hs (hs.trans hst : (0 : ℝ) ≤ t) hst

end RTMeas
end R18
end QuantumZipper
