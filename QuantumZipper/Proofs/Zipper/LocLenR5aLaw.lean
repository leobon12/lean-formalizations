import QuantumZipper.Proofs.Zipper.LocLenR5aLenInf
import QuantumZipper.Proofs.Zipper.LocLenR2bReg
import QuantumZipper.Proofs.Zipper.CfgBatchLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5a (D75): the universal law of the total open-arc left length; `E6PalmRegArcStmt` closed

Open-arc copy of `E6.cfgNormLenLawStmt_of_strictMono` (CfgBatchLaw.lean:126):

* the total left open-arc length is a.s. the measurable data reading
  `lenTotArcRd κ d = sup_n g1A (code d, n + 1)`: monotonicity from `b5UniformArcStmt_holds`
  (`ae_monotoneOn_lenArc`), the open-arc gate of R2b (`mem_gArcSet`, `unzipLengthsArc_eq_code`,
  LocLenR2bReg.lean) fed by goodness off the tip (`yGoodOffAll_of_yMergeOffTip` with the proved
  `SWCore.yMergeOffTipStmt_holds`);
* the data law of a normalized `Γ⁰` sample is universal (`E6.configLawFull_cfg_eq_of_normalized`).

Hence `cfgNormLenLawArc_holds`, `cfgLenInfArc_holds`, and **`e6PalmRegArc_holds :
E6PalmRegArcStmt`**. Own bookkeeping, as for the copied files.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open B2 E1 D3Plus E6
open Thm18Asm.G4Core (lcode measurable_lcode unzippedField_readCfg_cfgData)

/-- The data reading of the total left open-arc length. -/
def lenTotArcRd (κ : ℝ) (d : E6.FullData) : ℝ≥0∞ :=
  ⨆ n : ℕ, g1A (Real.sqrt κ) (lcode d, (n : ℝ) + 1)

theorem measurable_lenTotArcRd (κ : ℝ) : Measurable (lenTotArcRd κ) :=
  Measurable.iSup fun _ => (measurable_g1A _).comp (measurable_lcode.prodMk measurable_const)

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **Monotonicity of the left open-arc length of `Γ⁰`** (from `B5UniformArcStmt`). -/
theorem ae_monotoneOn_lenArc (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, MonotoneOn (fun t => (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) t).1) (Ici 0) := by
  have hN : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  filter_upwards [ae_all_iff.2 fun n : ℕ =>
      b5UniformArcStmt_holds κ hκ hκ4 ((n : ℝ) + 1) (hN n) P B X hB hX hind,
    ae_all_iff.2 fun n : ℕ => Wire2.ae_zeroMinus_Vr_facts hκ hκ4.le (hN n) P B hB]
    with ω hU hzm
  intro s hs t ht hst
  have hs' : (0 : ℝ) ≤ s := hs
  have ht' : (0 : ℝ) ≤ t := ht
  obtain ⟨n, hn⟩ := exists_nat_ge t
  obtain ⟨-, -, hanti, -⟩ := hzm n
  show (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) s).1 ≤
    (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) t).1
  rw [(hU n s ⟨hs', by linarith⟩).1, (hU n t ⟨ht', by linarith⟩).1]
  exact measure_mono (Ioo_subset_Ioo_right (hanti.antitoneOn ⟨by linarith, by linarith⟩
    ⟨by linarith, by linarith⟩ (by linarith)))

/-- **The open-arc gate holds a.s. at all times for `Γ⁰` data** (copy of the `hS` step of
`lenReadRegMeasArc_of_pStarGoodOff`). -/
theorem ae_gate_cfg (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, F1.PathGoodAll (F1.cfgData (cfg κ B X ω)).2 ∧ ∀ t : ℝ, 0 ≤ t →
      (lcode (F1.cfgData (cfg κ B X ω)), t) ∈ gArcSet (Real.sqrt κ) := by
  have hBm := IsBrownianReal.aemeasurable_pathOf hB
  have hpathP : ∀ᵐ ω ∂P, F1.PathGoodAll (F1.drivePath κ (pathOf B ω)) :=
    ae_of_ae_map ((F1.measurable_drivePath κ).comp_aemeasurable hBm)
      (F1.ae_pathGoodAll (κ := κ) hκ hκ4.le hB)
  filter_upwards [yGoodOffAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds κ hκ hκ4 P B X
      hB hX hind, hB.cont, hpathP] with ω hg hc hp
  have hd2 : (F1.cfgData (cfg κ B X ω)).2 = F1.drivePath κ (pathOf B ω) :=
    congrArg Prod.snd (F1.cfgData_drive κ (fun ω => ofFun (h0rev κ) + X ω) B ω)
  have hp' : F1.PathGoodAll (F1.cfgData (cfg κ B X ω)).2 := hd2 ▸ hp
  refine ⟨hp', fun t ht => ?_⟩
  have hU : unzippedField (Real.sqrt κ) (F1.readCfg (F1.cfgData (cfg κ B X ω))) t =
      unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) t :=
    unzippedField_readCfg_cfgData _ (F1.continuous_drive_of κ hc) (F1.drive_toNNReal κ B ω) t
  have hW' : F1.readDrv (F1.cfgData (cfg κ B X ω)).2 = drive κ B ω :=
    F1.readDrv_eq (F1.continuous_drive_of κ hc) (F1.drive_toNNReal κ B ω)
  have hEq := B3d.ZipLen.unzippedField_cfg_eq κ t (X ω) (drive κ B ω)
  obtain ⟨hreg, ⟨ν, hν⟩, -⟩ :=
    (hg t ht).mono (isClosed_offSet (drive κ B ω) t) (by simp [offSet])
  exact mem_gArcSet hp' ht (by rw [hU, hEq]; exact hreg) (ν := ν)
    (by rw [hU, hW', hEq]; exact hν)

/-- **The total left open-arc length is a.s. the data reading.** -/
theorem ae_lenTotArc_eq_rd (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, lenTotArc κ (cfg κ B X ω) = lenTotArcRd κ (F1.cfgData (cfg κ B X ω)) := by
  filter_upwards [ae_monotoneOn_lenArc hκ hκ4 hB hX hind, ae_gate_cfg hκ hκ4 hB hX hind, hB.cont]
    with ω hm hG hc
  unfold lenTotArc lenTotArcRd
  rw [iSup_Ici_eq_iSup_nat_of_monotoneOn hm]
  refine iSup_congr fun n => ?_
  have ht : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h := unzipLengthsArc_eq_code hG.1 ht (hG.2 _ ht)
  have hU : unzippedField (Real.sqrt κ) (F1.readCfg (F1.cfgData (cfg κ B X ω))) ((n : ℝ) + 1) =
      unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) ((n : ℝ) + 1) :=
    unzippedField_readCfg_cfgData _ (F1.continuous_drive_of κ hc) (F1.drive_toNNReal κ B ω) _
  have hW' : F1.readDrv (F1.cfgData (cfg κ B X ω)).2 = drive κ B ω :=
    F1.readDrv_eq (F1.continuous_drive_of κ hc) (F1.drive_toNNReal κ B ω)
  have hread : (unzipLengthsArc (Real.sqrt κ) (cfg κ B X ω) ((n : ℝ) + 1)).1 =
      (unzipLengthsArc (Real.sqrt κ) (F1.readCfg (F1.cfgData (cfg κ B X ω))) ((n : ℝ) + 1)).1 := by
    show arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (cfg κ B X ω) ((n : ℝ) + 1))
        (sideImages (drive κ B ω) ((n : ℝ) + 1)).1 0 =
      arcLen (Real.sqrt κ) (unzippedField (Real.sqrt κ) (F1.readCfg (F1.cfgData (cfg κ B X ω)))
        ((n : ℝ) + 1)) (sideImages (F1.readDrv (F1.cfgData (cfg κ B X ω)).2) ((n : ℝ) + 1)).1 0
    rw [hU, hW']
    rfl
  rw [hread, h]
  rfl

omit [IsProbabilityMeasure P] in
/-- **`CfgNormLenLawArcStmt` holds** (copy of `E6.cfgNormLenLawStmt_of_strictMono`). -/
theorem cfgNormLenLawArc_holds (κ : ℝ) : CfgNormLenLawArcStmt κ := by
  intro hκ hκ4 Ω₁ _ P₁ _ B₁ X₁ Ω₂ _ P₂ _ B₂ X₂ hB₁ hX₁ hi₁ hn₁ hB₂ hX₂ hi₂ hn₂
  have hlaw := configLawFull_cfg_eq_of_normalized κ hB₁ hX₁ hi₁ hn₁ hB₂ hX₂ hi₂ hn₂
  have hc₁ := aemeasurable_cfgData_cfg (κ := κ) hB₁ hX₁
  have hc₂ := aemeasurable_cfgData_cfg (κ := κ) hB₂ hX₂
  have he₁ := ae_lenTotArc_eq_rd hκ hκ4 hB₁ hX₁ hi₁
  have he₂ := ae_lenTotArc_eq_rd hκ hκ4 hB₂ hX₂ hi₂
  have hm := measurable_lenTotArcRd κ
  refine ⟨(hm.comp_aemeasurable hc₁).congr (he₁.mono fun _ h => h.symm), ?_⟩
  rw [Measure.map_congr he₁, Measure.map_congr he₂]
  have k₁ := AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hc₁
  have k₂ := AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hc₂
  simp only [Function.comp_def] at k₁ k₂
  rw [← k₁, ← k₂]
  exact congrArg (fun μ => Measure.map (lenTotArcRd κ) μ) hlaw

/-- **`E6PalmRegArcStmt` PROVED** (no tip core). -/
theorem e6PalmRegArc_holds : E6PalmRegArcStmt :=
  e6PalmRegArc_of_law cfgNormLenLawArc_holds

end LocLen
end QuantumZipper
