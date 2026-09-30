import QuantumZipper.Proofs.Zipper.LocLenStmtsF1Node
import QuantumZipper.Proofs.Zipper.LocLenReflect
import QuantumZipper.Proofs.Zipper.LocLenPosMain
import QuantumZipper.Proofs.Zipper.LocLenF1Flow
import QuantumZipper.Proofs.Zipper.LocLenF2Step4
import QuantumZipper.Proofs.Zipper.ESMComplF1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6e: F1d ("by symmetry") with open arcs

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4 p. 72: if
`L⁺ = k L⁻` with a constant `k`, the reflection invariance of `P_*` gives `k =_d 1/k`, hence
`k = 1`. Open-arc copies (`unzipLengths ↦ unzipLengthsArc`, `readLen ↦ readLenArc`) of
`F1.f1d_lengths_agree_core` (F1Reflect.lean:143), `F1.f1d_lengths_agree` (F1Reflect.lean:184),
`F1.f1d_lengths_agree_read` (F1Read.lean:116), `F1.f1d_lengths_agree_wedge` (F1Read.lean:163),
and of `F1.pstar_pos_one` (F1NodeAsm.lean:94): `0 < L⁻₁` from open-arc boundary positivity
(`UnzipBdryPosArcStmt`) and goodness off `offSet` (`PStarGoodOffAllStmt`), `L⁻₁ < ⊤` from the
fixed-time finiteness `LenFiniteArcStmt` (X1 in `P_*` form).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

section F1d

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Open-arc copy of `F1.f1d_lengths_agree_core` (Sheffield p. 72, "by symmetry"). -/
theorem f1d_lengths_agree_coreArc {γ : ℝ} (c : Ω → FieldSample × (ℝ → ℝ)) (k : ℝ≥0∞)
    (hlin : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      (unzipLengthsArc γ (c ω) t).2 = k * (unzipLengthsArc γ (c ω) t).1)
    (hmeas : AEMeasurable (fun ω => unzipLengthsArc γ (c ω) 1) P)
    (hmeas' : AEMeasurable (fun ω => unzipLengthsArc γ (reflectConfig (c ω)) 1) P)
    (hlaw : P.map (fun ω => unzipLengthsArc γ (reflectConfig (c ω)) 1) =
      P.map (fun ω => unzipLengthsArc γ (c ω) 1))
    (hrefl : ∀ᵐ ω ∂P, unzipLengthsArc γ (reflectConfig (c ω)) 1 =
      (unzipLengthsArc γ (c ω) 1).swap)
    (hpos : ∀ᵐ ω ∂P, 0 < (unzipLengthsArc γ (c ω) 1).1 ∧ (unzipLengthsArc γ (c ω) 1).1 < ⊤) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → (unzipLengthsArc γ (c ω) t).1 = (unzipLengthsArc γ (c ω) t).2 := by
  set S : Set (ℝ≥0∞ × ℝ≥0∞) := {p | p.2 = k * p.1} with hS
  have hSm : MeasurableSet S :=
    measurableSet_eq_fun measurable_snd (measurable_const.mul measurable_fst)
  have h1 : ∀ᵐ y ∂P.map (fun ω => unzipLengthsArc γ (c ω) 1), y ∈ S :=
    (ae_map_iff hmeas hSm).2 (hlin.mono fun ω h => h 1 zero_le_one)
  rw [← hlaw] at h1
  have h2 := (ae_map_iff hmeas' hSm).1 h1
  have hkk : k * k = 1 := by
    obtain ⟨ω, hω1, hω2, hω3, hω4⟩ := (h2.and (hrefl.and (hpos.and hlin))).exists
    have e1 : (unzipLengthsArc γ (c ω) 1).1 = k * (unzipLengthsArc γ (c ω) 1).2 := by
      have := hω1; simp only [hω2, Prod.fst_swap, Prod.snd_swap] at this
      exact this
    have e2 := hω4 1 zero_le_one
    have e3 : (k * k) * (unzipLengthsArc γ (c ω) 1).1 = 1 * (unzipLengthsArc γ (c ω) 1).1 := by
      rw [one_mul, mul_assoc, ← e2, ← e1]
    exact (ENNReal.mul_left_inj hω3.1.ne' hω3.2.ne).1 e3
  have hk1 := ennreal_eq_one_of_mul_self hkk
  filter_upwards [hlin] with ω h t ht
  rw [h t ht, hk1, one_mul]

/-- Open-arc copy of `F1.f1d_lengths_agree` (law form, measurable reading `g`). -/
theorem f1d_lengths_agreeArc {γ : ℝ} (c : Ω → FieldSample × (ℝ → ℝ)) (k : ℝ≥0∞)
    (hlin : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      (unzipLengthsArc γ (c ω) t).2 = k * (unzipLengthsArc γ (c ω) t).1)
    (hlaw : configLawFull (fun ω => reflectConfig (c ω)) P = configLawFull c P)
    (hmeas : AEMeasurable (fun ω => cfgData (c ω)) P)
    (hmeas' : AEMeasurable (fun ω => cfgData (reflectConfig (c ω))) P)
    (g : ((ℕ → ℝ) × (TestFun H → ℝ)) × (NNReal → ℝ) → ℝ≥0∞ × ℝ≥0∞) (hg : Measurable g)
    (hgc : ∀ᵐ ω ∂P, unzipLengthsArc γ (c ω) 1 = g (cfgData (c ω)))
    (hgc' : ∀ᵐ ω ∂P, unzipLengthsArc γ (reflectConfig (c ω)) 1 =
      g (cfgData (reflectConfig (c ω))))
    (hrefl : ∀ᵐ ω ∂P, unzipLengthsArc γ (reflectConfig (c ω)) 1 =
      (unzipLengthsArc γ (c ω) 1).swap)
    (hpos : ∀ᵐ ω ∂P, 0 < (unzipLengthsArc γ (c ω) 1).1 ∧ (unzipLengthsArc γ (c ω) 1).1 < ⊤) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → (unzipLengthsArc γ (c ω) t).1 = (unzipLengthsArc γ (c ω) t).2 := by
  rw [configLawFull_eq_map_cfgData, configLawFull_eq_map_cfgData] at hlaw
  have hm1 : AEMeasurable (fun ω => unzipLengthsArc γ (c ω) 1) P :=
    (hg.comp_aemeasurable hmeas).congr (hgc.mono fun ω h => h.symm)
  have hm1' : AEMeasurable (fun ω => unzipLengthsArc γ (reflectConfig (c ω)) 1) P :=
    (hg.comp_aemeasurable hmeas').congr (hgc'.mono fun ω h => h.symm)
  refine f1d_lengths_agree_coreArc c k hlin hm1 hm1' ?_ hrefl hpos
  rw [Measure.map_congr hgc, Measure.map_congr hgc']
  show Measure.map (g ∘ fun ω => cfgData (reflectConfig (c ω))) P =
    Measure.map (g ∘ fun ω => cfgData (c ω)) P
  rw [← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hmeas',
    ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hmeas, hlaw]

/-- Open-arc copy of `F1.unzipLengths_eq_readLen`. -/
theorem unzipLengthsArc_eq_readLenArc (γ : ℝ) {c : FieldSample × (ℝ → ℝ)} (hW : Continuous c.2)
    (hW0 : ∀ s, c.2 s = c.2 (s.toNNReal : ℝ)) :
    unzipLengthsArc γ c 1 = readLenArc γ (cfgData c) := by
  unfold readLenArc cfgData
  simp only
  rw [WedgeCan4.piC_coordsFull, readDrv_eq hW hW0,
    unzipLengthsArc_congr_avgReg γ (Factorization.avgReg_reconstruct_coords c.1) _ 1]

/-- Open-arc copy of `F1.f1d_lengths_agree_read`. -/
theorem f1d_lengths_agree_readArc {γ : ℝ}
    (c : Ω → FieldSample × (ℝ → ℝ)) (k : ℝ≥0∞)
    (hcont : ∀ᵐ ω ∂P, Continuous (c ω).2) (hnn : ∀ ω s, (c ω).2 s = (c ω).2 (s.toNNReal : ℝ))
    (hlin : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      (unzipLengthsArc γ (c ω) t).2 = k * (unzipLengthsArc γ (c ω) t).1)
    (hlaw : configLawFull (fun ω => reflectConfig (c ω)) P = configLawFull c P)
    (hmeas : AEMeasurable (fun ω => cfgData (c ω)) P)
    (hmeas' : AEMeasurable (fun ω => cfgData (reflectConfig (c ω))) P)
    (hread : AEMeasurable (readLenArc γ) (configLawFull c P))
    (hrefl : ∀ᵐ ω ∂P, unzipLengthsArc γ (reflectConfig (c ω)) 1 =
      (unzipLengthsArc γ (c ω) 1).swap)
    (hpos : ∀ᵐ ω ∂P, 0 < (unzipLengthsArc γ (c ω) 1).1 ∧ (unzipLengthsArc γ (c ω) 1).1 < ⊤) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → (unzipLengthsArc γ (c ω) t).1 = (unzipLengthsArc γ (c ω) t).2 := by
  obtain ⟨g, hg, hae⟩ := hread
  have h1 : ∀ᵐ ω ∂P, readLenArc γ (cfgData (c ω)) = g (cfgData (c ω)) := by
    have hae1 := hae
    rw [configLawFull_eq_map_cfgData] at hae1
    exact ae_of_ae_map hmeas hae1
  have h2 : ∀ᵐ ω ∂P, readLenArc γ (cfgData (reflectConfig (c ω))) =
      g (cfgData (reflectConfig (c ω))) := by
    have hae2 := hae
    rw [← hlaw, configLawFull_eq_map_cfgData] at hae2
    exact ae_of_ae_map hmeas' hae2
  refine f1d_lengths_agreeArc c k hlin hlaw hmeas hmeas' g hg ?_ ?_ hrefl hpos
  · filter_upwards [h1, hcont] with ω h hc
    rw [unzipLengthsArc_eq_readLenArc γ hc (hnn ω), h]
  · filter_upwards [h2, hcont] with ω h hc
    refine (unzipLengthsArc_eq_readLenArc γ hc.neg fun s => ?_).trans h
    show -(c ω).2 s = -(c ω).2 _
    rw [hnn ω s]

end F1d

/-- **F1d for `P_*`-configurations, open arcs** (copy of `F1.f1d_lengths_agree_wedge_bm`):
inputs (c) B4(d) reflection invariance (`WedgeCReg.wedgeRefReflectStmt_holds'`) and (d) the
measurable reading `ReadLenAEMeasArcStmt`. -/
theorem f1d_lengths_agree_wedgeArc {γ α κ : ℝ} (href : WedgeRefReflectStmt γ α)
    (hR : ReadLenAEMeasArcStmt γ α κ) (hκ : 0 < κ) (hκ4 : κ < 4) (hγ : γ = Real.sqrt κ)
    (hα : α < Qc γ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ} (hW : IsQuantumWedge γ α Y P)
    (hY : AEMeasurable (fun ω => dataH (Y ω)) P) (hB : IsBrownianReal B P)
    (hind : IndepFun (pathOf B) Y P) (k : ℝ≥0∞)
    (hlin : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → (unzipLengthsArc γ (Y ω, drive κ B ω) t).2 =
      k * (unzipLengthsArc γ (Y ω, drive κ B ω) t).1)
    (hrefl : ∀ᵐ ω ∂P, unzipLengthsArc γ (reflectConfig (Y ω, drive κ B ω)) 1 =
      (unzipLengthsArc γ (Y ω, drive κ B ω) 1).swap)
    (hpos : ∀ᵐ ω ∂P, 0 < (unzipLengthsArc γ (Y ω, drive κ B ω) 1).1 ∧
      (unzipLengthsArc γ (Y ω, drive κ B ω) 1).1 < ⊤) :
    ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      (unzipLengthsArc γ (Y ω, drive κ B ω) t).1 = (unzipLengthsArc γ (Y ω, drive κ B ω) t).2 :=
  have hBm := IsBrownianReal.aemeasurable_pathOf hB
  f1d_lengths_agree_readArc (fun ω => (Y ω, drive κ B ω)) k
    (hB.cont.mono fun _ hω => continuous_drive_of κ hω) (fun ω s => drive_toNNReal κ B ω s) hlin
    (configLawFull_reflect_of_wedge href hW hY hB.toIsPreBrownianReal hBm hind)
    (aemeasurable_cfgData_drive κ hY hBm) (aemeasurable_cfgData_reflect_drive κ hY hBm)
    (hR hκ hκ4 hγ hα Ω P Y B inferInstance hW hB hY hBm hind) hrefl hpos

/-- **`0 < L⁻₁ < ⊤` with open arcs** (copy of `F1.pstar_pos_one`): positivity from
`UnzipBdryPosArcStmt` (read through the limit off `offSet`, `PStarGoodOffAllStmt`) and
`O⁻₁ < 0` (`Thm18Asm.lenSideNegStmt_holds`); finiteness from `LenFiniteArcStmt` at `q = 1`. -/
theorem pstar_pos_one_arc (hPG : PStarGoodOffAllStmt) (hbd : UnzipBdryPosArcStmt)
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
  have e2 := IsLQGGoodOff.qBoundaryMeasureOn_eq hr hν (isClosed_offSet (drive κ B' ω) 1).isOpen_compl
    disjoint_compl_left
  have hpos := hb 1 one_pos _ _ le_rfl (hn 1 one_pos) le_rfl
  rw [e2] at hpos
  show 0 < arcLen _ _ _ _
  rw [e1]
  exact hpos.trans_le (Measure.restrict_apply_le _ _)

end LocLen
end QuantumZipper
