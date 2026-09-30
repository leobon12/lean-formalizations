import QuantumZipper.Proofs.Zipper.LocLenR6cRight
import QuantumZipper.Proofs.Zipper.LocLenStmtsF1Node
import QuantumZipper.Proofs.Zipper.LocLenStmtsR2b
import QuantumZipper.Proofs.Zipper.LocLenR5cPStar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R6c–R6h (4): regularity of `F` and of the read lengths, open arcs

Open-arc copies of `F1.lenReg_det`, `F1.lenRegStmt_of_flow` and `F1.lenReadRegStmt_of_meas`
(F1LenReg.lean; Sheffield arXiv:1012.4797 §1.4 and §5.4 pp. 70–72; `F = L⁺ ∘ tᴸ`). The only
change in the deterministic part: the finiteness of the lengths (automatic for the old global
measure, `unzipLengths_fst_lt_top`) is an input (X1), and `L⁻_0 = 0` is taken from
`LenLeftRegArcStmt` instead of being derived.

* `lenRegArc_det`, `lenRegArc_of_flow`, **`lenRegArc_of_yMergeOffTip`** (`LenRegArcStmt`);
* `lenReadRegArc_of_meas`, **`lenReadRegArc_of_yMergeOffTip`** (`LenReadRegArcStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open R5c (PStarLenInfArcStmt exists_reachArc_of_iSup_eq_top)

/-- **Deterministic regularity of `F`, open arcs** (copy of `F1.lenReg_det`). -/
theorem lenRegArc_det {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (hmono : StrictMonoOn (fun t => (unzipLengthsArc γ c t).1) (Ici 0))
    (hsurj : ∀ ℓ : ℝ, 0 < ℓ → ∃ t : ℝ, 0 ≤ t ∧ (unzipLengthsArc γ c t).1 = ENNReal.ofReal ℓ)
    (hL0 : (unzipLengthsArc γ c 0).1 = 0)
    (hfinL : ∀ t : ℝ, 0 ≤ t → (unzipLengthsArc γ c t).1 ≠ ⊤)
    (hfinR : ∀ t : ℝ, 0 ≤ t → (unzipLengthsArc γ c t).2 ≠ ⊤)
    (hRmono : MonotoneOn (fun t => (unzipLengthsArc γ c t).2) (Ici 0))
    (hRc : ContinuousOn (fun t => (unzipLengthsArc γ c t).2.toReal) (Ici 0))
    (hR0 : (unzipLengthsArc γ c 0).2 = 0) :
    ContinuousOn (lenFArc γ c) (Ici 0) ∧ MonotoneOn (lenFArc γ c) (Ici 0) ∧
      lenFArc γ c 0 = 0 := by
  have hτ : ∀ s : ℝ, 0 ≤ s → 0 ≤ leftTimeArc γ c s ∧
      (unzipLengthsArc γ c (leftTimeArc γ c s)).1 = ENNReal.ofReal s := by
    intro s hs
    rcases hs.eq_or_lt with h | h
    · have := leftTimeArc_of_eq hmono (le_refl (0 : ℝ)) (ℓ := 0) (by rw [hL0, ENNReal.ofReal_zero])
      rw [← h, this, hL0, ENNReal.ofReal_zero]
      exact ⟨le_rfl, rfl⟩
    · obtain ⟨t, ht, e⟩ := hsurj s h
      rw [leftTimeArc_of_eq hmono ht e]
      exact ⟨ht, e⟩
  have hτmono : MonotoneOn (leftTimeArc γ c) (Ici 0) := by
    intro s hs s' hs' hss
    by_contra hlt
    push Not at hlt
    have := hmono (mem_Ici.2 (hτ s' hs').1) (mem_Ici.2 (hτ s hs).1) hlt
    simp only at this
    rw [(hτ s hs).2, (hτ s' hs').2] at this
    exact absurd this (not_lt.2 (ENNReal.ofReal_le_ofReal hss))
  set g : ℝ → ℝ := fun s => if 0 ≤ s then leftTimeArc γ c s else s with hg
  have hgmono : Monotone g := by
    intro x y hxy
    simp only [hg]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, if_pos (hx.trans hxy)]
      exact hτmono (mem_Ici.2 hx) (mem_Ici.2 (hx.trans hxy)) hxy
    · rw [if_neg hx]
      by_cases hy : 0 ≤ y
      · rw [if_pos hy]; linarith [(hτ y hy).1]
      · rw [if_neg hy]; exact hxy
  have hgsurj : Function.Surjective g := by
    intro t
    by_cases ht : 0 ≤ t
    · refine ⟨(unzipLengthsArc γ c t).1.toReal, ?_⟩
      simp only [hg, if_pos ENNReal.toReal_nonneg]
      exact leftTimeArc_of_eq hmono ht (ENNReal.ofReal_toReal (hfinL t ht)).symm
    · exact ⟨t, by simp only [hg, if_neg ht]⟩
  have hτc : ContinuousOn (leftTimeArc γ c) (Ici 0) :=
    (hgmono.continuous_of_surjective hgsurj).continuousOn.congr fun s hs => by
      simp only [hg, if_pos (mem_Ici.1 hs)]
  refine ⟨?_, ?_, ?_⟩
  · exact hRc.comp hτc fun s hs => mem_Ici.2 (hτ s hs).1
  · intro s hs s' hs' hss
    exact ENNReal.toReal_mono (hfinR _ (hτ s' hs').1)
      (hRmono (mem_Ici.2 (hτ s hs).1) (mem_Ici.2 (hτ s' hs').1) (hτmono hs hs' hss))
  · have h0 := leftTimeArc_of_eq hmono (le_refl (0 : ℝ)) (ℓ := 0)
      (by rw [hL0, ENNReal.ofReal_zero])
    show ((unzipLengthsArc γ c (leftTimeArc γ c 0)).2).toReal = 0
    rw [h0, hR0, ENNReal.toReal_zero]

/-- `L⁺` is nondecreasing, from the capacity cocycle (copy of `F1.monotoneOn_snd_of_cocycle`). -/
theorem monotoneOn_snd_arc_of_cocycle {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (hcoc2 : ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → (unzipLengthsArc γ c (u + s)).2 =
      (unzipLengthsArc γ c u).2 + (unzipLengthsArc γ (zipCapDown γ u c) s).2) :
    MonotoneOn (fun t => (unzipLengthsArc γ c t).2) (Ici 0) := by
  intro x hx y _ hxy
  have h := hcoc2 x (y - x) hx (sub_nonneg.2 hxy)
  rw [add_sub_cancel] at h
  show (unzipLengthsArc γ c x).2 ≤ (unzipLengthsArc γ c y).2
  rw [h]
  exact le_self_add

/-- **`LenRegArcStmt` from the flow inputs** (copy of `F1.lenRegStmt_of_flow`). -/
theorem lenRegArc_of_flow (hM : LenStrictMonoArcStmt) (hS : LenLeftSurjArcStmt)
    (hL : LenLeftRegArcStmt) (hC : LenPairCocycleArcStmt) (hR : LenRightRegArcStmt)
    (hF : LenFiniteArcStmt) : LenRegArcStmt := by
  intro κ Ω' _ P' _ Y B' h
  filter_upwards [hM κ P' Y B' h, hS κ P' Y B' h, hL κ P' Y B' h, hC κ P' Y B' h,
    hR κ P' Y B' h, ae_unzipLengthsArc_lt_top_all hC hF κ P' Y B' h]
    with ω hm hs hl hc hr hf
  exact lenRegArc_det hm hs hl.2 (fun t ht => (hf t ht).1.ne) (fun t ht => (hf t ht).2.ne)
    (monotoneOn_snd_arc_of_cocycle fun u s hu hs => (hc u s hu hs).2) hr.1 hr.2

/-- **`LenRegArcStmt`, closed form**: from the offset merging input, the open-arc pair cocycle
(R6a), fixed-time finiteness (X1, R6g) and unboundedness of `L⁻`. -/
theorem lenRegArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) (hU : LenLeftUnbddArcStmt) :
    LenRegArcStmt :=
  lenRegArc_of_flow (lenStrictMonoArc_of_yMergeOffTip hYO hC hF)
    (lenLeftSurjArc_of_reg (lenLeftRegArc_of_yMergeOffTip hYO hC hF) hU hC hF)
    (lenLeftRegArc_of_yMergeOffTip hYO hC hF) hC (lenRightRegArc_of_yMergeOffTip hYO hC hF) hF

/-! ## The read lengths -/

/-- Open-arc lengths only read `avgReg` of the field (local copy of
`unzipLengthsArc_congr_avgReg`, LocLenF2Step4.lean). -/
theorem unzipLengthsArc_congr_avgReg_r6c (γ : ℝ) {x y : FieldSample} (h : avgReg x = avgReg y)
    (W : ℝ → ℝ) (t : ℝ) : unzipLengthsArc γ (x, W) t = unzipLengthsArc γ (y, W) t := by
  have hcc : unzippedField γ (x, W) t = unzippedField γ (y, W) t := by
    funext μ
    show coordChange _ (fwdMapInv W t) (Qc γ) μ = coordChange _ (fwdMapInv W t) (Qc γ) μ
    unfold coordChange
    rw [F2.evalReg_congr_avgReg h]
  simp only [unzipLengthsArc, hcc]

/-- Copy of `F1.unzipLengths_eq_readCfg`. -/
theorem unzipLengthsArc_eq_readCfg_r6c (γ : ℝ) {c : FieldSample × (ℝ → ℝ)} (hW : Continuous c.2)
    (hW0 : ∀ s, c.2 s = c.2 (s.toNNReal : ℝ)) :
    unzipLengthsArc γ c = unzipLengthsArc γ (F1.readCfg (F1.cfgData c)) := by
  funext t
  unfold F1.readCfg F1.cfgData
  simp only
  rw [WedgeCan4.piC_coordsFull, F1.readDrv_eq hW hW0,
    unzipLengthsArc_congr_avgReg_r6c γ (Factorization.avgReg_reconstruct_coords c.1) _ t]

/-- **`LenReadRegArcStmt` from the regularity of the sample and the measurability of the
regularity set** (copy of `F1.lenReadRegStmt_of_meas`). -/
theorem lenReadRegArc_of_meas (hM : LenStrictMonoArcStmt) (hR : LenRightRegArcStmt)
    (hmeas : LenReadRegMeasArcStmt) : LenReadRegArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  obtain ⟨hκ, hκ4, hW, hB, -⟩ := id hP
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  have hY : AEMeasurable (fun ω => F1.dataH (Y ω)) P' :=
    Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hW
  have hf : AEMeasurable (fun ω => F1.cfgData (F1.pcfg κ Y B' ω)) P' :=
    F1.aemeasurable_cfgData_drive_bm κ hY hB
  have hS := hmeas κ P' Y B' hP
  rw [F1.configLawFull_eq_map_cfgData] at hS ⊢
  refine F1.ae_map_of_nullMeasurableSet hf hS ?_
  filter_upwards [hM κ P' Y B' hP, hR κ P' Y B' hP, hB.cont] with ω hm hr hc
  have e := unzipLengthsArc_eq_readCfg_r6c (Real.sqrt κ) (c := F1.pcfg κ Y B' ω)
    (F1.continuous_drive_of κ hc) (F1.drive_toNNReal κ B' ω)
  show MonotoneOn (fun t => (unzipLengthsArc (Real.sqrt κ)
      (F1.readCfg (F1.cfgData (F1.pcfg κ Y B' ω))) t).1) (Ici 0) ∧ ContinuousOn
      (fun t => (unzipLengthsArc (Real.sqrt κ)
        (F1.readCfg (F1.cfgData (F1.pcfg κ Y B' ω))) t).2.toReal) (Ici 0)
  rw [← e]
  exact ⟨hm.monotoneOn, hr.1⟩

/-- **`LenReadRegArcStmt`, closed form**: from the offset merging input, the open-arc pair
cocycle (R6a), fixed-time finiteness (X1, R6g) and the measurability node (R2b). -/
theorem lenReadRegArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hC : LenPairCocycleArcStmt) (hF : LenFiniteArcStmt) (hmeas : LenReadRegMeasArcStmt) :
    LenReadRegArcStmt :=
  lenReadRegArc_of_meas (lenStrictMonoArc_of_yMergeOffTip hYO hC hF)
    (lenRightRegArc_of_yMergeOffTip hYO hC hF) hmeas

/-- **`LenLeftUnbddArcStmt` from `PStarLenInfArcStmt`** (copy of
`F1.lenLeftUnbddStmt_of_pStarLenInf`, LenInfLeft.lean; `PStarLenInfArcStmt` is the open-arc
`sup_t L⁻_t = ∞` of R5c, proved there from scale invariance, `pStarLenInfArc_of`). -/
theorem lenLeftUnbddArc_of_pStarLenInf (h : PStarLenInfArcStmt) : LenLeftUnbddArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  filter_upwards [h κ P' Y B' hP] with ω hω M
  exact exists_reachArc_of_iSup_eq_top hω

end LocLen
end QuantumZipper
