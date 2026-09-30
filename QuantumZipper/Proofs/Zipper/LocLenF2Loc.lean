import QuantumZipper.Proofs.Zipper.LocLenStmtsF2
import QuantumZipper.Proofs.Zipper.LocLenPStarGood
import QuantumZipper.Proofs.Zipper.WedgeUnzipR1
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.Zipper.ScaleGeomIn
import QuantumZipper.Proofs.Zipper.ZipLen2Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R4d: the local F2 statements, proved

Proofs of the statements of `LocLenStmtsF2.lean`, copied from the global producers
`WedgeUnzip.unscaledB3dStmt_of_core`/`unscaledB3dStmt_of_x` (WedgeUnzipB3d.lean:156,
WedgeUnzipXC.lean:169), `F2.scaleGeomAeStmt'_of_nodes` (ScaleGeomIn.lean:143),
`WedgeUnzip.wedgeUnzipLimitAllStmt_of_good` (WedgeUnzipB3d.lean:182) and
`WedgeUnzip.wedgeUnzipLimitStmt_of_good` (WedgeUnzipR1.lean:46), with goodness off the tip and
the root images (`WedgeGoodOffAllStmt`, `XGoodOffAllStmt`, `YGoodOffAllStmt`) in place of global
goodness. No tip estimate (TipCore, TIP-X) is used; the closed forms depend only on
`WedgeUnzip.YMergeOffTipStmt`.

Source: Sheffield, arXiv:1012.4797, p. 56 and §5.4 p. 70 (lengths read away from the tip);
Berestycki–Powell, arXiv:2404.16642, Def 6.41 p. 229 (boundary measure on an open segment).
The scaling/regularity parts are unchanged copies of the cited global proofs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-! ## (1) `UnscaledB3dLocStmt` -/

/-- Copy of `WedgeUnzip.unscaledB3dStmt_of_core` with wedge goodness off `offSet`. -/
theorem unscaledB3dLoc_of_core (hG : WedgeGoodOffAllStmt) (hE : WedgeUnzip.WedgeExactAllStmt)
    (hC : WedgeUnzip.WedgeContinuumStmt) : UnscaledB3dLocStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  filter_upwards [hG κ hκ hκ4 P X' A B'' hX hA hI hB hIB, hE κ hκ hκ4 P X' A B'' hX hA hI hB hIB,
    hC κ hκ hκ4 P X' A B'' hX hA hI hB hIB,
    Wire2.ae_wedge_canonical_spec hγ hγ2 (F2.alpha_lt_Qc' hγ hγ2) hX hA hI,
    hB.cont, hB.eval_zero_ae_eq_zero] with ω hGω hEω hCω hspec hc h0
  refine ⟨hGω, fun s hs => ?_⟩
  have ha : 0 < scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) := hspec.1
  have hWc : Continuous (drive κ B'' ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, h0]
  have hWmax := F2.drive_max κ B'' ω
  have has : 0 ≤ scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2 * s :=
    mul_nonneg (sq_nonneg _) hs
  refine WedgeUnzip.regEq_unzippedField_canonConfig hWc hW0 hWmax ha hs (fun d r hr => ?_)
    (hEω _ has)
  rw [B3d.canonConfig_snd_of_max hWmax]
  have hC' := hCω.2 _ has
    ((scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) : ℂ) * d) _ (mul_pos ha hr)
  exact WedgeUnzip.scaleConsistent_of_continuum hCω.1 _ hWc hW0 ha hs d hr hC'.1 hC'.2

/-- Copy of `WedgeUnzip.unscaledB3dStmt_of_x` (W-D, X-G off `offSet`, X-X, X-C, C). -/
theorem unscaledB3dLoc_of_x (hD : WedgeUnzip.WedgeDecompStmt) (hXG : XGoodOffAllStmt)
    (hXX : WedgeUnzip.XExactAllStmt) (hXC : WedgeUnzip.XContinuumStmt)
    (hC : WedgeUnzip.GlobalCaraStmt) : UnscaledB3dLocStmt :=
  unscaledB3dLoc_of_core (wedgeGoodOffAll_of_x hD hXG hXC hC)
    (wedgeExactAll_of_xOff hD hXG hXX hXC hC) (WedgeUnzip.wedgeContinuum_of_x hD hXC)

/-- **`UnscaledB3dLocStmt` from the off-tip boundary merging alone.** -/
theorem unscaledB3dLoc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    UnscaledB3dLocStmt :=
  unscaledB3dLoc_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds (xGoodOffAll_of_yMergeOffTip hYO)
    F1.xExactAllStmt_holds WedgeUnzip.xContinuumStmt_holds WedgeUnzip.globalCaraStmt_holds

/-! ## (2) `ScaleGeomAeLocStmt'` -/

/-- Copy of `F2.scaleGeomAeStmt'_of_nodes` with `Γ⁰` goodness off the tip `{0}`. -/
theorem scaleGeomAeLoc_of_nodes (hY : YGoodOffAllStmt) (hYE : WedgeUnzip.YExactAllStmt)
    (hXC : WedgeUnzip.XContinuumStmt) : ScaleGeomAeLocStmt' := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind a ha
  have hcont : ∀ᵐ ω ∂P, Continuous (drive κ B ω) :=
    hB.cont.mono fun ω h => continuous_const.mul (h.comp continuous_real_toNNReal)
  have hzero : ∀ᵐ ω ∂P, drive κ B ω 0 = 0 := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h
    simp [drive, h]
  filter_upwards [hY κ hκ hκ4 P B X hB hX hind, RS.ae_real_alive hB hκ hκ4.le,
    F2.scaleGeomRegAeStmt_of hYE hXC hκ hκ4 hB hX hind ha, F2.scaleGeomSplitAeStmt_holds hX κ ha,
    hcont, hzero] with ω hg hal hRω h2 hc h0 t ht
  have hat : 0 ≤ a ^ 2 * t := mul_nonneg (sq_nonneg a) ht
  obtain ⟨l, m, hl, hm⟩ := F1.exists_tendsto_sideImages_of_alive hat
    (fun x hx => hal x hx _ hat)
  obtain ⟨hsc, hexact⟩ := hRω t ht
  refine ⟨?_, ⟨l, hl⟩, ⟨m, hm⟩, ?_⟩
  · rw [F2.unzippedField_h0rev_eq_unzY]
    exact hg _ hat
  · rw [F2.unzippedField_congr_fc (y := rescale (ofFun (h0rev κ) + X ω) (Qc (Real.sqrt κ)) a)
      (fun d r hr => F2.addConst_rescale_fc ha hr d (h2 d r hr))]
    exact F2.regEq_unzippedField_scale (x := ofFun (h0rev κ) + X ω) (W := drive κ B ω)
      ha ht hc h0 hsc hexact

/-- **`ScaleGeomAeLocStmt'` from the off-tip boundary merging alone.** -/
theorem scaleGeomAeLoc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    ScaleGeomAeLocStmt' :=
  scaleGeomAeLoc_of_nodes (yGoodOffAll_of_yMergeOffTip hYO) B3d.ZipLen.yExactAllStmt_holds
    WedgeUnzip.xContinuumStmt_holds

/-! ## (3) Local limits of the unzipped wedge field -/

/-- Copy of `WedgeUnzip.wedgeUnzipLimitStmt_of_good` at the wedge parameter `α = γ − 2/γ`. -/
theorem wedgeUnzipLimitLoc_of_good (hG : WedgeGoodOffAllStmt) (κ : ℝ) :
    WedgeUnzipLimitLocStmt (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) κ := by
  intro hκ hκ4 _ _ Ω _ P X A B hP hX hA hB hAm hBm hind
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  obtain ⟨hXA, hXAB⟩ := WedgeUnzip.indep_pairs_of_srcSigma hXm hAm hBm hind
  filter_upwards [hG κ hκ hκ4 P X A B hX hA hXA hB hXAB] with ω hω m
  obtain ⟨hreg, ⟨ν, hν⟩, _⟩ := hω _ (GermZeroOne.epsSeq m).2
  exact ⟨ν, hν.isVagueLimitOnR hreg⟩

theorem wedgeUnzipLimitLoc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) (κ : ℝ) :
    WedgeUnzipLimitLocStmt (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) κ :=
  wedgeUnzipLimitLoc_of_good (wedgeGoodOffAll_of_yMergeOffTip hYO) κ

end LocLen
end QuantumZipper
