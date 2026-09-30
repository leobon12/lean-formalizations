import QuantumZipper.Proofs.Zipper.LocLenF1NodeAB
import QuantumZipper.Proofs.Zipper.LocLenF1NodeScale
import QuantumZipper.Proofs.Zipper.LocLenF1NodeC
import QuantumZipper.Proofs.Zipper.LocLenF1NodeEmbed
import QuantumZipper.Proofs.Zipper.LocLenF1NodeReadT
import QuantumZipper.Proofs.Zipper.LocLenF1NodeD
import QuantumZipper.Proofs.Zipper.LocLenCanonRegMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6e: the F1 node with open arcs

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, proof of Theorem 1.3
(pp. 70–72): with `F(s) = L⁺(tᴸ(s))` (open-arc lengths), stationarity of the length zipper (E6)
and scaling give `F(s) = s F(1)` (Birkhoff/Jensen rigidity, F1a–F1b); `F(1)` is a.s. constant by
a 0-1 law (F1c); it equals `1` by symmetry (F1d). Open-arc copy of the old chain
`F1.f1Node_of_embed_len` → `F1.f1Node_of_embed_refined` → `F1.f1Node_of_embed` →
`F1.f1Node_of_inputs` (F1LenNode.lean, F1NodeC.lean, F1NodeAsm.lean).

* `f1NodeArc_of_parts`: assembly from F1a–F1b (`F1ABArcStmt`), the embedding step
  (`F1EmbedArcStmt`), locality, reading, goodness off `offSet`, positivity and finiteness.
* `f1NodeArc_of_inputs`: the same with every proved piece discharged from
  `WedgeUnzip.YMergeOffTipStmt`; the remaining hypotheses are the open Arc statements of the other
  campaign tasks.

Own bookkeeping (as in `F1.f1Node_of_inputs`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- **F1 node with open arcs from its parts** (copy of `F1.f1Node_of_embed` +
`F1.f1Node_of_inputs`). -/
theorem f1NodeArc_of_parts (hYO : WedgeUnzip.YMergeOffTipStmt) (hAB : F1ABArcStmt)
    (hE : F1EmbedArcStmt)
    (hR : ∀ κ : ℝ, ReadLenAEMeasArcStmt (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) κ)
    (hF : LenFiniteArcStmt) : F1NodeArcStmt := by
  intro hE6 κ Ω' _ P' _ Y B' h
  have hall : HLinAllArcStmt := hAB hE6
  obtain ⟨f, hf⟩ := hall κ P' Y B' h
  obtain ⟨k, hk⟩ := f1c_pstarArc hE (B5.f1LocalityArc_of_yMergeOffTip hYO) hall h
  have hpos := pstar_pos_one_arc (pStarGoodOffAll_of_yMergeOffTip hYO)
    (unzipBdryPosArc_of_yMergeOffTip hYO) hF h
  have hS := thm18Setting_of_pstar h
  have hIn := Thm18Asm.thm18Inputs_of_setting hS
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 h.1
  have hγ2 : Real.sqrt κ < 2 := sqrt_lt_two_of h.2.1
  have hα := Thm18Asm.alpha_lt_Qc hγ hγ2
  have hlin : ∀ᵐ ω ∂P', ∀ t : ℝ, 0 ≤ t →
      (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).2 =
        k * (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) t).1 := by
    filter_upwards [hf, hk, hpos] with ω hω hkω hp t ht
    rw [hω t ht, ← hkω, lenRatio_eq_of (hω 1 zero_le_one) hp.1 hp.2]
  exact f1d_lengths_agree_wedgeArc (WedgeCReg.wedgeRefReflectStmt_holds' hγ hγ2 hα) (hR κ)
    h.1 h.2.1 rfl hα h.2.2.1 hIn.2.1 h.2.2.2.1 h.2.2.2.2.symm k hlin
    (pstar_refl_one_arc_of_yMergeOffTip hYO h) hpos

/-- **F1 node with open arcs** (copy of `F1.f1Node_of_embed_len`): every proved piece is
discharged (F1a canonical rescaling `lenCanonRegArc_of_yMergeOffTip`, F1b scaling
`lenScaleArc_of_yMergeOffTip`, F1c locality `B5.f1LocalityArc_of_yMergeOffTip`, F1d reflection
`pstar_refl_one_arc_of_yMergeOffTip`, positivity `unzipBdryPosArc_of_yMergeOffTip`, embedding
`f1EmbedArc_of`, reading `readLenAEMeasArc_of_yMergeOffTip`, `lenReadTimeArc_of_yMergeOffTip`); the other
hypotheses are the open Arc statements of the other campaign tasks. -/
theorem f1NodeArc_of_inputs (hYO : WedgeUnzip.YMergeOffTipStmt)
    (hsm : LenStrictMonoArcStmt) (hC : LenPairCocycleArcStmt) (hLR : LenLeftRegArcStmt)
    (hLU : LenLeftUnbddArcStmt) (hF : LenFiniteArcStmt) (hreg : LenRegArcStmt)
    (hrr : LenReadRegArcStmt) (hum : UnzipMeasArcStmt) :
    F1NodeArcStmt :=
  f1NodeArc_of_parts hYO
    (f1ABArc_of_inputs
      (lenCocycleArc_of_flow hsm (lenLeftSurjArc_of_reg hLR hLU hC hF) hC
        (lenCanonArc_of_reg (lenCanonRegArc_of_yMergeOffTip hYO)) hF)
      (lenScaleArc_of_yMergeOffTip hYO) (lenReadArc_of (lenReadTimeArc_of_yMergeOffTip hYO) hrr) hreg
      (lenBridgeArc_of_strictMono hsm hC hF) hum)
    (f1EmbedArc_of hYO hC hF) (readLenAEMeasArc_of_yMergeOffTip hYO) hF

end LocLen
end QuantumZipper
