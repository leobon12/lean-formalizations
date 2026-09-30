import QuantumZipper.Proofs.Zipper.LocLenXGood
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.Zipper.WedgeDecompCore
import QuantumZipper.Proofs.Zipper.WedgeCore2XC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75 / R4b: the wedge fields are good off the root images at all times

Local copy of `WedgeUnzip.wedgeGoodAll_of_x` / `WedgeUnzip.wedgeGoodAll_of_decomp`
(`WedgeUnzipAddFun.lean`, `WedgeUnzipCore.lean`) with `IsLQGGood ↦ IsLQGGoodOff · (offSet W t)`
(`handoff/FOLLOW-PAPER-13.md` §1 substitution rule). The unscaled wedge field is a free field plus
`α₀(−log|·|)` plus a continuous radial function `G` (W-D); unzipping commutes with adding `G`
(`WedgeUnzip.unzipAddFun`), and goodness off a closed set is stable under adding a function
continuous on `ℍ̄` (`IsLQGGoodOff.add_ofFun`, the local rule (5.1)).

Sources: Sheffield, arXiv:1012.4797, §1.6 and p. 70 (the two sides are wedges; Prop 1.6),
§5.1 rule (5.1); Berestycki–Powell arXiv:2404.16642, Def 6.41 p. 229 (boundary measure on open
segments). The reduction bookkeeping is the one of the global version (own bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **Rule (5.1), goodness off a closed set** (local copy of `IsLQGGood.add_ofFun`): adding a
function continuous on `ℍ̄` preserves goodness off `S`. -/
theorem IsLQGGoodOff.add_ofFun {γ : ℝ} {x : FieldSample} {S : Set ℝ} (hS : IsClosed S)
    (hx : IsLQGGoodOff γ x S) {φ : ℂ → ℝ} (hφ : ContinuousOn φ Hbar) :
    IsLQGGoodOff γ (x + ofFun φ) S := by
  obtain ⟨hr, ⟨ν, hν⟩, ⟨μ, hμ⟩⟩ := hx
  exact ⟨GoodSample.gs_add_ofFun_sample hr hφ,
    ⟨_, hν.add_ofFun hr hS.isOpen_compl isOpen_univ (fun _ _ => mem_univ _)
      (by rwa [univ_inter])⟩,
    ⟨_, GoodSample.hasAreaLimit_add_ofFun hr hμ hφ⟩⟩

/-- **W-G off the root images from the free-field statements** (copy of
`WedgeUnzip.wedgeGoodAll_of_x`). -/
theorem wedgeGoodOffAll_of_x (hD : WedgeUnzip.WedgeDecompStmt) (hXG : XGoodOffAllStmt)
    (hXC : WedgeUnzip.XContinuumStmt) (hC : WedgeUnzip.GlobalCaraStmt) :
    WedgeGoodOffAllStmt := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  obtain ⟨Ω₂, _, Q, _, X'', G, hX'', hB2, hI2, hae⟩ := hD κ hκ hκ4 P X' A B'' hX hA hI hB hIB
  refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hXG κ hκ hκ4 _ _ X'' hB2 hX'' hI2, hXC κ hκ hκ4 _ _ X'' hB2 hX'' hI2,
    hC κ hκ hκ4 _ _ hB2, hae, hB2.cont, hB2.eval_zero_ae_eq_zero] with ω hG hCo hCa hZ hc h0
  obtain ⟨hGc, -, hZfc⟩ := hZ
  intro t ht
  set W := drive κ (fun t (ω : Ω × Ω₂) => B'' t ω.1) ω
  have hW : Continuous W := by
    show Continuous (drive κ _ ω)
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : W 0 = 0 := by simp [W, drive, h0]
  have hreg : RegEq (F2.zU (Real.sqrt κ) X' A ω.1) (X'' ω + F2.logSingField κ + ofFun (G ω)) :=
    S5.FieldShift.regEq_of_fc hZfc
  have e1 : unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω.1, drive κ B'' ω.1) t =
      unzippedField (Real.sqrt κ) (X'' ω + F2.logSingField κ + ofFun (G ω), W) t :=
    Factorization.coordChange_congr (funext fun k => funext fun z => hreg k z) _ _
  rw [e1]
  have hraw := WedgeUnzip.unzipAddFun (Real.sqrt κ) (X'' ω + F2.logSingField κ) (G ω) W t ht
    hW hW0 hGc hCo.1 (fun d _ r hr => hCo.2 t ht d r hr)
  rw [isLQGGoodOff_congr_coords (WedgeUnzip.coords_eq_of_fc hraw)]
  exact (hG t ht).add_ofFun (isClosed_offSet _ _) (hGc.comp_continuousOn (hCa t ht))

/-- **W-G off the root images, closed form** (no TipCore, no TIP-X): from the offset merge
statement `YMergeOffTipStmt` only. -/
theorem wedgeGoodOffAll_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    WedgeGoodOffAllStmt :=
  wedgeGoodOffAll_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds (xGoodOffAll_of_yMergeOffTip hYO)
    WedgeUnzip.xContinuumStmt_holds WedgeUnzip.globalCaraStmt_holds

end LocLen
end QuantumZipper
