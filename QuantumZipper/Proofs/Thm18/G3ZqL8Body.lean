import QuantumZipper.Proofs.Thm18.G3ZqL7AE
import QuantumZipper.Proofs.Thm18.G3ZqBody
import QuantumZipper.Proofs.Thm18.G3ZqFLeaf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (8): the map mixing body from zoom locality at quantum-typical points

`G3Zq.g3FixMixBody_map` (G3ZqBody) with the every-point node `G3ZqZoomLocStmt` replaced by the
`ν_h`-a.e. node `G3ZqLZoomLocAEMapStmt`, and the two fixed-point leaves discharged by the proved
`G3ZqF.g3ZqFixXStmt_holds`, `G3ZqF.g3ZqFixRStmt_holds`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open G3Zq

/-- **Node: zoom locality through the local maps at `ν_h`-a.e. point.** -/
def G3ZqLZoomLocAEMapStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ, G1PsiSel γ Ψ →
  ∀ a : ℝ≥0 → ℝ, G3ZqGoodPath γ a → ∀ side : Bool,
    G3ZqLZoomLocAEStmt (g3zMapZ γ Ψ side a) γ

/-- **The mixing body of the map zooms from the a.e. zoom-locality node alone.** -/
theorem g3FixMixBody_mapAE (hL : G3ZqLZoomLocAEMapStmt)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hsel : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (ha : G3ZqGoodPath γ a)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : Ω' → FieldSample) (hW : IsQuantumWedge γ γ Y' P') :
    R18.G3FixMixBody (g2WedgeLaw P' Y') (g2WedgeLaw P' Y') (g3PalmLaw γ) (g3X γ) (g3R γ)
      (g3UfZ (g3zMapZ γ Ψ true a) γ) (g3VfZ (g3zMapZ γ Ψ false a) γ) := by
  have hZm := measurable_g3zMapZ hsel true a
  have hZm' := measurable_g3zMapZ hsel false a
  have hS := g2RootLenSmoothZ_of_zoomLocAE hZm (g3zMapZ_avgReg_congr γ true a) hZm'
    (g3zMapZ_avgReg_congr γ false a) hγ hγ2 (hL γ hγ hγ2 Ψ hsel a ha true)
    (hL γ hγ hγ2 Ψ hsel a ha false)
  have hcX := g2RootXCutStmtZ_of_palm hγ hγ2
    (g2RootXPalmIdStmtZ_holds hZm (g3zMapZ_reconstruct_coords γ true a) hγ hγ2)
    (G3ZqF.g3ZqFixXStmt_holds γ hγ hγ2 Ψ hsel a ha P' Y' hW)
  have hcR := g2RootRCutStmtZ_of_palm hγ
    (g2RootRPalmIdStmtZ_holds hZm' (g3zMapZ_reconstruct_coords γ false a) hγ hγ2)
    (G3ZqF.g3ZqFixRStmt_holds γ hγ hγ2 Ψ hsel a ha P' Y' hW)
  exact g3FixMixBodyZ_of_len hγ hγ2
    (g2FixMixLenXZ_of_root hZm hγ hγ2 (g2FixMixRootXStmtZ_of_cut hS.1 hcX))
    (g2FixMixLenRZ_of_root hZm' hγ hγ2 (g2FixMixRootRStmtZ_of_cut hS.2 hcR))

end G3ZqL
end Thm18Asm
end QuantumZipper
