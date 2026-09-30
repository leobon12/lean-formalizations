import QuantumZipper.Proofs.Thm18.G3Pl3Red
import QuantumZipper.Proofs.Thm18.G1Side3Split
import QuantumZipper.Proofs.Thm18.G1RCProfile
import QuantumZipper.Proofs.GFF.CoordRegEnergy
import QuantumZipper.Proofs.Zipper.WedgeShiftInt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (a): PAIR-LIM for the unscaled wedge field from the free field

The unscaled wedge field `W = wedgeField (lateralPart x) A Q` is, on folded circles well inside
`ℍ`, the regular version `F` of the free field plus the circle average of the (cut) wedge profile
`profCut x A Q c₀`, a continuous function (`G1Side.evalReg_wedge_fc`, `G1Side.continuous_profCut`;
Sheffield arXiv:1012.4797 §1.6, the wedge is the free field plus a radial profile). A dilated test
measure `(ρ± dz) ∘ (c ·)⁻¹` is carried by a compact subset of `ℍ`, so for small smoothing radii
the profile part converges by continuity (dominated convergence), and PAIR-LIM for `W` reduces
to PAIR-LIM for the regular version of the free field (`G3Pl3FreePairLimStmt`,
Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1: the circle-average smoothing of the
free field converges as a distribution). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The dilated test measure `(σ dz) ∘ (c ·)⁻¹`. -/
abbrev g3plTM (σ : ℂ → ℝ) (c : ℝ) : Measure ℂ := (G1.tmeas σ).map fun z => (c : ℂ) * z

end R18
end QuantumZipper
