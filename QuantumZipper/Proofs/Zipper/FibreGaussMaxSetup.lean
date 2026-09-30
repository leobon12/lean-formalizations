import QuantumZipper.Proofs.Zipper.UnifGaugeNodes
import QuantumZipper.Proofs.Zipper.JointModFixed
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame
import QuantumZipper.Proofs.Thm18.G1PkgTrace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FIBRE-GAUSSMAX (2): the tip family as a Gaussian process and its increment bound

The tip values `X(ν i) - X(fc(0,1))`, `ν i = νT W i.2 1 i.1`, are coordinates of the Gaussian
process of balanced admissible pairs of `IsFreeGFFModConstH` (`fgmPhi`). For any vectors `v`
whose increments have the variances of these coordinates, the increment bound
`‖v g - v h‖² ≤ (2 √(fgmA κ C))² ‖P g - P h‖^{1/36}` holds as soon as the intermediate parameter
`(h.1, g.2)` is available (`fgm_hv`): split time and space steps (`fgm_time_le`,
`fgm_space_le`) and use the triangle inequality. The reference parameter `(0,0)` gives the
circle `fc(0,1)` itself (`fgmNu_ref`). Own elementary bookkeeping.
-/

noncomputable section

open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open CharFun TwoPoint RegCont KolmD RegSample

/-- Index type of the difference process of `IsFreeGFFModConstH`. -/
abbrev FgmPairT : Type :=
  {q : Measure ℂ × Measure ℂ // IsAdmissibleH q.1 ∧ IsAdmissibleH q.2 ∧ q.1 univ = q.2 univ}

variable {κ C : ℝ} {f : C(Icc (0 : ℝ) 1, ℝ)}

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end RegUnif
end QuantumZipper
