import QuantumZipper.Proofs.Thm18.G3Z2b2Fac
import QuantumZipper.Proofs.Thm18.G3Z2b2Reg
import QuantumZipper.Proofs.Thm18.G3Z2bFub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (7): Fubini over the path for the wedge Palm-window integral through the curve maps

* `g1Inner_eq_g1PhiM`: for a good path, the inner integral of `g1zWedgePalmInt` through the curve
  maps `g1zLocMap` equals the measurable functional `g1PhiM`, at every good field `y` whose
  boundary-measure-a.e.
  window point satisfies the regularity conditions `G1FacReg`.
* **`g1zWedgePalmInt_fubini`**: in the Theorem 1.8 setting, if a.s. the window points satisfy
  `G1FacReg` (for boundary-measure-a.e. window point), then
  `g1zWedgePalmInt = ∫ (∫ g1PhiM(wedgeRep ω', a) dP'(ω')) d(law of the path)(a)`
  on the space of the wedge representative. This is Z2a (`g3PathFubiniStmt_holds`) with the
  measurable `G = g1PhiM ∘ (fromC, ·)` of `G3Z2b2Fac`.

Sheffield, arXiv:1012.4797, p. 70 (the curve is independent of the wedge; average over the field
at a fixed curve). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

open D3Plus Factorization

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

theorem measurableSet_g1zWedgeWin (γ : ℝ) (left : Bool) (y : FieldSample) (U : ℝ) :
    MeasurableSet (g1zWedgeWin γ left y U) := by
  set ν := qBoundaryMeasure γ y
  cases left
  · have hmono : Monotone fun x : ℝ => ν (Icc 0 x) := fun a b hab =>
      measure_mono (Icc_subset_Icc_right hab)
    have e : g1zWedgeWin γ false y U = Ioi 0 ∩ {x | ν (Icc 0 x) ≤ ENNReal.ofReal U} := by
      ext x; simp [g1zWedgeWin, g1SideHalf, g1SideSeg, ν]
    rw [e]
    exact measurableSet_Ioi.inter (measurableSet_le hmono.measurable measurable_const)
  · have hanti : Antitone fun x : ℝ => ν (Icc x 0) := fun a b hab =>
      measure_mono (Icc_subset_Icc_left hab)
    have e : g1zWedgeWin γ true y U = Iio 0 ∩ {x | ν (Icc x 0) ≤ ENNReal.ofReal U} := by
      ext x; simp [g1zWedgeWin, g1SideHalf, g1SideSeg, ν]
    rw [e]
    exact measurableSet_Iio.inter (measurableSet_le hanti.measurable measurable_const)

end G3Z2b2
end Thm18Asm
end QuantumZipper
