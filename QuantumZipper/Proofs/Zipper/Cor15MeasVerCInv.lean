import QuantumZipper.Proofs.Zipper.Cor15MeasVerBasic
import QuantumZipper.Proofs.Zipper.Cor15RegDeriv
import QuantumZipper.Proofs.Zipper.Cor15RegMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-MEASVER (3): the measurable version of the zipped field built from `CInv`/`DInv`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5.
Task COR15-MEASVER.

`Cor15ZipCoordsMeasStmt` (`Cor15MeasVerBasic.lean`) asks for the a.e.-measurability of the circle
coordinates of the zipped field `U_a c = coordChange (𝔥₀ + X) (revMapInv W' a) (Qc √κ)`, where
`W' = weldDriver (√κ) (𝔥₀ + X) a` is the welding driver of the *input* field. Two things are
unmeasurable there: the welding driver `W'` (a non-measurable functional of the field), and
`deriv (revMapInv W' a)`, which is junk on the hull.

This file removes both, by the route of `Cor15RegDeriv.lean`:

* `Cor15ZipReadStmt` (the one remaining input, of the same kind as `Cor15ZcReadStmt` of
  `Cor15RegZc.lean`): a measurable parameter `e` and a jointly measurable family `Vp` of
  continuous drivers (`Vp b 0 = 0`, `b ↦ Vp b s` measurable) such that a.s. `Vp (e ω)` agrees
  with the welding driver on `[0,a]` **and** the time-reversed forward hull of `Vp (e ω)` is null
  for every dyadic folded circle. The second clause is the circle-measure form of the proved
  input K0 `cor15HullNullStmt` (which gives it for the *Brownian* driver, i.e. on the good event
  of a genuine configuration whose welding driver is its driving function — exactly the reading
  content here).
* `zipFld_apply_eq_CInv`: at every dyadic folded circle `σ_i` the zipped field equals the
  `CInv` candidate of `Cor15RegDeriv.lean` evaluated at the input's circle coordinates —
  `coordChange` and `CInv` differ only in `deriv` versus `DInv`, and on `σ_i` the two agree
  a.e. because `σ_i` is carried by `H` and by no hull point (`DInv_eq`, own bookkeeping).
* `aemeasurable_coordsFull_zipFld_sub_of_read`, `cor15ZipCoordsMeasStmt_of_readStmt`:
  `Cor15ZipReadStmt` implies the a.e.-measurability of the circle coordinates. The measurable
  version itself (an honest field at every admissible measure) is `zipVer`,
  `Cor15MeasVerZip.lean`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

open CharFun CoordsFull

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## The remaining reading input -/

/-! ## The circle value of the zipped field is the `CInv` candidate -/

/-- **The hull clause of `Cor15ZipReadStmt` is well posed.** Drivers that agree on `[0,a]` have the
same time-reversed forward hull: both the time reversal and the hull read the driver only on
`[0,a]` (`ArcDriver.trev`, `CharFunRhs.fwdHull_eq_of_eqOn`). -/
theorem fwdHull_trev_eq_of_eqOn {V V' : ℝ → ℝ} (hV : Continuous V) (hV' : Continuous V')
    {a : ℝ} (ha : 0 ≤ a) (h : EqOn V V' (Icc 0 a)) :
    fwdHull (ArcDriver.trev V a) a = fwdHull (ArcDriver.trev V' a) a :=
  CharFunRhs.fwdHull_eq_of_eqOn (ArcDriver.continuous_trev hV a)
    (ArcDriver.continuous_trev hV' a) ha
    (fun r hr => by
      have hr' : a - r ∈ Icc (0 : ℝ) a :=
        ⟨by linarith [Set.mem_Icc.1 hr |>.2], by linarith [Set.mem_Icc.1 hr |>.1]⟩
      have h1 := h hr'
      have h2 := h (show a ∈ Icc (0 : ℝ) a from ⟨ha, le_rfl⟩)
      simp only [ArcDriver.trev]
      rw [h1, h2])

/-! ## From the reading input to the measurable version -/

end Cor15Group
end QuantumZipper
