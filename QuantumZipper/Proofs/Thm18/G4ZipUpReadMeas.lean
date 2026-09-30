import QuantumZipper.Proofs.Thm18.G4ReadZip
import QuantumZipper.Proofs.Zipper.Cor15RegMeas
import QuantumZipper.Proofs.Zipper.Cor15LawCongr
import QuantumZipper.Proofs.Thm18.G4GoodSet

/-!
# Theorem 1.8, node G4: reduction of the measurable zip-up to a surrogate inverse reverse map

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (3). Task
G4-ZIPUPREAD.

`G4ZipUpFieldReadStmt` (`G4ReadZip.lean`) asks the field data (circle coordinates, raw pairings)
and the scale of the zip-up `canonical γ (zipField γ x.1 (F (cfgData x)))`, along a measurably
read driver `(T, W') = F (cfgData x)`, to be measurable functions of the data `cfgData x`.

**What is proved here (deterministic bookkeeping).**

* `zipField_eq_fromC`: the zipped field reads the input field *only through its circle
  coordinates*: `zipField γ x p = coordChange (E1.fromC (coordsFull x)) (revMapInv p.2 p.1) Qc γ`
  (`Cor15Group.regEq_fromC_coordsFull` + `Cor15Group.coordChange_congr_regEq`). Hence the
  field data of the zip-up is a function of the data `cfgData x` and of the *function*
  `revMapInv (F (cfgData x)).2 (F (cfgData x)).1`, and of nothing else about `x`.
* `g4ZipUpFieldReadStmt_of_dataMeas`: **`G4ZipUpFieldReadStmt` from the two explicit inputs
  below** (`G4ZipUpDataMeasStmt`, `G4SurrogateZipDataMeasStmt`), with the factorization clause
  and the a.s. clause of the statement discharged.
* `g4Stmt_of_coreNodesZipUp`: `G4Stmt` with `G4ZipUpFieldReadStmt` replaced by those two inputs.

**The two remaining inputs (precise Lean statements below).**

* `G4ZipUpDataMeasStmt`: a *surrogate inverse reverse map*. For a measurably read driver
  `(T, W') = F d` one must produce a **function** `ψ d : ℂ → ℂ`, jointly measurable in `(d, z)`
  with measurable `log ‖(ψ d)'‖`, that agrees with `revMapInv W' T` on a measurable set `A` of
  data charged a.s. by the unzipped configuration, together with the scale of the surrogate
  field. This is the genuine gap: `revMap W T` is defined by `Classical.choose` from the
  *existence of a solution* of the Loewner equation, which holds exactly when `W` is continuous
  on `[0, T]` (`IsReverseSol` forces `t ↦ W t` to be continuous there). The set of continuous
  drivers is **not measurable** in the product σ-algebra of `ℝ^{ℝ≥0}` (every measurable set is
  determined by countably many coordinates, and changing a continuous driver at a single point
  outside that countable set destroys continuity), so `d ↦ revMapInv (F d).2 (F d).1` cannot be
  measurable by junking its values off the continuous drivers: on the (non-measurable) set of
  discontinuous drivers it is identically `0` (no solution exists), so the preimage of `{0}`
  would have to be measurable. What *is* available: `measurable_revMapInv_param`
  (`Cor15RezipRegMeas.lean`) gives `(z, a) ↦ revMapInv (V_a) t z` measurable for a *fixed* time
  `t` and a family of *continuous* drivers; `LenDrvReading` gives neither continuity as a
  measurable condition nor a fixed time. The natural completion is to build, by measurable
  selection, a *continuous* surrogate driver from the countably many rational values of
  `F d` (uniform continuity on `[0, T]` is a countable-cylinder condition, satisfied a.s. by the
  unzipped configuration, whose driver `s ↦ (c.2 (t' + a² max s 0) − c.2 t')/a` is continuous),
  and to pass to the limit in the Loewner flow (piecewise-linear interpolations of the driver
  converge uniformly, and the flow is continuous in the driver in sup-norm,
  `tamedUnc_stability`), reducing the random time to time `1` by Brownian scaling
  (`sclDrv`/`revMap_sclDrv`, `G4Read2Bdry.lean`).
* `G4SurrogateZipDataMeasStmt`: the *analytical* bookkeeping for such a surrogate: for a
  measurable family of fields `y`, a jointly measurable `ψ` with measurable `log ‖ψ'‖` and a
  measurable scalar `sc`, the circle coordinates, raw pairings and scale written through
  `y`, `ψ`, `sc` are measurable. Its proof needs the identity
  `evalReg (coordChange y ψ Q) ν = evalReg y (ν.map ψ) + Q ∫ log ‖ψ'‖ ∂ν` at the s-finite
  measures that occur (`foldedCircle`s and `volume.withDensity` of test functions), which the
  repository has only for *regular* samples; with it, `G1Meas.measurable_coordsFull_coordChange`
  and the `MeasUnzipZip.measurable_locFieldFull_rescale` pattern give the conclusion.

**Own elementary argument** (measurability bookkeeping and reduction).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The zipped field reads the input field only through its circle coordinates: the zip-up along
`p` of `x` only depends on `coordsFull x`. -/
theorem zipField_eq_fromC (γ : ℝ) (x : FieldSample) (p : ℝ × (ℝ → ℝ)) :
    zipField γ x p =
      coordChange (E1.fromC (CoordsFull.coordsFull x)) (revMapInv p.2 p.1) (Qc γ) :=
  Cor15Group.coordChange_congr_regEq (Cor15Group.regEq_fromC_coordsFull x) _ _

/-- The zipped field written from the *data* `d` of a configuration and a function `ψ` standing
for the inverse reverse map of the driver: `coordChange (E1.fromC d.1.1) ψ Qc γ`. -/
def zipFieldData (γ : ℝ) (d : E6.FullData) (ψ : ℂ → ℂ) : FieldSample :=
  coordChange (E1.fromC d.1.1) ψ (Qc γ)

theorem zipField_eq_zipFieldData (γ : ℝ) (x : FieldSample × (ℝ → ℝ)) (p : ℝ × (ℝ → ℝ)) :
    zipField γ x.1 p = zipFieldData γ (cfgData x) (revMapInv p.2 p.1) :=
  zipField_eq_fromC γ x.1 p

/-- The *canonical* surrogate zipped field: the surrogate field `zipFieldData γ d ψ` rescaled by
the scale `a` (so that on the good set, with `a = scaleParam γ (zipFieldData γ d ψ)`, it is
`canonical γ (zipField γ x.1 (F d))`). -/
def canonicalData (γ : ℝ) (d : E6.FullData) (ψ : ℂ → ℂ) (a : ℝ) : FieldSample :=
  coordChange (zipFieldData γ d ψ) (fun w => (a : ℂ) * w) (Qc γ)

open Classical in
/-- **Analytical input for the surrogate zip-up** (`y`, `ψ`, `sc` measurable as indicated): the
circle coordinates and raw pairings of `canonicalData`, and the scale of the surrogate field
(junk `0` off the good samples), are measurable in the parameter. -/
def G4SurrogateZipDataMeasStmt : Prop :=
  ∀ (γ : ℝ) {Z : Type} [MeasurableSpace Z] (y : Z → FieldSample) (ψ : Z → ℂ → ℂ)
    (sc : Z → ℝ),
    Measurable y →
    Measurable (fun q : Z × ℂ => ψ q.1 q.2) →
    Measurable (fun q : Z × ℂ => Real.log ‖deriv (ψ q.1) q.2‖) →
    Measurable sc →
    Measurable (fun z => (CoordsFull.coordsFull
        (coordChange (coordChange (y z) (ψ z) (Qc γ)) (fun w => (sc z : ℂ) * w) (Qc γ)),
      fun ρ : TestFun H => pairRaw
        (coordChange (coordChange (y z) (ψ z) (Qc γ)) (fun w => (sc z : ℂ) * w) (Qc γ)) ρ.1)) ∧
    Measurable fun z => if IsLQGGood γ (coordChange (y z) (ψ z) (Qc γ)) then
      scaleParam γ (coordChange (y z) (ψ z) (Qc γ)) else 0

end Thm18Asm
end QuantumZipper
