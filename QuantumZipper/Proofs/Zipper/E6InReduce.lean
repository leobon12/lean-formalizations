import QuantumZipper.Proofs.Zipper.E6NodeMain
import QuantumZipper.Proofs.Zipper.F1StrictMonoAllT
import QuantumZipper.Proofs.Zipper.B3dStmt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E6 inputs: reductions of `LenCollidedAllStmt`, `CanonZipRawAllStmt`, `E6PalmRegStmt`

Theorem 1.3, node E6 (Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.4, pp. 70–72). `E6.e6NodeStmtRich_of_nodes` (`E6NodeAsm.lean`) takes five inputs. This file
reduces three of them:

* `lenCollidedAllStmt_of_extAll`, `lenCollidedAllStmt_of_ext_levMoment`: `LenCollidedAllStmt`
  from the **same two analytic inputs at every horizon** that already feed the F1 strict
  monotonicity capstone (`F1.lenStrictMonoStmt_of_allHorizonInputs`,
  `F1.lenStrictMonoStmt_of_ext_levMoment`): `RegUnif.AnchorUnifFamExtAllStmt` (Sheffield–Wang
  arXiv:1605.06171 Thm 4.3) and the tip input (`UnifTipRatAllStmt`, or its level-moment form
  `TipLevMomentAllStmt`). Wiring only (`unifWindowAll_unifAtomlessAll_of_extAll` +
  `RegUnif.lenCollidedStmt_holds`), no new frontier node.
* `canonZipRawStmt_of_reg`, `canonZipRawAllStmt_of_reg`: the raw zip algebra from the
  `ConfigEq` zip algebra (`E6.canonZipStmt_of`, whose field cocycle is closed by D33,
  `RegUnif.capCocycleAddStmt_holds`, and whose B3(b)/B3(d) half is `B3d.ZipLenInputsStmt`)
  plus the **raw-regularity node** `CanonZipRegStmt`: both sides of the zip identity have raw
  values (at the `coordsFull` circles and test densities) equal to their regularized values.
  `ConfigEq` alone does not give `RawEq` (decision D25: `ConfigEq` only sees `avgReg`), so this
  node is exactly the extra content of the raw form. The deterministic bridge
  `rawEq_of_configEq_of_rawRegular` is an own elementary argument.
* `e6PalmGoodStmt_of_flow`, `e6PalmRegStmt_of_flow`: the Palm side of B5 locality from the
  **uniform-in-time good behaviour of the capacity flow** `FlowGoodAllStmt`: a.s., for every
  capacity time `u ∈ [0, T]` and every constant `k`, the canonicalized constant-shifted
  configuration `canonConfig γ (C_u + k)` (`C_u = zipCapDown γ u 𝒵`) is `HitScaleGood`. Every
  zoomed collided configuration `Z_C C̄_x` (`τ_x < T`) is of this form, with `u = T − τ_x` and
  `k = −m + C/γ`; this is definitional. The Palm measure and `ϖ` disappear.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 D3Plus

/-! ## 1. `LenCollidedAllStmt` from the F1 analytic inputs at every horizon -/

/-! ## 2. The raw zip algebra from the `ConfigEq` zip algebra and raw regularity -/

/-- **Raw regularity of a field sample**: its raw values at all `coordsFull` circles and its raw
pairings with all test functions supported in `ℍ` equal the regularized values (`evalReg`,
`pairTest`), i.e. the data read by `cfgFull` are functions of the regularized circle averages. -/
def RawRegular (x : FieldSample) : Prop :=
  (∀ i : ℕ, CoordsFull.coordsFull x i =
      evalReg x (foldedCircle (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2)) ∧
    ∀ ρ : TestFun H, pairRaw x ρ.1 = pairTest x ρ.1

/-- `evalReg` reads the field only through `avgReg`. -/
theorem evalReg_congr_of_regEq {x y : FieldSample} (h : RegEq x y) (ν : Measure ℂ) :
    evalReg x ν = evalReg y ν := by
  have e : (fun k : ℕ => ∫ w, avgReg x k w ∂ν) = fun k : ℕ => ∫ w, avgReg y k w ∂ν :=
    funext fun k => by simp only [h k]
  unfold evalReg
  rw [e]

/-- **`ConfigEq` + raw regularity of both fields gives `RawEq`** (own elementary argument). -/
theorem rawEq_of_configEq_of_rawRegular {a b : Cfg} (h : ConfigEq a b) (ha : RawRegular a.1)
    (hb : RawRegular b.1) : RawEq a b := by
  have hE := evalReg_congr_of_regEq h.1
  show cfgFull a = cfgFull b
  unfold cfgFull
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext i
    show CoordsFull.coordsFull a.1 i = CoordsFull.coordsFull b.1 i
    rw [ha.1 i, hb.1 i, hE]
  · funext ρ
    show pairRaw a.1 ρ.1 = pairRaw b.1 ρ.1
    rw [ha.2 ρ, hb.2 ρ]
    unfold pairTest
    rw [hE, hE]
  · funext t
    exact h.2 t t.2

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## 3. The Palm side of B5 locality from the uniform-in-time flow statement -/

end QuantumZipper.E6
