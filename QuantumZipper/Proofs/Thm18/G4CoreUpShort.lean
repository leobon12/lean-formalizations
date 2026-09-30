import QuantumZipper.Proofs.Thm18.G4CoreDownShort
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.LocRichBasic
import QuantumZipper.Proofs.Thm18.G4WeldHull
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood

/-!
# Theorem 1.8, node G4: the partial-unzip identity of the core `G4UpShortCoreStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2), case
`s < 0 < t`, `−s < t` (the paper gives no proof). Let `c = (x, W)`, `p = (T, V)` a length-`t`
driver, `q = (T_q, V)` its restriction to `[0, T_q]`, `b > 0` the scale of the field zipped along
`p`, `D` the driver of `Z_t c = canonConfig (zipWeldUp p c)` and `s' = (T − T_q)/b²`. With
`f_p, f_q` the reverse flows, `g_p, g_q` their inverses and `f_S` the reverse flow of the shifted
driver `Ṽ r = V(T_q + r) − V(T_q)` on `[0, T − T_q]`:

* `fwdMapInv_zipDrv_mid` (Loewner time reversal and scaling, Lawler, *Conformally Invariant
  Processes in the Plane*, §4.1; generalizes `fwdMapInv_zipDrv` from `s' = T/b²`):
  `f_{s'}⁻¹ = z ↦ f_S(b z)/b` on `ℍ` for the driver `D`.
* `revMap_split_restrict` (flow composition, `TwoPoint.revMap_concat_eq`): `f_p = f_S ∘ f_q`.
* `unzipShort_fc_apply` (deterministic, at one measure `σ`): unzipping `(x zipped along p)(b·) +
  Q log b` by `z ↦ f_S(b z)/b` gives at `σ` the value of `(x zipped along q)(b·) + Q log b`,
  once `b·σ` is carried by `f_q(ℍ)`, the three intermediate fields are regular at the pushed
  measures, and `log|g_p'(b F)|`, `log|F'|` are `σ`-integrable.

**Own elementary argument** (change of variables and the chain rule, as in `G4RezipDet`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The shifted driver `Ṽ r = V(T_q + r) − V(T_q)`. -/
abbrev shiftDrvAt (V : ℝ → ℝ) (Tq : ℝ) : ℝ → ℝ := fun r => V (Tq + r) - V Tq

/-! ## The configuration-level reduction -/

/-- The partial unzipping map `F(w) = f_S(b w)/b` of `Z_t c` at time `(T − T_q)/b²`. -/
abbrev usMap (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (p q : ℝ × (ℝ → ℝ)) : ℂ → ℂ :=
  fun w => revMap (shiftDrvAt p.2 q.1) (p.1 - q.1)
    ((scaleParam γ (zipField γ c.1 p) : ℂ) * w) / (scaleParam γ (zipField γ c.1 p) : ℂ)

end Thm18Asm
end QuantumZipper
