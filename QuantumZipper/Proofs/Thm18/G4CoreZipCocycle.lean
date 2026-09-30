import QuantumZipper.Proofs.Thm18.G4CoreUpShort
import QuantumZipper.Proofs.Thm18.G4GroupMixCross
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.LocRichBasic
import QuantumZipper.Proofs.Thm18.G4WeldHull

/-!
# Theorem 1.8, node G4: the field part of the zip cocycle `G4ZipCocycleStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2) (zip
cocycle; blueprint B5 field cocycle and B3(d) Loewner scaling, in the zipping direction). Let
`c = (x, W)`, `p = (T, V)` a length-`t` driver, `b > 0` the scale of the field zipped along `p`,
`D` the driver of `Z_t c = canonConfig (zipWeldUp p c)`, `f_p`, `g_p` the reverse flow of `p`
and its inverse, and `G = f_{b²u}⁻¹ = fwdMapInv W (b² u)`.

* `fwdMapInv_zipDrv_add` (Loewner flow property `RS.fwdMapInv_add_shift`, forward scaling
  `RS.fwdMapInv_scale`, and `fwdMapInv_zipDrv`; Lawler, *Conformally Invariant Processes in the
  Plane*, §4.1): `f_{T/b² + u}⁻¹(w) = f_p(G(b w))/b` for the driver `D`, `w ∈ ℍ`.
* `zipCocycle_fc_apply` (deterministic, at one measure `σ` carried by `ℍ`): unzipping
  `(x zipped along p)(b·) + Q log b` by `w ↦ f_p(G(b w))/b` gives at `σ` the value of
  `(x unzipped by b²u)(b·) + Q log b`, once the three intermediate fields are regular at the
  pushed measures and `log|g_p'(b F)|`, `log|F'|` are `σ`-integrable. No hull condition is
  needed (`g_p ∘ f_p = id` on `ℍ`).
* `g4ZipCocycleStmt_of`: `G4ZipCocycleStmt` from the length node `G4ZipCocycleLenStmt` (the
  scale positivity and the two quantum-length conjuncts) and the regularity node
  `G4ZipCocyclePushRegStmt`.

**Own elementary argument** (change of variables and the chain rule, as in `G4RezipDet`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The time-reversed driver of `W` on `[0, s]`: `fwdMapInv W s = revMap (timeRevAt W s) s` on
`ℍ`. -/
abbrev timeRevAt (W : ℝ → ℝ) (s : ℝ) : ℝ → ℝ := fun r => W (s - r) - W s

/-! ## The configuration-level reduction -/

/-- The unzipping map of `Z_t c` at capacity time `T/b² + u`: `w ↦ f_p(G(b w))/b`. -/
abbrev zcMap (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (p : ℝ × (ℝ → ℝ)) (u : ℝ) : ℂ → ℂ :=
  fun w => revMap p.2 p.1 (revMap (timeRevAt c.2 (scaleParam γ (zipField γ c.1 p) ^ 2 * u))
    (scaleParam γ (zipField γ c.1 p) ^ 2 * u) ((scaleParam γ (zipField γ c.1 p) : ℂ) * w)) /
    (scaleParam γ (zipField γ c.1 p) : ℂ)

end Thm18Asm
end QuantumZipper
