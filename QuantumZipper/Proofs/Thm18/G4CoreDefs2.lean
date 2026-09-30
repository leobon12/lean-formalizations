import QuantumZipper.Proofs.Thm18.G4PushReg2Exact
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.Thm18.G4PushReg2Exact
import QuantumZipper.Proofs.Thm18.G4CoreDownLong
import QuantumZipper.Proofs.Thm18.G4RezipNodes
import QuantumZipper.Proofs.Thm18.G4WeldUniq
import QuantumZipper.Proofs.Thm18.G4CoreUpShort
import QuantumZipper.Proofs.Thm18.G4Rezip2Weld

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 consolidation (task G4-CONSOLIDATE): the core statements

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 and its proof
(§5.4, pp. 69–72). Route decision and derivations: `handoff/G4-CORE.md`.

The G4 leaves split into

* **Group I** — statements about the wedge configuration `c = (Y, W)` read at a random unzipping
  time `τ_ℓ` (maps built from the SLE driver `W`). They are instances of **all-parameter**
  statements about the process `(Y, W)`:
  - Core A `G4DriverPushExactAllStmt` (analytic): exactness of the unzipped field at the dyadic
    folded circles pushed by `a · revMapInv (backDrv W τ τ' a)`, for all `0 ≤ τ' ≤ τ`, `a > 0`,
    **guarded** by the support condition at the same circle (without the guard the statement
    can fail at exceptional parameters: the junk value `revMapInv = 0` puts an atom at `0`);
  - Core A' `G4DownShortTraceNullStmt` (analytic, LW-FAR type): the support condition at the
    random parameters of `Z_s ∘ Z_{−ℓ}` (fixed `s, ℓ`; not in all-parameter form, which is a
    trap: positive-length intersections of the trace with circles at exceptional scales are not
    excluded by any available estimate);
  - Core B `G4UnzipSideAllStmt` (length transport): equal side lengths of every sub-arc
    `η[τ − r, τ]` and positivity of `ν_{U_τ}` on `[0,∞)`, for all `τ ≥ 0`.
* **Group II** — statements about zipping up the wedge by its own length-welding drivers. They
  all follow from Core C `G4ZipUpGoodStmt`: for every `t > 0`, a.s. a good length-`t` welding
  driver exists, the zipped configuration `Z_t c` is **Group-I good** (`Group1Good`), and
  `Z_{−t} (Z_t c) = c`. Every Group II property of `(c, p)` is a Group I property of `Z_t c`
  read at its unzipping time `τ_t (Z_t c) = p.1 / b²`.

This file contains the definitions and the two instantiations of Core B
(`g4UnzipSideLenStmt_of_all`, `g4UnzipBdryPosRightStmt_of_all`). **Own elementary argument**
(instantiation at `τ = τ_ℓ`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-! ## Core A: driver-pushed exactness at all parameters (guarded) -/

/-- Support condition at the `i`-th dyadic folded circle for the re-zipping driver
`backDrv W τ τ' a`: `σ_i` is carried by the image `revMap (backDrv …) '' H`. -/
def BackSupportI (c : FieldSample × (ℝ → ℝ)) (τ τ' a : ℝ) (i : ℕ) : Prop :=
  fcI i (revMap (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1 '' H)ᶜ = 0

/-- Exactness and integrability data at the `i`-th dyadic folded circle for the map
`ψ = revMapInv (backDrv W τ τ' a)` at free parameters `(τ, τ', a)`: the rescaled unzipped field
`rescale U_τ Q a` is exact at `σ_i.map ψ`, `U_τ` is exact at `σ_i.map (a ψ)`, and
`log|(f_τ⁻¹)'(a ψ)|`, `log|ψ'|` are `σ_i`-integrable. At `a = scaleParam γ U_τ` these are the
last four conjuncts of `DownShortRegAt` (and, at `τ' = 0`, the two conjuncts of `UpZipRegAt`,
since `backDrv W τ 0 a = revDrv W τ a`). -/
def DriverPushExactI (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) (τ τ' a : ℝ) (i : ℕ) : Prop :=
  evalReg (rescale (unzippedField γ c τ) (Qc γ) a)
      ((fcI i).map (revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1)) =
    rescale (unzippedField γ c τ) (Qc γ) a
      ((fcI i).map (revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1)) ∧
  evalReg (unzippedField γ c τ)
      ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1 w) =
    unzippedField γ c τ
      ((fcI i).map fun w => (a : ℂ) * revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1 w) ∧
  Integrable (fun w => Real.log ‖deriv (fwdMapInv c.2 τ)
    ((a : ℂ) * revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1 w)‖) (fcI i) ∧
  Integrable (fun w => Real.log ‖deriv
    (revMapInv (backDrv c.2 τ τ' a).2 (backDrv c.2 τ τ' a).1) w‖) (fcI i)

/-! ## Core A': support at the random parameters of `Z_s ∘ Z_{−ℓ}` -/

/-! ## Core B: side lengths and boundary positivity at all unzipping times -/

/-! ## Core C: the zipped configuration is Group-I good -/

/-! ## Derivations: Group I leaves from Core B -/

end G4Core
end Thm18Asm
end QuantumZipper
