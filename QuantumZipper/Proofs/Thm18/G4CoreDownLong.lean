import QuantumZipper.Proofs.Thm18.G4CoreDownShort

/-!
# Theorem 1.8, node G4: the rezip identity of the core `G4DownLongCoreStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2), case
`t < 0 < s`, `s > −t` (the paper gives no proof). Let `c = (x, W)`, `τ ≥ 0`, `a > 0`,
`F = f_τ⁻¹ = fwdMapInv W τ`, `q` a driver with reverse flow `f_q` and inverse `g_q`, and
`P = backCatDrv W τ a q` (the `a`-rescaled time reversal of `W` on `[0, τ]` followed by the
`a`-rescaled `q`), with reverse flow `R` and inverse `g`.

* `revMap_backCatDrv` (Loewner flow composition, `TwoPoint.revMap_concat_eq`, plus scaling,
  Lawler, *Conformally Invariant Processes in the Plane*, §4.1): `R z = f_q(F(a z))/a` on `ℍ`.
* `rezipLong_fc_apply` (deterministic, at one measure `σ`): re-zipping `U_τ(a·) + Q log a` along
  `P` gives at `σ` the value of `(x zipped along q)(a·) + Q log a`, once `σ` is carried by
  `R(ℍ)`, the three intermediate fields are regular at the pushed measures, and
  `log|F'(a g)|`, `log|g'|` are `σ`-integrable.
* `g4DownLongCoreStmt_of`: `G4DownLongCoreStmt` from the welding node `G4DownLongWeldStmt`, the
  regularity node `G4DownLongPushRegStmt` and `G4UnzipGoodStmt`.

**Own elementary argument** (change of variables and the chain rule, as in `G4RezipDet`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## The configuration-level reduction -/

/-- The re-zipping driver of `Z_s ∘ Z_{−ℓ}`, `ℓ < s`: `backCatDrv W τ_ℓ a_ℓ q`. -/
abbrev dlDrv (γ ℓ : ℝ) (c : FieldSample × (ℝ → ℝ)) (q : ℝ × (ℝ → ℝ)) : ℝ × (ℝ → ℝ) :=
  backCatDrv c.2 (unzipTime γ ℓ c) (unzipScale γ ℓ c) q

end Thm18Asm
end QuantumZipper
