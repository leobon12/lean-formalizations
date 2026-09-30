import QuantumZipper.Proofs.Zipper.FieldLawlerCoverDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-EXCLOWER: interface definitions

Task FL-EXCLOWER (helper of FL-THM, D75): prove `FieldLawler.FLExcLowerStmt`
(`FieldLawlerCoverDefs.lean`), the lower bound `ℰ_ℍ(η, ℝ₋) ≥ c (diam η / |a| ∧ 1)` used in the
proof of L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
Prop. 3.1 (p. 7), which they take from their Corollary 5.2.

Route: normalize by the similarity `flSim σ m : z ↦ (σ Re z + i Im z)/m` (`σ = ±1`, `m > 0`),
which maps `ℍ` onto `ℍ` and preserves harmonic measures and excursion integrals (conformal
invariance of the excursion measure, Lawler, *Conformally invariant processes in the plane*,
§5.2), to a crosscut from `−1` to `a ≤ −1`, where the lower half of the key estimate of
Lawler–Werness, Ann. Probab. 41 (2013), proof of Lemma 4.3 (p. 24), proved in the repository
(`lw3_circle`, `lw3_outer`), works without the hypothesis `diam η ≤ 1/2` once `r` is taken
`≍ diam η ∧ 1`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The similarity `z ↦ (σ Re z + i Im z)/m` (for `σ = ±1`, `m > 0`: `z ↦ z/m` or
`z ↦ −conj z/m`). Its inverse is `flSim σ m⁻¹`. -/
def flSim (σ m : ℝ) (z : ℂ) : ℂ := ⟨σ * z.re / m, z.im / m⟩

/-- The normalized lower bound: a crosscut from `−1` to `a ≤ −1` (any diameter). -/
def FLExcNormStmt : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (η : ℝ → ℂ) (a : ℝ) (h : ℂ → ℝ),
    IsCrosscutH η → Tendsto η (𝓝[>] 0) (𝓝 (-1 : ℂ)) → Tendsto η (𝓝[<] 1) (𝓝 (a : ℂ)) →
    a ≤ -1 → IsHarmMeas (hullComp η) (arcH η) h →
    ENNReal.ofReal (c * min (Metric.diam (arcH η)) 1) ≤ excR h (Ici 0)

end FieldLawler
end QuantumZipper
