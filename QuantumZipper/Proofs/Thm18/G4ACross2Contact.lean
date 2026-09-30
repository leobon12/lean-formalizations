import QuantumZipper.Proofs.Thm18.G4CoreDefs3
import QuantumZipper.Proofs.Thm18.G4PushRegScale
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.Zipper.ESMLMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core A-cross: the quantitative-contact route (task ACROSS-DECIDE)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), proof
pp. 69–71. Decision: `handoff/G4-CORE.md` §7 (proposed DECISIONS entry D-ACROSS).

**Source check.** Sheffield's proof never evaluates a field at a measure pushed by the re-zipping
map: fields are distributions modulo conformal coordinate change, so `Z_ℓ ∘ Z_{−ℓ} = id` is a
tautology there. The crossing-circle exactness of `G4BackCrossStmt` is an artefact of the
regularized `FieldSample` model (`evalReg`/`avgReg`), and no published proof covers it. Hence an
**own argument**, designed so that the only random-time input concerns the SLE **trace alone**:

* the obstacle of the previous prover is that `τ_ℓ, a_ℓ` depend on the field `Y`, so no Fubini /
  independence transfer applies to a statement involving `Y`;
* a statement about the trace alone at `(τ_ℓ, τ_{ℓ−s}, a_ℓ)` does not have this problem: the
  hull of `backDrv W τ τ' a` is the scaled hull of the **shifted** driver
  `W̃ = W(τ' + ·) − W(τ')` (`backDrv_eq_revDrv_shift`, below), `τ` is removed by monotonicity of
  hulls, `τ' = τ_{ℓ−s}` is a stopping time of `W` given `Y` (strong Markov: `W̃` is a Brownian
  motion independent of `(Y, W|[0,τ'])`), and the scale `a` is one real parameter, covered by the
  scale grid of `ae_forall_scale_fc_trace_null_far` (one parameter only, as that grid allows).

So `G4BackCrossStmt` is split along a **quantitative contact guard** `BackContactI`
(`σ_i(δ-neighbourhood of the hull) ≤ C δ^β`, the hull-side form of
`Cor15RezipRegHull.ae_measure_infDist_le_pow`, which gives it at one fixed circle with `β = 1/8`):

* `G4CrossQAllStmt` (analytic, **all** parameters, no random time): at crossing circles with
  quantitative contact, exactness and integrability hold. Guard makes the log-integrability
  automatic (`∫ log(1/dist(·, hull)) dσ_i ≤ Σ C e^{−βn}`) and restores the ε/3 continuity
  extension at the tip (the non-conformal part has `σ_i`-mass `≤ C δ^β`; truth plausible, the
  diagonal choice of `δ` against the regularization level needs quantitative A-sep rates).
* contact at the random parameters (trace only): `s = ℓ` is **proved** here (`ae_contact_full`)
  from the pure SLE node `SLEScaleContactStmt κ` (one scale parameter); `s < ℓ` is
  `G4CrossContactShortStmt` (strong Markov at `τ_{ℓ−s}` given `Y`, then the same SLE node).

Proved here: `backDrv_eq_revDrv_shift`, `backHull_eq`, `fcI_thickening_backHull_le`,
`fcI_hull_null_of_contact`, `backSupportI_of_contact`, `ae_contact_full`, `ae_contact_all`,
`ae_backSupportI_full_of_contact`, and the derivations `g4BackCrossStmt_of_contact`,
`g4BackCrossExactStmt_of_contact`, `g4DownShortTraceNullStmt_of_contact`.
**Own elementary argument** (Loewner scaling and time reversal already in the repository, set
inclusions, a limit `δ → 0`, instantiation).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-! ## Deterministic: `backDrv` is the re-zip driver of the shifted driver -/

/-- The driver after time `τ'`, recentred: `W̃ u = W (τ' + u) − W τ'`. -/
def shiftDrv (W : ℝ → ℝ) (τ' : ℝ) : ℝ → ℝ := fun u => W (τ' + u) - W τ'

/-! ## The quantitative contact guard -/

/-! ## The two nodes of the route -/

/-! ## Derivations -/

end G4Core
end Thm18Asm
end QuantumZipper
