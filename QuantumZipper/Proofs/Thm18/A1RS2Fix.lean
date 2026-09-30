import QuantumZipper.Proofs.Thm18.A1RSGenFam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS2 (1): the fixed-driver continuum limit of the smeared-loop pairings at rational parameters

Toward `A1RFSmearContStmt` (A1RFSmear.lean). For a fixed good driver `W`, Hölder on `[0, b₀]`,
and a free field `X`, on every rational parameter box `ratBox a b` inside the open parameter set
`smearU = {t > 0, s > 0}`:

**`ae_smear_cauchy_fixed`**: almost surely, for every `n` there is `N` such that for all rational
radii `0 < r < 1/(N+1)` and all rational parameters `q` of the box,
`|evalReg X (ν_{q,r}) − evalReg X (ν_{q,0})| < 1/(n+1)`, where `ν_{q,ρ} = smearFam W left q ρ`.

This is Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (continuous modification by Kolmogorov–Čentsov, Revuz–Yor 3rd ed. Ch. I Thm (2.1)) for
the family `ν_{q,ρ}`: the `GenFam` bounds `genFam_smearFam_ratBox` feed the GENERIC-UC engine
`GenUC.ae_unifConv_countable`, the fixed-parameter exactness `ae_evalReg_eq_smearFam` is its
identity input (at `ρ > 0`) and identifies its limit (at `ρ = 0`). The statement is countable in
the parameters, so it is a measurable event (for the transfer to the Brownian driver).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

/-- The open parameter set `{t > 0, s > 0}` of the smeared-loop family. -/
def smearU : Set (Fin 4 → ℝ) := {p | 0 < p 0 ∧ 0 < p 3}

/-- The real point of a rational parameter. -/
def ratPt (q : Fin 4 → ℚ) : Fin 4 → ℝ := fun i => (q i : ℝ)

end A1RS
end R18
end QuantumZipper
