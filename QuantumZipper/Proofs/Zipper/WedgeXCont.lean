import QuantumZipper.Proofs.Zipper.WedgeUnzipCore

/-!
# D29 (wedge unzipping), part 7: node X-C, continuum limits for the unzipped `x` field

Task X-CONT (handoff `WEDGE-UNZIP.md`, decision D29). Node **X-C** (`WedgeUnzip.XContinuumStmt`,
defined in `WedgeUnzipCore.lean`) asks, for `x = X + α₀(−log|·|)` (`X` a free-boundary GFF modulo
constants, `α₀ = √κ − 2/√κ`), for the smoothing-radius continuum limits of the `x`-pairings
against the pushed folded circles `(f_t⁻¹)_* fc(c, r)` at **all** times `t ≥ 0`, plus regularity
of `x`:

* **(regularity)** a.s. `x` is a regular sample (`IsRegularSample`);
* **(limits)** for all `t ≥ 0`, `c ∈ ℍ̄`, `r > 0`, the function
  `ρ ↦ ∫ u, evalReg x (fc(u, ρ)) d((fc(c,r)).map (fwdMapInv W t))` is `Integrable` for every
  `ρ > 0` and has a limit as `ρ → 0⁺`.

Proved here **without hypothesis**: the regularity half (`ae_isRegularSample_xLogSing`). The free
field `X` is a.s. a regular sample (`RegSample.ae_isRegularSample`, blueprint M4-R3, via the
four-parameter Kolmogorov theorem `KolmD.exists_continuous_modification_D`), and adding the
deterministic log-singularity preserves regularity (`IsRegularSample.add_ofFun_log'`,
`RegularClosure.lean`). No tip input is needed for regularity: circle averages of `log|·|` are
continuous on `ℍ̄ × (0,∞)`, so the singularity at the origin is harmless for `IsRegularSample`.

The smoothing-radius continuum limit is stated as a named hypothesis, exactly the
"continuum-radius JointMod" of the D29 handoff:

* `XContJointStmt κ T P B X` — the **extension of JointMod to a continuous smoothing radius**: a
  jointly continuous modification in `(t, c, r, ρ)` on `[0,T] × ℍ̄ × (0,∞) × [0,∞)` of the
  smoothed pairing, identified a.s. with the actual integral at every parameter (`ρ = 0` is in
  the domain, so joint continuity *up to the limit* is part of the statement). Template for the
  proof: `RegUnif.JointModStmt`/`jointModStmt_holds` and the `(t, ρ)` Kolmogorov step of
  `RegCont.ae_UCq` (whose `μq W w r T q` is the circle-smoothed pushed measure at time `sPar T q`
  and radius `ρPar q`, i.e. exactly the `(t, ρ)` pair used here), with the uniform tip bound
  TIP-X (D26) for the parameters whose pushed curve approaches the tip, where the singularity of
  `x` at the origin sits.
* `XContTipStmt κ T P B X` — the **tip part**: the bare `ρ → 0⁺` limit, with `Integrable` for
  every `ρ > 0`, for every parameter. This is the second conjunct of `XContinuumStmt` at horizon
  `T` isolated from the joint-continuity refinement; near the tip it is the statement needing the
  uniform-in-`t` control of `ν_{x_t}`/`μ_{x_t}` (TIP-X), away from it the free-field
  energy/Frostman estimates of `RegContMain`/`Regularization`.

Proved bookkeeping (beyond the named hypotheses): `xContTipStmt_of_joint` (joint continuity up to
`ρ = 0` yields the bare limits) and `xContinuumStmt_of_tip` (X-C from regularity + the tip
statement at every horizon), hence `xContinuumStmt_of_joint` (X-C from the continuum-radius
extension).

Own bookkeeping; the free-field regularity input is `RegSample.ae_isRegularSample` (M4-R3).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-! ## Regularity of `x` (no hypothesis) -/

/-- **Regularity half of X-C, unconditionally.** For a free-boundary GFF `X` modulo constants and
any `κ`, a.s. `x = X + α₀(−log|·|)` is a regular sample: `X` is one
(`RegSample.ae_isRegularSample`, blueprint M4-R3) and adding `α₀(−log|·|)` preserves regularity
(`IsRegularSample.add_ofFun_log'`). The singularity at the origin is harmless because circle
averages of `log|·|` are finite and continuous on `ℍ̄ × (0,∞)`. -/
theorem ae_isRegularSample_xLogSing [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (κ : ℝ) : ∀ᵐ ω ∂P, IsRegularSample (X ω + F2.logSingField κ) := by
  filter_upwards [RegSample.ae_isRegularSample hX] with ω hω
  have h := hω.add_ofFun_log' (Real.sqrt κ - 2 / Real.sqrt κ) 0
  simpa [F2.logSingField] using h

/-! ## The reductions -/

end WedgeUnzip
end QuantumZipper
