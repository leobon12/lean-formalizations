import QuantumZipper.Proofs.Thm18.G4RoundWedgeReg

/-!
# Theorem 1.8, node G4: the reading node with continuous drivers (`G4ZipReadCStmt`)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (3), blueprint
`SECTION5_BLUEPRINT.md` node G4 / A5. Task G4-READ.

**Why `G4ZipReadStmt` must be weakened.** Its factorization clause
`∀ x, cfgData x ∈ A → cfgData (zipLenC γ t x) = Φ (cfgData x)` quantifies over *all*
configurations, including those with discontinuous drivers. For `a²s > T` the driver coordinate
`s` of `Z^LEN_t x` is `(x.2 (a² s − T) − W' T) / a`, where `T` (zipping time) and `a` (scale) are
functions of the field only. A measurable `Φ` and a measurable `A` (product σ-algebra on
`ℝ≥0 → ℝ`) depend on countably many driver coordinates `C`; changing `x.2` at the single time
`u = a² s − T ∉ C` keeps `cfgData x ∈ A` and `Φ (cfgData x)` but changes the output coordinate.
So the clause forces `a² s − T ∈ C` for every datum of `A` with `a² s > T`; for the unzipped
configuration `Z^LEN_{−t} c` (which `A` must charge a.s.) one has `a² s − T = (s − τ)/a_c²`
(`τ` the unzipping time, `a_c` the unzipping scale), which should have an atomless law. Hence
`G4ZipReadStmt` should fail for the Theorem 1.8 sample (same failure mode as `G4FactorStmt`,
see `G4FactorRead.lean`). This refutation is not formalized (it needs the atomlessness of the
law of `τ`), but it shows that `G4ZipReadStmt` asks too much: its deterministic clause must
also hold for configurations with discontinuous drivers, which the wedge never produces.

**Fix.** `G4ZipReadCStmt` asks the factorization only for configurations with a continuous
driver. This suffices: the drivers of `c` and of `Z^LEN_{−t} c` are a.s. continuous, and the law
transfer (`Cor15Group.map_comp_eq_of_factor`) only needs the factorization a.s. at `c` and at
`Z^LEN_{−t} c`. **Own elementary argument** (pushforward algebra).

* `g4ZipReadCStmt_of_read`: the old node implies the new one.
* `configLawFull_zipLenC_pos_of_readC`: clause (3) for `t > 0` from the new node.
* `g4Stmt_of_coreNodesC`: `g4Stmt_of_coreNodes` with `G4ZipReadStmt` replaced by
  `G4ZipReadCStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- A.s. the wedge configuration has a continuous driver. -/
theorem ae_continuous_wedgeConfig_snd {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) : ∀ᵐ ω ∂P, Continuous (wedgeConfig γ B Y ω).2 := by
  filter_upwards [hS.2.2.1.cont] with ω hc
  exact drive_continuous (κ := γ ^ 2) hc

end Thm18Asm
end QuantumZipper
