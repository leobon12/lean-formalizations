import QuantumZipper.Proofs.Zipper.F1EmbedBasic
import QuantumZipper.Proofs.LQG.WedgeRestriction
import QuantumZipper.Proofs.LQG.WedgeMeasurable

/-!
# Theorem 1.3, F1c: the embedding step `F1EmbedStmt`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4 (p. 71, F1c: the 0-1
law is run on the unscaled wedge `(wedgeField (lateralPart X) A Q, √κ B)`) and §5.1 (pp. 60–62,
B3(d): the canonical description is the unscaled one rescaled by the random scale
`a = scaleParam`); blueprint `E_BRANCH_BLUEPRINT.md` §F1 (F1c).

`f1EmbedStmt_of` proves `F1.F1EmbedStmt` from
* `F2.UnscaledB3dStmt` (B3(d) side conditions for the unscaled configuration),
* `ReadLenAEMeasStmt` (the measurable reader `readLen` of the lengths at time `1`),
* `Thm18Asm.UnzipBdryPosStmt` (positivity of the unzipped boundary measure).

Construction (own bookkeeping; D27 measurable versions): given a `P_*` sample `(Y, B')` on `Ω'`,
take the representation `(X, A)` of the wedge `Y` on `Ω₁` (the definition of `IsQuantumWedge`),
replace the two Brownian motions of `A` and `B'` by jointly measurable continuous versions
(`WedgeRes.exists_good_version`, `WedgeMeas.measurable_wedgePath_joint`), and put
`X, A` on the first and `B` on the second factor of `Ω₁ × Ω'`. The canonical `P_*` sample
`(Y₀, B₀)` of this unscaled configuration (`FSMeas.pstar_of_unscaled_fs`) satisfies
`L⁺ = f₀ L⁻` (hypothesis `HLinAllStmt`), which transfers to the unscaled configuration by
B3(d) (`ae_unzipLengths_transfer`) with `g = f₀`; `f₀` is a.s. the ratio of `(Y₀, B₀)` at time `1`;
and `(Y₀, B₀)`, `(Y, B')` have the same configuration law (same field law by construction, same
Brownian path law), which determines the law of the ratio through `readLen`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- A Brownian motion has a measurable, everywhere continuous version, again a Brownian motion. -/
theorem exists_meas_brownian_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ b : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (b t)) ∧ (∀ ω, Continuous fun s => b s ω) ∧
      IsBrownianReal b P ∧ pathOf b =ᵐ[P] pathOf B := by
  obtain ⟨b, hbm, hbc, hbe⟩ := WedgeRes.exists_good_version hB
  exact ⟨b, fun t => hbm.of_uncurry_left, hbc,
    { toIsPreBrownianReal := hB.toIsPreBrownianReal.congr fun s => hbe.mono fun ω h => (h s).symm
      cont := ae_of_all _ hbc }, hbe.mono fun ω h => funext fun s => h s⟩

end F1
end QuantumZipper
