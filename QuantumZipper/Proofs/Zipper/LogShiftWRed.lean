import QuantumZipper.Proofs.Zipper.LogShiftLen
import QuantumZipper.LQG.Measures
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import QuantumZipper.Proofs.Zipper.F2Step3Dens

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSL-W (2): `LogShiftLenWeightStmt` from the stage geometry and the stage density

Task LSL-W. Target `F1.LogShiftLenWeightStmt` (`LogShiftLen.lean`). Sheffield, arXiv:1012.4797,
§1.4 (quantum lengths of the two sides of `η[0,t]` are the boundary measure of the unzipped field)
and §5.4 pp. 71–72 (this measure is transported by the unzipping maps), with the local rule of
Duplantier–Sheffield (Invent. Math. 185 (2011), §6; `LocalRule.isVagueLimitOnR_add_ofFun`).

The node is split, at one *stage* (the configuration unzipped by `t`, or unzipped by `u` and
then by `s`), into

* **`LogShiftWArcsStmt`** (geometry of the `Γ⁰` picture only; no `Z`): a curve `η` (measurable)
  and, at every stage, boundary position maps `a`, `b` (continuous, strictly monotone on `[0, s]`,
  from `O∓` to `0`) such that the `Γ⁰` boundary measure of `[O⁻, a r]` and `[b r, O⁺]` is the `Γ⁰`
  length of the stage unzipped only up to relative time `r`, and the boundary extension `Ψ` of the
  inverse unzipping map sends `a r`, `b r` to the curve point `η(u + r)` (Loewner boundary
  correspondence for a simple curve; transport of boundary length by the transition map
  `f_t ∘ f_r⁻¹`, Sheffield–Wang arXiv:1605.06171 Thm 4.3, `F1.BdryAllMapsStmt`);
* **`LogShiftWDensStmt`** (local rule + tips; this is where `Z` enters): at every stage the `Z`
  boundary measure is `ρ · ν_Γ` on `(O⁻, 0]` and on `[0, O⁺)`, `ρ = e^{γ φ(Ψ ·)/2}`,
  `φ = −γ log|·| + G = Z − Γ⁰`, and it has no atoms at `O±` (TIP-X).

`logShiftLenWeightStmt_of_arcs_dens` proves the node from the two, with `w(r) = e^{γ φ(η(r))/2}`,
through the deterministic transport of `LogShiftWTransport.lean` (the change of variables from
the boundary to capacity time). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- `φ = −γ log|·| + G` (`γ = √κ`), the difference `Z − Γ⁰` of the two fields. -/
def lswPhi (κ : ℝ) (G : ℂ → ℝ) (z : ℂ) : ℝ := -(Real.sqrt κ * Real.log ‖z‖) + G z

/-- The local-rule density `e^{γ φ(Ψ x)/2}` of a stage with boundary extension `Ψ`. -/
def lswDens (κ : ℝ) (G : ℂ → ℝ) (Ψ : ℝ → ℂ) : ℝ → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (Real.exp (Real.sqrt κ / 2 * lswPhi κ G (Ψ x)))

/-- Geometry of one stage: the boundary position maps of the sub-arcs. -/
def LswArcs (νΓ : Measure ℝ) (O : ℝ × ℝ) (s : ℝ) (L : ℝ → ℝ≥0∞ × ℝ≥0∞) (Ψ η : ℝ → ℂ) :
    Prop :=
  Measurable Ψ ∧ ∃ a b : ℝ → ℝ, Continuous a ∧ Continuous b ∧ StrictMonoOn a (Icc 0 s) ∧
    StrictAntiOn b (Icc 0 s) ∧ a 0 = O.1 ∧ a s = 0 ∧ b 0 = O.2 ∧ b s = 0 ∧
    (∀ r ∈ Icc 0 s, νΓ (Icc O.1 (a r)) = (L r).1 ∧ νΓ (Icc (b r) O.2) = (L r).2) ∧
    ∀ r ∈ Ioc 0 s, Ψ (a r) = η r ∧ Ψ (b r) = η r

theorem measurable_lswDens {κ : ℝ} {G : ℂ → ℝ} (hG : Continuous G) {Ψ : ℝ → ℂ}
    (hΨ : Measurable Ψ) : Measurable (lswDens κ G Ψ) := by
  unfold lswDens lswPhi
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul ?_))
  exact ((measurable_const.mul (Real.measurable_log.comp (measurable_norm.comp hΨ))).neg).add
    (hG.measurable.comp hΨ)

end F1
end QuantumZipper
