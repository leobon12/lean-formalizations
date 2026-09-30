import QuantumZipper.Proofs.Thm18.G3FidMass
import QuantumZipper.Proofs.LQG.FirstMoment

/-!
# G3 fidelity F3: finiteness of `E ν_h[−δ, 0]` reduced to the unit-normalized free field

Sheffield, arXiv:1012.4797, Theorem 1.8; Duplantier–Sheffield arXiv:0808.1560 §6. The residual
F3 input `Thm18Asm.G3HonestFinStmt` (`G3FidMass.lean`) is the finiteness of the expected
boundary length `E ν_h[−δ, 0]` of the Theorem 1.2 field `h = normField γ X₀`.

This file reduces it to the corresponding statement for the *unit-normalized free field*
`zField X₀ 1` (`G3HonestFinOneStmt`), i.e. the `R = 1` case of the free-field first-moment
finiteness `FirstMoment.lintegral_qBoundaryMeasure_Icc_lt_top` — the case excluded by the
library's window condition `N + 2 ≤ R`, because the mean `(2/γ) log |·|` of `h` is singular at
`0`.

Route: the log-singularity theorem (`G3FidHonest.qBoundaryMeasure_normField_restrict`,
`LogSing.ae_logSingularity`, Duplantier–Sheffield arXiv:0808.1560 §6) gives a.s.

  `ν_h = |t| · ν_{zField X₀ 1}`  on `ℝ ∖ {0}`,

so on `[−δ, 0]` (where `|t| ≤ δ`) the honest mass is dominated by `δ` times the mass of the
unit-normalized free field:

* `qBoundaryMeasure_normField_Icc_le`: a.s. `ν_h(Icc (−δ) 0) ≤ ofReal δ · ν_{zF 1}(Icc (−δ) 0)`;
* `G3HonestFinOneStmt`: the `R = 1` first-moment finiteness for `zField X₀ 1`;
* `g3HonestFinStmt_of_zFieldOne`: `G3HonestFinOneStmt ⟹ G3HonestFinStmt`.

The remaining input is therefore a *non-singular* free-field statement (no log singularity in the
mean). Its level-`k` computation is available in the library: `PalmFree.variance_zG_fc` gives,
for `R = 1` and `|x| + radius k ≤ 1` (automatic for `x ∈ [−1/4, 0]` and large `k`, since
`i.δ ≤ 1/4`),

  `Var[zG X 1 (fcK x k)] + 2 log (radius k) = 2 log 1 = 0`,

so the level-`k` first-moment density `PalmFormula.rhoK γ 0 (zG X 1) P x k` is identically `1`
and the level-`k` expectation of `∫ f d(bdryApprox γ (zField X 1) k)` is `∫ f`. The `k → ∞`
passage (Fatou + the a.s. vague limit `ae_isVagueLimitR_qBoundaryMeasure_zField`) is what
remains for `G3HonestFinOneStmt`; see the report.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open K3

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- **F3, honest mass dominated by the unit-normalized free field.** A.s., on `[−δ, 0]` the
honest boundary measure of `h = normField γ X₀` is dominated by `δ` times the boundary measure
of `zField X₀ 1`: the log-singularity theorem writes `ν_h = |t| · ν_{zF 1}` off `{0}`, and
`|t| ≤ δ` on `[−δ, 0]`. -/
theorem qBoundaryMeasure_normField_Icc_le {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {δ : ℝ}
    (_hδ : 0 ≤ δ) :
    ∀ᵐ ω ∂gffBase.P,
      qBoundaryMeasure γ (normField γ X₀ ω) (Icc (-δ) 0) ≤
        ENNReal.ofReal δ *
          qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Icc (-δ) 0) := by
  filter_upwards [qBoundaryMeasure_normField_restrict (X := X₀) gffBase.gff hγ hγ2] with ω hω
  set ν₁ := qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) with hν₁
  rw [hω, withDensity_apply _ measurableSet_Icc]
  calc ∫⁻ t in Icc (-δ) 0, ENNReal.ofReal |t| ∂(ν₁.restrict {0}ᶜ)
      ≤ ∫⁻ _ in Icc (-δ) 0, ENNReal.ofReal δ ∂(ν₁.restrict {0}ᶜ) := by
        refine setLIntegral_mono measurable_const fun t ht => ENNReal.ofReal_le_ofReal ?_
        rw [abs_of_nonpos ht.2]
        linarith [ht.1]
    _ = ENNReal.ofReal δ * (ν₁.restrict {0}ᶜ) (Icc (-δ) 0) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal δ * ν₁ (Icc (-δ) 0) := by
        refine mul_le_mul' le_rfl ?_
        rw [Measure.restrict_apply measurableSet_Icc]
        exact measure_mono Set.inter_subset_left

/-- **The residual F3 finiteness input in non-singular form**: the expected boundary length of
the *unit-normalized* free field `zField X₀ 1` on `[−δ, 0]` is finite. This is the `R = 1` case
of the free-field first-moment finiteness (`FirstMoment.lintegral_qBoundaryMeasure_Icc_lt_top`,
whose window condition `N + 2 ≤ R` forces `R ≥ 2`), for the radius-`1` normalization of
Theorem 1.2's field. -/
def G3HonestFinOneStmt (γ : ℝ) (i : G3Idx) : Prop :=
  ∫⁻ ω, qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Icc (-i.δ) 0) ∂gffBase.P < ⊤

/-- **F3 finiteness from the unit-normalized free-field first moment**: the honest expected
boundary length of `h = normField γ X₀` on `[−δ, 0]` is finite as soon as
`G3HonestFinOneStmt` holds. -/
theorem g3HonestFinStmt_of_zFieldOne {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h : G3HonestFinOneStmt γ i) : G3HonestFinStmt γ i := by
  have hδ0 : 0 ≤ i.δ := (i.hη.trans i.hηδ).le
  have hle : ∫⁻ ω, qBoundaryMeasure γ (normField γ X₀ ω) (Icc (-i.δ) 0) ∂gffBase.P ≤
      ENNReal.ofReal i.δ *
        ∫⁻ ω, qBoundaryMeasure γ (BdryExist.zField X₀ 1 ω) (Icc (-i.δ) 0) ∂gffBase.P :=
    (lintegral_mono_ae (qBoundaryMeasure_normField_Icc_le (γ := γ) hγ hγ2 hδ0)).trans_eq
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h)

end Thm18Asm
end QuantumZipper
