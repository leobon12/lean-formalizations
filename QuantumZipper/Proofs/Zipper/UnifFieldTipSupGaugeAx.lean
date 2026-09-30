import QuantumZipper.Proofs.Zipper.UnifFieldTipSupGauge

/-!
# FIELD-TIPSUP: the gauge shift preserves the `IsFreeGFFModConstH` hypotheses

Companion to `UnifFieldTipSupGauge` (the gauge equivariance of `fieldTipSup`). This file proves
the other half of the obstruction to `RegUnif.FieldTipSupStmt`: the **hypotheses** of the node are
invariant under the additive-constant gauge `X ↦ X + C · mass` for an *arbitrary measurable*
`C : Ω → ℝ`. The axioms of `IsFreeGFFModConstH` (GFF/Defs.lean) constrain only balanced pairs
`X μ − X ν` (`μ univ = ν univ`), where the gauge cancels, so:

* the centred Gaussian process of differences is pointwise unchanged (`gaussian`),
* the means and covariances are unchanged (`centered`, `covariance_eq`),
* `linear` is preserved by the mass identity `((a • μ + b • ν) univ).toReal
  = a (μ univ).toReal + b (ν univ).toReal` (`toReal_univ_nnreal_smul_add`).

Together with `UnifFieldTipSupGauge.fieldTipSup_shiftField`
(`fieldTipSup (x + c·mass) = e^{√κ c} · fieldTipSup x`), this shows that
`RegUnif.FieldTipSupStmt κ p` cannot be deduced from its hypotheses: for `√κ · p > 0` and a gauge
`C` with `∫⁻ e^{p√κ C} = ⊤` (e.g. `C = −log U`, `U` uniform, independent of the field and the
driver) all the hypotheses of the node hold, while the conclusion `∫⁻ (fieldTipSup)^p ≠ ⊤` fails.
Repairing the node requires pinning the gauge (e.g. requiring the joint law of `(ZE q)_q` to be
the centred Gaussian vector with covariance `kernelCov2 neumannH (ν4 q) (ν4 q')`), not just the
gauge-invariant axiom set.

"Own elementary argument": the measure/`ENNReal` bookkeeping.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- Mass identity used for the `linear` axiom of the shifted field:
`((a • μ + b • ν) univ).toReal = a (μ univ).toReal + b (ν univ).toReal`. -/
theorem toReal_univ_nnreal_smul_add (a b : ℝ≥0) (μ ν : Measure ℂ) (hμ : μ Set.univ ≠ ⊤)
    (hν : ν Set.univ ≠ ⊤) :
    ((a • μ + b • ν) Set.univ).toReal =
      (a : ℝ) * (μ Set.univ).toReal + (b : ℝ) * (ν Set.univ).toReal := by
  have h1 : (a • μ) Set.univ = (a : ℝ≥0∞) * μ Set.univ := by
    rw [← Measure.coe_nnreal_smul, Measure.smul_apply, smul_eq_mul]
  have h2 : (b • ν) Set.univ = (b : ℝ≥0∞) * ν Set.univ := by
    rw [← Measure.coe_nnreal_smul, Measure.smul_apply, smul_eq_mul]
  rw [Measure.add_apply, h1, h2,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hμ)
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hν),
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp

/-- **The gauge shift preserves the hypotheses**: if `X` is a free GFF modulo constants then so is
`X + C · mass`, for every measurable `C : Ω → ℝ` (in particular for a gauge with heavy tails). -/
theorem isFreeGFFModConstH_shiftField {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (C : Ω → ℝ) (hC : Measurable C) :
    IsFreeGFFModConstH (fun ω => shiftField (C ω) (X ω)) P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro μ
    exact (hX.measurable_coord μ).add (hC.mul measurable_const)
  · have hfun : (fun (p : {p : Measure ℂ × Measure ℂ //
          IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}) (ω : Ω) =>
        (fun ω => shiftField (C ω) (X ω)) ω p.1.1 -
          (fun ω => shiftField (C ω) (X ω)) ω p.1.2) =
        (fun (p : {p : Measure ℂ × Measure ℂ //
          IsAdmissibleH p.1 ∧ IsAdmissibleH p.2 ∧ p.1 Set.univ = p.2 Set.univ}) (ω : Ω) =>
          X ω p.1.1 - X ω p.1.2) := by
      funext p ω
      simp only [shiftField_apply]
      rw [← p.2.2.2]
      ring
    rw [hfun]
    exact hX.gaussian
  · intro μ ν hμ hν hm
    have hfun : (fun ω => shiftField (C ω) (X ω) μ - shiftField (C ω) (X ω) ν) =
        fun ω => X ω μ - X ω ν := by
      funext ω
      simp only [shiftField_apply]
      rw [← hm]
      ring
    rw [hfun]
    exact hX.centered μ ν hμ hν hm
  · intro p q hp1 hp2 hpm hq1 hq2 hqm
    have h1 : (fun ω => shiftField (C ω) (X ω) p.1 - shiftField (C ω) (X ω) p.2) =
        fun ω => X ω p.1 - X ω p.2 := by
      funext ω
      simp only [shiftField_apply]
      rw [← hpm]
      ring
    have h2 : (fun ω => shiftField (C ω) (X ω) q.1 - shiftField (C ω) (X ω) q.2) =
        fun ω => X ω q.1 - X ω q.2 := by
      funext ω
      simp only [shiftField_apply]
      rw [← hqm]
      ring
    rw [h1, h2]
    exact hX.covariance_eq p q hp1 hp2 hpm hq1 hq2 hqm
  · intro μ ν hμ hν a b
    filter_upwards [hX.linear μ ν hμ hν a b] with ω hω
    have hmass := toReal_univ_nnreal_smul_add a b μ ν hμ.1.measure_univ_lt_top.ne
      hν.1.measure_univ_lt_top.ne
    simp only [shiftField_apply]
    rw [hω, hmass]
    ring

end RegUnif
end QuantumZipper
