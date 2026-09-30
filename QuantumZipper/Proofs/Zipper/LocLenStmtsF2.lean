import QuantumZipper.Proofs.Zipper.LocLenBridge
import QuantumZipper.Proofs.Zipper.F2Unscaled
import QuantumZipper.Proofs.Zipper.ScaleGeomFix
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.Zipper.B5LocF1Assembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R4d: local F2 statements

Local copies (FOLLOW-PAPER-13 §1 substitution rule) of four statements consumed by node F2 and
by B5 locality: goodness of an unzipped field at a variable time `t` is required only off the
closed set `offSet W t = {O⁻_t, 0, O⁺_t}` (wedge fields) or off the tip `{0}` (the `Γ⁰` field
`h⁰ + X`, which is `F2.unzY`, `F2.unzippedField_h0rev_eq_unzY`); global vague boundary limits
at a variable time become local ones on `(offSet W t)ᶜ`.

Source: Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper*,
arXiv:1012.4797, p. 56 (boundary lengths are read on arcs away from the tip) and §5.4, p. 70;
Berestycki–Powell, arXiv:2404.16642, Def 6.41 p. 229 (boundary measure on an open segment).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-- Local copy of `F2.UnscaledB3dStmt` (F2Unscaled.lean:67): goodness of the unzipped wedge
field only off `offSet W t`. -/
def UnscaledB3dLocStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P,
      (∀ t, 0 ≤ t → IsLQGGoodOff (Real.sqrt κ)
        (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) t)
        (offSet (drive κ B'' ω) t)) ∧
      ∀ s, 0 ≤ s → RegEq
        (unzippedField (Real.sqrt κ)
          (canonConfig (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)) s)
        (rescale (unzippedField (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)
            (scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω) ^ 2 * s))
          (Qc (Real.sqrt κ)) (scaleParam (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω)))

/-- Local copy of `F2.ScaleGeomAeStmt'` (ScaleGeomFix.lean:61): the unzipped `Γ⁰` field
`h⁰ + X` (`= F2.unzY`) is good off the tip `{0}`. -/
def ScaleGeomAeLocStmt' : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ a : ℝ, 0 < a →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      IsLQGGoodOff (Real.sqrt κ)
        (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) (a ^ 2 * t)) {0} ∧
      (∃ l, Tendsto (fun r : ℝ => (fwdMap (drive κ B ω) (a ^ 2 * t) r).re)
        (𝓝[<] (0 : ℝ)) (𝓝 l)) ∧
      (∃ l, Tendsto (fun r : ℝ => (fwdMap (drive κ B ω) (a ^ 2 * t) r).re)
        (𝓝[>] (0 : ℝ)) (𝓝 l)) ∧
      RegEq (unzippedField (Real.sqrt κ)
          (ofFun (h0rev κ) + addConst (rescale (X ω) (Qc (Real.sqrt κ)) a)
              (2 / Real.sqrt κ * Real.log a),
            fun s => drive κ B ω (a ^ 2 * s) / a) t)
        (rescale (unzippedField (Real.sqrt κ)
            (ofFun (h0rev κ) + X ω, drive κ B ω) (a ^ 2 * t))
          (Qc (Real.sqrt κ)) a)

/-- Local copy of `B5.WedgeUnzipLimitStmt` (B5LocF1Assembly.lean:92): local vague boundary
limits of the unzipped wedge field at the times `1/(m+1)` on `(offSet W t)ᶜ`. -/
def WedgeUnzipLimitLocStmt (γ α κ : ℝ) : Prop :=
  0 < κ → κ < 4 → γ = Real.sqrt κ → α < Qc γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample) (A : ℝ → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure P → IsFreeGFFModConstH X P →
    IsWedgeProcess α (Qc γ) A P → IsBrownianReal B P → (∀ t, Measurable (A t)) →
    (∀ t, Measurable (B t)) → iIndep (srcSigma X A B) P →
    ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ ν, IsVagueLimitOnR (offSet (drive κ B ω) (GermZeroOne.epsSeq m : ℝ))ᶜ
      (bdryApprox γ (unzippedField γ (unscaledConfig γ κ X A B ω) (GermZeroOne.epsSeq m : ℝ))) ν

end LocLen
end QuantumZipper
