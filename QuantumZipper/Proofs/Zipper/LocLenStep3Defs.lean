import QuantumZipper.Proofs.Zipper.LocLenF2Chain
import QuantumZipper.Proofs.Zipper.F2Step3Dens
import QuantumZipper.Proofs.Zipper.LogShiftWRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R7a: F2 step (3) with open arcs (statements)

Open-arc copies (substitution rule of `handoff/FOLLOW-PAPER-13.md` §1) of the two inputs of
`F2.step3_of_local` (F2Step3.lean): `F2.Step3LocalDensityStmt` and `F2.Step3WeldStmt`. With the
local boundary measures on `(offSet W t)ᶜ = ℝ ∖ {O⁻_t, 0, O⁺_t}` the endpoint-atom clauses
disappear (a local measure on `(offSet)ᶜ` does not charge `offSet`).

Two further statements split the welding input into its two ingredients (both proved in the R7a
files, they are not frontier nodes):
* `Step3InvDensityArcStmt`: rule (5.1) in the direction `x_t = y_t − γ log|F_t|`, i.e.
  `ν_{x_t} = |F_t|^{−γ²/2} ν_{y_t}` on `(offSet)ᶜ` (Sheffield arXiv:1012.4797 p. 70 and §5.1 rule
  (5.1); B-P arXiv:2404.16642 Def 6.41 p. 229);
* `Step3GammaArcsStmt`: stage geometry of the `Γ⁰` picture with open-arc lengths (copy of the
  first clause of `F1.LogShiftWArcsStmt`, LogShiftWRed.lean:99, with the local `Γ⁰` measure on
  `(offSet)ᶜ` and `unzipLengthsArc`), plus finiteness of the `Γ⁰` open-arc lengths.

Paper: Sheffield arXiv:1012.4797 §5.4 pp. 70–72.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **Open-arc copy of `F2.Step3LocalDensityStmt`** (rule (5.1) at the unzipped level, no endpoint
atom clauses): a.s., for all `t ≥ 0`, `O⁻_t ≤ 0 ≤ O⁺_t`, `x_t`, `y_t` are regular, and their local
boundary limits `νx`, `νy` on `(offSet W t)ᶜ` exist and satisfy `νy = |F_t|^{γ²/2} νx`. -/
def Step3LocalDensityArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (sideImages (drive κ B ω) t).1 ≤ 0 ∧ 0 ≤ (sideImages (drive κ B ω) t).2 ∧
      IsRegularSample (F2.unzX κ (X ω) (drive κ B ω) t) ∧
      IsRegularSample (F2.unzY κ (X ω) (drive κ B ω) t) ∧
      ∃ νx νy : Measure ℝ,
        HasBdryLimitOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) t)
          (offSet (drive κ B ω) t)ᶜ νx ∧
        HasBdryLimitOn (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t)
          (offSet (drive κ B ω) t)ᶜ νy ∧
        νy = νx.withDensity
          (fun w => F2.logDens (Real.sqrt κ) (F2.invBdry (drive κ B ω) t w))

/-- **Rule (5.1), inverse direction**: as `Step3LocalDensityArcStmt` with
`νx = e^{γ/2·(−γ log|F_t|)} νy` (`F1.lswDens κ 0`). -/
def Step3InvDensityArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (sideImages (drive κ B ω) t).1 ≤ 0 ∧ 0 ≤ (sideImages (drive κ B ω) t).2 ∧
      IsRegularSample (F2.unzX κ (X ω) (drive κ B ω) t) ∧
      IsRegularSample (F2.unzY κ (X ω) (drive κ B ω) t) ∧
      ∃ νx νy : Measure ℝ,
        HasBdryLimitOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) t)
          (offSet (drive κ B ω) t)ᶜ νx ∧
        HasBdryLimitOn (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t)
          (offSet (drive κ B ω) t)ᶜ νy ∧
        νx = νy.withDensity (F1.lswDens κ (fun _ => 0) (F2.invBdry (drive κ B ω) t))

/-- **Stage geometry of the `Γ⁰` picture with open arcs** (copy of the first clause of
`F1.LogShiftWArcsStmt`): a measurable curve `η` such that at every horizon `t ≥ 0` the boundary
position maps of the sub-arcs of `η[0,t]` exist for the local `Γ⁰` measure of `y_t` on
`(offSet W t)ᶜ` and the open-arc lengths of `B2.cfg`; and these lengths are finite. -/
def Step3GammaArcsStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, (∀ r : ℝ, 0 ≤ r →
        (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) r).1 ≠ ⊤ ∧
        (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) r).2 ≠ ⊤) ∧
      ∃ η : ℝ → ℂ, Measurable η ∧ ∀ t : ℝ, 0 ≤ t →
        F1.LswArcs (qBoundaryMeasureOn (Real.sqrt κ) (F2.unzY κ (X ω) (drive κ B ω) t)
            (offSet (drive κ B ω) t)ᶜ)
          (sideImages (drive κ B ω) t) t
          (fun r => unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) r)
          (fun x => F2.extInv (drive κ B ω) t x) η

/-- **Open-arc copy of `F2.Step3WeldStmt`** (welding invariance of the local boundary measure of
`x_t` on `(offSet)ᶜ`, integrals over the open arcs). -/
def Step3WeldArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t₀ M : ℝ,
      SmallTimeAgreeArc (Real.sqrt κ) (X ω + F2.logSingField κ) (drive κ B ω) t₀ M →
      ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → (∀ r ∈ Icc (0 : ℝ) t, |drive κ B ω r| ≤ M) →
      ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ w in Ioo (sideImages (drive κ B ω) t).1 0, g (F2.invBdry (drive κ B ω) t w)
          ∂qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) t)
            (offSet (drive κ B ω) t)ᶜ =
        ∫⁻ w in Ioo 0 (sideImages (drive κ B ω) t).2, g (F2.invBdry (drive κ B ω) t w)
          ∂qBoundaryMeasureOn (Real.sqrt κ) (F2.unzX κ (X ω) (drive κ B ω) t)
            (offSet (drive κ B ω) t)ᶜ

end LocLen
end QuantumZipper
