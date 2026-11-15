/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm13Inputs6
import InteractingSLE.Spec.Sec7.Lemma71CFromMid
import InteractingSLE.Spec.Sec7.StripHeights44
import InteractingSLE.Spec.Sec7.AdmissibleFlowCode
import InteractingSLE.Spec.Sec7.StripDetPath
import InteractingSLE.Spec.Exist.StagedAssembly

/-!
# Theorem 1.3 from the current inputs, with Lemma 7.1 discharged

Theorem 1.3's Lemma 7.1 pocket-chart input is supplied by the proved Lemma71T route from the Proposition 4.11 and
Proposition 5.1 inputs. The R56 height-extended strip data are also wired into the R48-safe determination of the
two-piece strip history.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Wire

/-- Theorem 1.3's trace conclusion with Lemma 7.1's chart-form input derived from Propositions 4.11 and 5.1. -/
theorem ae_exists_isGeneratingTrace_of_open7
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ)
    {a : ℝ} (ha : 0 < a := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by assumption) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  exact ae_exists_isGeneratingTrace_of_open6
    (Sec7.Lemma71CFromMid.lemma71PocketChartStatement_of_prop411Q_of_prop51Q h411 h51)
    hC4 hR7 hPW hA2 hA2' ha hF hE

/-- Theorem 1.3 as `Exist.Theorem13Statement`, with Lemma 7.1 supplied by its proved route. -/
theorem theorem13Statement_of_open7
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ) : Exist.Theorem13Statement.{u} := by
  intro _ ha _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ hE
  exact ae_exists_isGeneratingTrace_of_open7 h411 h51 hC4 hR7 hPW hA2 hA2' ha hF hE

/-- R56's height-carrying strip data supply the two (4.4) hypotheses to R48-safe driver determination. -/
theorem exists_borel_drivers_of_stripHeights44
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {θ₀ θ : ℝ} (t₀ : ℝ≥0)
    (hS : Sec7.StripHeights44.IsStripSystemWithHeights44 κ b jumps P h W' ζ' E θ₀ θ)
    (hreg : ∀ j ω, InteractingSLE.Exist.Staged.IsRegularDriver
      (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) j ω))
    (hθ : θ₀ ≤ θ) (hθπ : θ ≤ θ₀ + Real.pi) :
    ∃ D₀ D₁ : LQGMetric.DistOn upperHalfPlaneOpens → (ℝ≥0 → ℝ) × ℝ≥0∞,
      Measurable D₀ ∧ Measurable D₁ ∧ (∀ f, InteractingSLE.Exist.Staged.IsRegularDriver (D₀ f)) ∧
        (∀ f, InteractingSLE.Exist.Staged.IsRegularDriver (D₁ f)) ∧ ∀ᵐ ω ∂P,
          (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω).2 = ⊤ ∧
            (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 1 ω).2 = ⊤ ∧
              E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 0 ω = D₀ (h ω) ∧
                E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ) 1 ω = D₁ (h ω) := by
  have hstage : IsStagedHistory κ b jumps P h (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)
      (E (Sec7.StripSys.twoAngleSpec θ₀ t₀ θ)) :=
    hS.system.staged _ (Sec7.StripSys.isBoundaryContinuedProgram_twoAngleProg
      hS.startAngle_mem hS.finishAngle_mem t₀)
  exact Sec7.StripDet.exists_borel_drivers h44 hS.system.kappa_pos hS.system.kappa_lt_four
    hS.system.boundaryData hS.system.gff hstage hreg hS.heights.atStart.1 hS.heights.atStart.2
    hS.heights.atFinish.1 hS.heights.atFinish.2 hθ hθπ

end InteractingSLE.Wire

end
