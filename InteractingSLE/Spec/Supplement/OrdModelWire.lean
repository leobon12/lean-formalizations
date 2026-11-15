/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdModelLeaf
import InteractingSLE.Spec.Supplement.OrdModelMatch

/-!
# Leaf 3's second continuation without the arbitrary-stop extension

Packet PROVE-T15-ASTOP2. PROVE-T15-ASTOP's `RLC.retOrdDetSndStatement_of_stoppedModels` takes, besides the model
statement and Theorem 1.3, the arbitrary-stop extension `StoppedExtend.StoppedHullExtendStatement` (defective, R79).
Here the A-stopped models also carry their code rule (`HasCodeHistoryRule`, the A-stop rule of the killed history given
the code; the constructor `exists_stoppedModelTransferJ_rule_of_aStop` supplies it), and the R79-safe consumer
`ae_codeMatch_of_finite_stoppedModelsJ_rule` needs Theorem 1.3 only:

* `exists_stoppedModelTransferJ_rule_of_sourceInputs`;
* `RLC.RetOrdStoppedModelsSndRStatement` (models with code rules), `RLC.retOrdStoppedModelsSndRStatement_of_source`;
* **`RLC.retOrdDetSndStatement_of_stoppedModelsR`** and **`RLC.retOrdDetSndStatement_of_source`**:
  `RetOrdAStopSourceSndStatement → Exist.Theorem13Statement → RetOrdDetSndStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace RLC.OrdModel

open LQGMetric (DistOn TestOn)
open Restart Restart.RetAux79 OrdAStop

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω]

/-- **The A-stopped model with its code rule from source inputs.** -/
theorem exists_stoppedModelTransferJ_rule_of_sourceInputs {κ θ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {M : Set Ω} {c : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞}
    {γ : Ω → ℝ≥0 → ℂ} {Sd : Ω → ℝ} (h : AStopSourceInputs κ θ P M Sd c Hc V γ) (hPM : P M ≠ 0) :
    ∃ T : StoppedModelTransferJ κ θ P M c Hc V γ, HasCodeHistoryRule T.model ∧
      ∃ seed : T.model.space → ℝ, Measurable[T.model.data.filt 0] seed ∧ ∀ ω, seed (T.read ω) = Sd ω := by
  obtain ⟨a, 𝓗, W, E, V', γ', hM, hc, hHc, hWc, hW0, hWa, hVs, hγm, hγc, hγ0, hE, hSd, hag, htype, hint, hS,
    hL, hg, hVpos, hthr, hoff, hend⟩ := h
  obtain ⟨T, hT⟩ := exists_stoppedModelTransferJ_rule_of_aStop a hM hPM hc hHc hWc hW0 hWa hVs hγm hγc hγ0 hE
    hSd htype hint hS hL hg hVpos hthr hoff hend
  exact ⟨congrTransferJ T hag, hT⟩

end RLC.OrdModel

namespace RLC

open Supp7 Supp9D Restart LQGMetric Sec7.Lemma76F OrdAStop OrdModel

universe u

/-- **A-stopped models of the second continuation with their code rules** (the R79-safe form of
`RetOrdStoppedModelsSndStatement`). -/
def RetOrdStoppedModelsSndRStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ (d : RetData Ω) (hd : d.IsMeasGood),
      (∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) →
    ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension b jumps u₀ →
    ∀ β : Ω → BoundaryWord × ℝ, Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β →
      IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
        {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} (fun ω => (β ω).1) →
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        (β ω).1.IsSorted ∧ (β ω).2 = tipPos d η₁ ω ∧ 0 < (β ω).2 ∧
        IsRetainedWord κ θ₁ θ₂ (η₁ ω) d.u (η₂ ω) d.r (d.inv ω) (β ω).1 ∧
        IsUntouchedWord b jumps (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) (d.inv ω) (β ω).1) →
    ∃ (n : ℕ) (M : Fin n → Set Ω), (∀ i, MeasurableSet (M i)) ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ∃ i, ω ∈ M i) ∧
      ∀ i, P (M i) ≠ 0 → ∃ T : StoppedModelTransferJ κ θ₂ P (M i) (fun ω => (β ω).1)
        (hd.chartField κ h)
        (fun ω => canonRetLife (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0)
        (fun ω => canonRetPath (d.D ω) (d.fwd ω) (η₂ ω) (ζ₂ ω) d.r (η₁ ω '' Icc 0 d.u ∪ η₂ ω '' Icc 0 d.r) 0),
        HasCodeHistoryRule T.model

/-- The R79-safe model statement from source inputs. -/
theorem retOrdStoppedModelsSndRStatement_of_source (hsrc : RetOrdAStopSourceSndStatement.{u}) :
    RetOrdStoppedModelsSndRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hword
  obtain ⟨n, M, hM, hcover, hsource⟩ := hsrc κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hag u₀ hu₀ β hβ hmean hword
  exact ⟨n, M, hM, hcover, fun i hi =>
    let ⟨T, hT, _⟩ := exists_stoppedModelTransferJ_rule_of_sourceInputs (hsource i hi) hi
    ⟨T, hT⟩⟩

/-- **(Det) for the second continuation from A-stopped models with code rules and Theorem 1.3** (no arbitrary-stop
extension, R79). -/
theorem retOrdDetSndStatement_of_stoppedModelsR (h13 : Exist.Theorem13Statement.{0})
    (hmodels : RetOrdStoppedModelsSndRStatement.{u}) : RetOrdDetSndStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag F₂ hF₂ u₀ hu₀
    β hβ hmean hword
  obtain ⟨n, M, hM, hcover, hmodel⟩ := hmodels κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    d hd hag u₀ hu₀ β hβ hmean hword
  exact ae_codeMatch_of_finite_stoppedModelsJ_rule
    (F := {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r}) hM hcover hmodel h13 hκ hF₂

/-- **(Det) for the second continuation from its A-stopped source inputs and Theorem 1.3.** -/
theorem retOrdDetSndStatement_of_source (h13 : Exist.Theorem13Statement.{0})
    (hsrc : RetOrdAStopSourceSndStatement.{u}) : RetOrdDetSndStatement.{u} :=
  retOrdDetSndStatement_of_stoppedModelsR h13 (retOrdStoppedModelsSndRStatement_of_source hsrc)

end RLC

end InteractingSLE
