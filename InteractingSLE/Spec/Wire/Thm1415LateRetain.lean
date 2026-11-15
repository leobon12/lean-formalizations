/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetFinModels
import InteractingSLE.Spec.Restart.Aux54Loc

/-!
# Retained determination with the stopped-model construction discharged

The old arbitrary-stop extension premise is not retained. The exact remaining
model determination is named separately. Migrating that model's stopped K2
consumer to the R79 regular rule is still required; the corrected extension
cannot be substituted for the old premise by type coercion.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)
namespace InteractingSLE.Wire
open Restart Restart.RetAux79 Sec2.Assembly Sec7.PocketTraversal

/-- The unresolved stopped K2 determination on the already constructed
standard Borel models. This is an internal conditional input, not a source theorem. -/
def RetStoppedTypeDeterminationStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ : ℝ, ∀ M : StoppedTypeModel κ θ,
    ∀ Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ Fc →
      ∀ᵐ ω ∂M.law, M.data.life ω ≤ (Fc ((M.data.word ω, 0), M.data.field ω)).2 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ M.data.life ω →
          M.data.trace ω t = decPath (Fc ((M.data.word ω, 0), M.data.field ω)) t

universe v
variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Pull a proved model determination back to its source type event. -/
theorem ae_codeMatch_of_stoppedModelTransfer_late [IsProbabilityMeasure P]
    {κ θ : ℝ} {F : Set Ω} {c : Ω → BoundaryWord}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (T : StoppedModelTransfer κ θ P F c Hc V γ) (hF : MeasurableSet F)
    (hMatch : RetStoppedTypeDeterminationStatement) (hκ : 0 < κ) (hκ4 : κ < 4)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have hm := hMatch κ hκ hκ4 θ T.model Fc hFc
  have hm' : ∀ᵐ ω ∂(P[|F]).map T.read,
      T.model.data.life ω ≤ (Fc ((T.model.data.word ω, 0), T.model.data.field ω)).2 ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T.model.data.life ω →
          T.model.data.trace ω t = decPath (Fc ((T.model.data.word ω, 0), T.model.data.field ω)) t :=
    (congrArg (fun μ : Measure T.model.space => ae μ) T.mapLaw).symm ▸ hm
  have hp := FCDet.ae_imp_of_ae_cond hF (ae_of_ae_map T.readMeas.aemeasurable hm')
  filter_upwards [hp, T.agrees] with ω hω he hωF
  obtain ⟨ec, eH, eV, eγ⟩ := he hωF
  obtain ⟨hV, hγ⟩ := hω hωF
  rw [ec, eH, eV] at hV hγ
  exact ⟨hV, fun t ht => (eγ t ht).symm.trans (hγ t ht)⟩

/-- Finitely many conditional models suffice. Null type events need no model. -/
theorem ae_codeMatch_of_finite_stoppedModels_late [IsProbabilityMeasure P]
    {κ θ : ℝ} {c : Ω → BoundaryWord} {Hc : Ω → DistOn upperHalfPlaneOpens}
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {F : Set Ω} {n : ℕ} {M : Fin n → Set Ω}
    (hM : ∀ i, MeasurableSet (M i))
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → ∃ i, ω ∈ M i)
    (hmodels : ∀ i, P (M i) ≠ 0 → Nonempty (StoppedModelTransfer κ θ P (M i) c Hc V γ))
    (hMatch : RetStoppedTypeDeterminationStatement) (hκ : 0 < κ) (hκ4 : κ < 4)
    {Fc : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞}
    (hFc : IsCanonicalFlowCode κ θ Fc) :
    ∀ᵐ ω ∂P, ω ∈ F → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
  have hi : ∀ i : Fin n, ∀ᵐ ω ∂P, ω ∈ M i → V ω ≤ (Fc ((c ω, 0), Hc ω)).2 ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω → γ ω t = decPath (Fc ((c ω, 0), Hc ω)) t := by
    intro i
    by_cases hz : P (M i) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω hω hωM
      exact (hω hωM).elim
    · obtain ⟨T⟩ := hmodels i hz
      exact ae_codeMatch_of_stoppedModelTransfer_late T (hM i) hMatch hκ hκ4 hFc
  filter_upwards [ae_all_iff.2 hi, hcover] with ω hω hc hωF
  obtain ⟨i, hi⟩ := hc hωF
  exact hω i hi

/-- The retained-model construction is supplied by Lemma 7.5. -/
theorem lemma76DetRStatement_of_modelMatch_late
    (hMatch : RetStoppedTypeDeterminationStatement) (h75 : Theorem15.Lemma75Statement.{v}) :
    Sec7.Lemma76DetRStatement.{v} := by
  have hmodels := Restart.RetFin.retStoppedModelsStatement_of_lemma75 h75
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω mΩ P _ h hh
    η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag Fc hFc u₀ hu₀ β hβ hmean hsort
  obtain ⟨n, M, hM, -, hcover, hmodel⟩ := hmodels κ hκ hκ4 b jumps hb
    x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hag u₀ hu₀ β hβ hmean hsort
  exact ae_codeMatch_of_finite_stoppedModels_late hM hcover hmodel hMatch hκ hκ4 hFc

end InteractingSLE.Wire
