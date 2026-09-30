import QuantumZipper.Proofs.Thm18.G1CoreFixed

/-!
# G1-CORE, part 4: the product form for the explicit wedge representative

`G1RegFixedStmt` (G1CoreFixed.lean) only involves the law `fieldLawFull H Y P` of the wedge
data. By the definition of `IsQuantumWedge` that law is the one of the explicit representative
`canonical γ (wedgeField (lateralPart X) A Q)` (`X` a free-boundary GFF modulo constants, `A` an
independent wedge process with `α = γ - 2/γ`, `Q = Qc γ`). This file reduces `G1RegFixedStmt`
to `G1RegRepStmt`, the same product statement for that representative on its own probability
space, with the path and the field on *separate* probability spaces (no coupling left):

`g1RegFixedStmt_of_rep : G1RegRepStmt → G1RegFixedStmt`, and the chain
`g1Stmt_of_zoom_regRep : G1ZoomPartStmt → G1RegRepStmt → G1Stmt`.

Own argument (law transfer, `ae_map_iff` with the a.e.-measurability of the wedge data,
`WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The explicit representative of the `γ`-wedge with `α = γ - 2/γ` used in `IsQuantumWedge`. -/
def wedgeRep (γ : ℝ) {Ω' : Type} (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (ω' : Ω') :
    FieldSample :=
  canonical γ (wedgeField (lateralPart (X ω')) (fun t => A t ω') (Qc γ))

/-- **G1 regularity half for the explicit representative** (product form, separate spaces). -/
def G1RegRepStmt : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' → IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      ∃ E : Set G1PathData, MeasurableSet E ∧ (∀ p ∈ E, G1RegGood γ p) ∧
        ∀ᵐ a ∂(P.map (pathOf B)), ∀ᵐ ω' ∂P',
          (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∈ E

/-- **Law transfer**: the representative statement gives the product form. -/
theorem g1RegFixedStmt_of_rep (h : G1RegRepStmt) : G1RegFixedStmt := by
  intro γ Ω _ P _ B Y hS _
  obtain ⟨hγ, hγ2, hB, hY, -⟩ := hS
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hXA, hlaw⟩ := hY
  obtain ⟨E, hE, hg, hae⟩ := h γ hγ hγ2 P B hB P' X A hX hA hXA
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hα, Ω', inferInstance, P', X, A, hP', hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  refine ⟨E, hE, hg, ?_⟩
  rw [hlaw]
  filter_upwards [hae] with a ha
  exact (ae_map_iff hm (measurable_prodMk_left hE)).2 ha

/-- **G1 from the zoom half and the representative regularity half.** -/
theorem g1Stmt_of_zoom_regRep (hZ : G1ZoomPartStmt) (hR : G1RegRepStmt) : G1Stmt :=
  g1Stmt_of_zoom_regFixed hZ (g1RegFixedStmt_of_rep hR)

end Thm18Asm
end QuantumZipper
