import QuantumZipper.Proofs.Thm18.G1Z3Fixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B (Z2a): law transfer to `wedgeRep` and Fubini over the independent path

In the Theorem 1.8 setting the driving path `B` is independent of the wedge field `Y`, and the law
of the wedge data `fieldLawFull H Y P` is that of the explicit representative
`wedgeRep γ X A = canonical γ (wedgeField (lateralPart X) A Q)` of `IsQuantumWedge` on its own
probability space `(Ω', P')`. Hence every functional of the pair (path, wedge data) which is read
off a measurable `G` on `G1PathData` has expectation

  `E_P[F] = ∫ (∫ G(a, data(wedgeRep ω')) dP'(ω')) d(law of the path)(a)`:

first the law transfer to the representative, then Fubini over the independent path.

This is the independence argument of Sheffield, arXiv:1012.4797, §1.6/§5 (the SLE is sampled
independently of the wedge, so one may fix the curve and average over the field), in the form of
Duplantier–Sheffield, *LQG and KPZ*, Invent. Math. 185 (2011), Prop. 2.1 (conformal maps chosen
independently of the field). Own bookkeeping (the pattern of `G1Z3Fixed.lean`,
`G1CoreRep.g1RegFixedStmt_of_rep`; AGENT_GUIDE cost rule).

The representative comes with the free field `X` and the independent wedge process `A`, so
`g3WedgePalmIdStmt_holds` (G3Z2bPalm.lean) applies to the inner integral on the same space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Z2a (law transfer and Fubini over the path).** -/
def G3PathFubiniStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ),
      IsFreeGFFModConstH X P' ∧ IsWedgeProcess (γ - 2 / γ) (Qc γ) A P' ∧
      IndepFun X (fun ω t => A t ω) P' ∧
      ∀ (F : Ω → ℝ≥0∞) (G : G1PathData → ℝ≥0∞), Measurable G →
        (∀ᵐ ω ∂P, F ω = G (pathOf B ω, WedgeMeas.dataFull H (Y ω))) →
        ∫⁻ ω, F ω ∂P =
          ∫⁻ a, ∫⁻ ω', G (a, WedgeMeas.dataFull H (wedgeRep γ X A ω')) ∂P' ∂(P.map (pathOf B))

/-- **Z2a proved.** -/
theorem g3PathFubiniStmt_holds : G3PathFubiniStmt := by
  intro γ Ω _ P _ B Y hS hIn
  obtain ⟨hγ, hγ2, hB, hY, hind⟩ := hS
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hXA, hlaw⟩ := hY
  refine ⟨Ω', inferInstance, P', hP', X, A, hX, hA, hXA, ?_⟩
  intro F G hG hF
  have hgm : AEMeasurable (pathOf B) P := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
  have hdm : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P := hIn.2.1
  have hind' : IndepFun (pathOf B) (fun ω => WedgeMeas.dataFull H (Y ω)) P :=
    hind.comp measurable_id measurable_dataFull_H
  have hαQ : γ - 2 / γ < Qc γ := alpha_lt_Qc hγ hγ2
  have hrep : IsQuantumWedge γ (γ - 2 / γ) (wedgeRep γ X A) P' :=
    ⟨hα, Ω', inferInstance, P', X, A, hP', hX, hA, hXA, rfl⟩
  have hm := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hαQ) (WedgeInf.wedgeInfiniteTotal hγ hγ2 hαQ)
    hγ hγ2 hrep
  rw [lintegral_congr_ae hF,
    ← lintegral_map' hG.aemeasurable (hgm.prodMk hdm),
    (indepFun_iff_map_prod_eq_prod_map_map hgm hdm).1 hind',
    lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun a => ?_
  have e : (P.map fun ω => WedgeMeas.dataFull H (Y ω)) =
      P'.map fun ω' => WedgeMeas.dataFull H (wedgeRep γ X A ω') := hlaw
  rw [e]
  exact lintegral_map' (f := fun y => G (a, y)) (hG.comp measurable_prodMk_left).aemeasurable hm

end Thm18Asm
end QuantumZipper
