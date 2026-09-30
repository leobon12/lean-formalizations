import QuantumZipper.Proofs.Thm18.G3ZqL19GdQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (20): the G3 path limit from AREA-ONLY pulled-back goodness at typical points

As G3ZqL18Path, with the pulled-back goodness `g3zMapGd` (contains `IsLQGGood`, D89) replaced by
the area-only rational local condition `g3zMapGdQ` (G3ZqL19GdQ). Node `G3ZqLMapTypQStmt` (implied
by `G3ZqLMapTypStmt`, hence by `G3Zq.G3ZqMapGdStmt`); headline `theorem1_8PaperMO_of_typQ`.
Own bookkeeping (Sheffield, arXiv:1012.4797, pp. 65–66, 70–72).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open G3Z2b2 G1Zm G3Zq R18.G3ZqL R18

/-- Typical-point area-only goodness of a field for the two map zooms. -/
def G3ZqLTypQ (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (a : ℝ≥0 → ℝ) (y : FieldSample) : Prop :=
  ∀ᵐ x ∂(qBoundaryMeasure γ y), g3zMapGdQ γ Ψ true a y x ∧
    g3zMapGdQ γ Ψ false a y (g3zPartner γ y x)

/-- Palm-typical area-only goodness of the scheme `B` and `C` fields. -/
def G3ZqLSchemeTypQ (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (a : ℝ≥0 → ℝ) : Prop :=
  (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wCut γ i.η) i),
      g3zMapGdQ γ Ψ true a (g3pField γ (g3wCut γ i.η) p.1) (g3pX γ (g3wCut γ i.η) i p)) ∧
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wProf γ) i),
      g3zMapGdQ γ Ψ true a (g3pField γ (g3wProf γ) p.1) (g3pX γ (g3wProf γ) i p)) ∧
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wCut γ i.η) i),
      g3zMapGdQ γ Ψ false a (g3pField γ (g3wCut γ i.η) p.1) (g3pR γ (g3wCut γ i.η) i p)) ∧
    (∀ i : G3Idx, ∀ᵐ p ∂(g3pPalmLaw γ (g3wProf γ) i),
      g3zMapGdQ γ Ψ false a (g3pField γ (g3wProf γ) p.1) (g3pR γ (g3wProf γ) i p))

end G3ZqL
end Thm18Asm
end QuantumZipper
