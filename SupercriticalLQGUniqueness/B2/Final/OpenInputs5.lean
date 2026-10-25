import SupercriticalLQGUniqueness.B2.Final.OpenInputs4
import SupercriticalLQGUniqueness.B2.Final.S2IntIdentity

 


























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

 




def S2IdentificationSite : Prop :=
  DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
    DG20CouplingData ξ Q m e c V P' h' hN L → CoupledSmallAnnuli ξ m e V P' hN L →
    CoupledAcrossTails P' L → CoupledRatCoords ξ m e V P' hN L →
    ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
    PfeWeyl.NormalizedLscLimit ξ m e Φ → FixedFieldWeylAllBounded ξ m e Φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ FixedFieldPatchIdentification ξ m (fun n => e (ψ n)) Φ

 



def S2LocalitySite : Prop :=
  DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
    DG20CouplingData ξ Q m e c V P' h' hN L → CoupledSmallAnnuli ξ m e V P' hN L →
    CoupledAcrossTails P' L → CoupledRatCoords ξ m e V P' hN L →
    ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
    PfeWeyl.NormalizedLscLimit ξ m e Φ → FixedFieldWeylAllBounded ξ m e Φ →
    FixedFieldPatchIdentification ξ m e Φ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
          ∃ F : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞), Measurable F ∧
            ∀ᵐ ω ∂P, (PfeAxioms.patchWitness ξ m e (h ω)).internal (U : Set ℂ) =
              F (restrictTo U (h ω))

 
def ThreeBNew : Prop :=
  S2IdentificationSite ∧ S2LocalitySite

end SupercriticalLQGUniqueness.B2.Final
