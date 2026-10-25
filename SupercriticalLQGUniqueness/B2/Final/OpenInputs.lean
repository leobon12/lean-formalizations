import SupercriticalLQGUniqueness.B2.Final.CouplingData
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RInputs
import SupercriticalLQGUniqueness.B2.PfeLocal.InputsL5
import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsGeometry0

 




























set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

 

 



def DG20LaneC2Star : Prop :=
  DG20Conc.LaneC2StarAt.{0}

 



def DG20LaneFineStarIndep : Prop :=
  DG20Conc.LaneFineStarIndepCoarse.{0}

 

 














def DG20SmallAnnuliCoupling : Prop :=
  DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), IsLFPPExponent ξ Q →
  ∀ (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)), (∀ δ, IsLFPPNormalizer ξ δ (m δ)) →
  ∀ (ε : ℕ → Set.Ioi (0 : ℝ)), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
    ∃ φ₁ : ℕ → ℕ, StrictMono φ₁ ∧ ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
    ∃ V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ),
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω') (P' : Measure Ω')
      (_ : IsProbabilityMeasure P') (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC)
      (L : Ω' → LSCMetric),
      DG20CouplingData ξ Q m (fun n => ε (φ₁ n)) c V P' h' hN L ∧
      CoupledSmallAnnuli ξ m (fun n => ε (φ₁ n)) V P' hN L ∧
      ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          PfeWeyl.NormalizedSmallAnnuli ξ m (fun n => ε (φ₁ (ψ n))) Φ ∧
          PfeWeyl.NormalizedPointCircles ξ m (fun n => ε (φ₁ (ψ n))) Φ

 






def DG20CoupledAcrossTailsInput : Prop :=
  DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
    DG20CouplingData ξ Q m e c V P' h' hN L → CoupledAcrossTails P' L

 

 






def PfeL5ObsLocality : Prop :=
  DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
    DG20CouplingData ξ Q m e c V P' h' hN L →
    CoupledSmallAnnuli ξ m e V P' hN L → CoupledAcrossTails P' L →
    PfeLocal.Inputs.L5ObsLocality P' h' L

 

 




def MedianPassageOfGeometry : Prop :=
  DG20Interfaces → PfeAxioms.Inputs.LimitLengthSpace0 →
    PfeAxioms.Inputs.LimitEuclideanControl0 → MedianPassage

 
def AllOpenInputs : Prop :=
  DG20LaneC2Star ∧ DG20LaneFineStarIndep ∧ DG20SmallAnnuliCoupling ∧
    DG20CoupledAcrossTailsInput ∧ PfeL5ObsLocality ∧ MedianPassageOfGeometry

end SupercriticalLQGUniqueness.B2.Final
