import SupercriticalLQGUniqueness.B2.Final.OpenInputs3
import SupercriticalLQGUniqueness.B2.Final.DG20CoupledCoords

 






















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric (DistC normGFFLaw heatMollify)
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

 
theorem CoupledRatCoords.comp {ξ : Set.Ioi (0 : ℝ)} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
    {e : ℕ → Set.Ioi (0 : ℝ)} {V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)}
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {hN : ℕ → Ω' → DistC}
    {L : Ω' → LSCMetric} (h : CoupledRatCoords ξ m e V P' hN L) {ψ : ℕ → ℕ}
    (hψ : StrictMono ψ) :
    CoupledRatCoords ξ m (fun n => e (ψ n)) V P' (fun n => hN (ψ n)) L := by
  obtain ⟨Z, Zlim, hZm, hZlm, hZid, hZconv, hL⟩ := h
  exact ⟨fun n => Z (ψ n), Zlim, fun n => hZm (ψ n), hZlm,
    hZid.mono fun _ hω n => hω (ψ n), fun ω => (hZconv ω).comp hψ.tendsto_atTop, hL⟩

 




def DG20CouplingSmallAnnuliCoords : Prop :=
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
      CoupledRatCoords ξ m (fun n => ε (φ₁ n)) V P' hN L

 



def PfeS1SmallAnnuliCoords : Prop :=
  DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
    DG20CouplingData ξ Q m e c V P' h' hN L →
    CoupledSmallAnnuli ξ m e V P' hN L → CoupledAcrossTails P' L →
    CoupledRatCoords ξ m e V P' hN L →
    ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ PfeWeyl.NormalizedSmallAnnuli ξ m (fun n => e (ψ n)) Φ

 




def PfePointCirclesCoords : Prop :=
  DG20Interfaces →
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ))
    {Ω' : Type} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (h' : Ω' → DistC) (hN : ℕ → Ω' → DistC) (L : Ω' → LSCMetric),
    DG20CouplingData ξ Q m e c V P' h' hN L →
    CoupledSmallAnnuli ξ m e V P' hN L → CoupledAcrossTails P' L →
    CoupledRatCoords ξ m e V P' hN L →
    ∀ Φ : DistC → LSCMetric, Measurable Φ → (∀ᵐ ω ∂P', L ω = Φ (h' ω)) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ PfeWeyl.NormalizedPointCircles ξ m (fun n => e (ψ n)) Φ

 
theorem pfeS1SmallAnnuliCoords_of_old (h : PfeS1SmallAnnuli) : PfeS1SmallAnnuliCoords :=
  fun hI ξ Q m e c V _ _ _ P' _ h' hN L hB hsa hat _ => h hI ξ Q m e c V P' h' hN L hB hsa hat

 
theorem pfePointCirclesCoords_of_old (h : PfePointCircles) : PfePointCirclesCoords :=
  fun hI ξ Q m e c V _ _ _ P' _ h' hN L hB hsa hat _ => h hI ξ Q m e c V P' h' hN L hB hsa hat

 

def RemainingInputs4 : Prop :=
  DG20CouplingSmallAnnuliCoords ∧ PfeS1SmallAnnuliCoords ∧ PfePointCirclesCoords

end SupercriticalLQGUniqueness.B2.Final
