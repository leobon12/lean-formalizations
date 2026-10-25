import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableNormalizedContinuous
import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableFiniteMeasurable
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.ClosedEventToolkit

 

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem measurable_normalizedLFPP_neighborhood
    {Ω : Type} [MeasurableSpace Ω]
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    {X : Ω → C(ℂ, ℝ)} (hX : ∀ z, Measurable fun ω => X ω z)
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (x y : V) (ρ : ℝ) :
    Measurable fun ω => neighborhoodInternal
      (PfeWeyl.normalizedLFPPMetric ξ a (X ω)) V x y ρ := by
  let E : Ω → LSCMetric := fun ω => PfeWeyl.normalizedLFPPMetric ξ a (X ω)
  have hE : Measurable E := measurable_normalizedLFPPMetric_comp ξ a hX
  let S : Set (V × V) :=
    {p | dist (p.1 : ℂ) x < ρ ∧ dist (p.2 : ℂ) y < ρ}
  have heq : ∀ ω, neighborhoodInternal (E ω) V x y ρ =
      ⨅ p : S, (E ω).internal V (p.1.1, p.1.2) := by
    intro ω
    unfold neighborhoodInternal
    apply le_antisymm
    · refine le_iInf fun p => ?_
      exact iInf_le_of_le p.1.1 <| iInf_le_of_le p.2.1 <|
        iInf_le_of_le p.1.2 <| iInf_le_of_le p.2.2 le_rfl
    · refine le_iInf fun u => le_iInf fun hu =>
        le_iInf fun v => le_iInf fun hv => ?_
      exact iInf_le_of_le (⟨(u, v), hu, hv⟩ : S) le_rfl
  change Measurable (fun ω => neighborhoodInternal (E ω) V x y ρ)
  simp_rw [heq]
  have hfun : (fun ω : Ω => ⨅ p : S, (E ω).internal V (p.1.1, p.1.2)) =
      (⨅ p : S, fun ω : Ω => (E ω).internal V (p.1.1, p.1.2)) := by
    funext ω
    simp only [iInf_apply]
  rw [hfun]
  apply measurable_iInf_of_upperSemicontinuous
  · intro p
    let O : TopologicalSpace.Opens ℂ := ⟨V, hV⟩
    have hm := (Uniqueness.Toolkit.CountableBase.internalBoundedOpen_borel
      hV hVb (p.1.1 : O) (p.1.2 : O)).comp hE
    exact hm
  · intro ω
    exact (continuous_normalizedLFPPMetric_internal ξ a (X ω) hV).comp
      continuous_subtype_val |>.upperSemicontinuous

end SupercriticalLQGUniqueness.B2.PfeAxioms
