import SupercriticalLQGUniqueness.B2.DG20Lim.LFPPSubseqCoupling
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import LQGMetric.Papers.DFGPS.T12P0

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalizedGFF_of_law_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (h' : Ω' → DistC) (hm : Measurable h')
    (hlaw : P'.map h' = P.map h) :
    IsNormalizedWholePlaneGFF h' P' :=
  SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_new_of_old
    (LQGMetric.DFGPS.T12.isNormalizedWPGFF_of_map_eq hm
      (SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalized_old_of_new hh)
      hlaw)

 


theorem exists_lfpp_joint_coord_skorokhod_gff
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω')
        (_ : StandardBorelSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P')
        (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
        (Ylim : Ω' → (CoordJ → ℝ) × RatCoords),
        (∀ n, Measurable (Y n)) ∧ Measurable Ylim ∧
        IsNormalizedWholePlaneGFF (fun ω => pairJInv ⊤ (Ylim ω).1) P' ∧
        (∀ n, P'.map (fun ω =>
          (pairJInv ⊤ (Y n ω).1,
            finiteMetricE (circleCoordsInv (Y n ω).2.1))) =
          P.map (fun ω => (h ω,
            rescaledLFPP ξ (m (ε (ψ n))) (X (ε (ψ n)) ω)))) ∧
        (∀ n ω, Continuous
          (finiteMetricE (circleCoordsInv (Y n ω).2.1))) ∧
        (∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) := by
  obtain ⟨ψ, hψ, Ω', mΩ', sbΩ', P', hP', Y, Ylim,
      hYm, hYlimm, hLaw, hCont, hConv, hMarg⟩ :=
    exists_lfpp_joint_coord_skorokhod P h hh X hX ξ m ε
  refine ⟨ψ, hψ, Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, ?_, hLaw, hCont, hConv⟩
  exact normalizedGFF_of_law_eq h hh _
    ((measurable_pairJInv ⊤).comp (measurable_fst.comp hYlimm)) hMarg

end SupercriticalLQGUniqueness.B2.DG20Lim
