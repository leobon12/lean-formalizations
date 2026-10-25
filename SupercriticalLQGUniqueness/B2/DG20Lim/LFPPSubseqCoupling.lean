import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPPCoupling

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_lfpp_joint_coord_skorokhod
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
        (∀ n, P'.map (fun ω =>
          (pairJInv ⊤ (Y n ω).1,
            finiteMetricE (circleCoordsInv (Y n ω).2.1))) =
          P.map (fun ω => (h ω,
            rescaledLFPP ξ (m (ε (ψ n))) (X (ε (ψ n)) ω)))) ∧
        (∀ n ω, Continuous
          (finiteMetricE (circleCoordsInv (Y n ω).2.1))) ∧
        (∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) ∧
        P'.map (fun ω => pairJInv ⊤ (Ylim ω).1) = P.map h := by
  let D : ℕ → Ω → ContMetric := fun n ω =>
    normalizedContLFPP ξ (m (ε n)) (X (ε n) ω)
  have hD : ∀ n, AEMeasurable (D n) P := by
    intro n
    exact aemeasurable_normalizedContLFPP_heat_version P h hh
      (ε n) (m (ε n)) ξ (X (ε n)) (hX (ε n))
  obtain ⟨ψ, hψ, Ω', mΩ', sbΩ', P', hP', Y, Ylim,
      hYm, hYlimm, hLaw, hConv, hMarg⟩ :=
    exists_lifted_joint_skorokhod P h hh.1.measurable D hD
  refine ⟨ψ, hψ, Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hYm, hYlimm, ?_, ?_, hConv, hMarg⟩
  · intro n
    exact joint_law_rescaledLFPP_of_finite_law h hh.1.measurable
      (D (ψ n)) (hD (ψ n)) (Y n) (hYm n) (hLaw n)
      ξ (m (ε (ψ n))) (X (ε (ψ n))) (fun _ => rfl)
  · intro n ω
    exact continuous_finiteMetricE _

end SupercriticalLQGUniqueness.B2.DG20Lim
