import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoupling

 





set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 


theorem exists_lifted_joint_skorokhod
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : Measurable h) (D : ℕ → Ω → LQGMetric.ContMetric)
    (hD : ∀ n, AEMeasurable (D n) P) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω')
        (_ : StandardBorelSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P')
        (Y : ℕ → Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords)
        (Ylim : Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords),
        (∀ n, Measurable (Y n)) ∧ Measurable Ylim ∧
        (∀ n, P'.map (fun ω => decodeFinitePair (Y n ω)) =
          P.map (fun ω => (h ω, D (ψ n) ω))) ∧
        (∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) ∧
        P'.map (fun ω => LQGMetric.pairJInv ⊤ (Ylim ω).1) = P.map h := by
  let C (n : ℕ) := measurableRatCoordsVersion (D n) (hD n)
  have hC : ∀ n, Measurable (C n) := fun n =>
    measurable_measurableRatCoordsVersion (D n) (hD n)
  obtain ⟨ψ, hψ, Ω', mΩ', sbΩ', P', hP', Y, Ylim, hY, hYlim,
      hYlaw, hYconv, hYlimLaw⟩ := exists_joint_coord_skorokhod P h hh C hC
  refine ⟨ψ, hψ, Ω', mΩ', sbΩ', P', hP', Y, Ylim,
    hY, hYlim, ?_, hYconv, hYlimLaw⟩
  intro n
  exact joint_finite_pair_law_of_coord_law h hh (D (ψ n)) (hD (ψ n))
    (Y n) (hY n) (hYlaw n)

end SupercriticalLQGUniqueness.B2.DG20Lim
