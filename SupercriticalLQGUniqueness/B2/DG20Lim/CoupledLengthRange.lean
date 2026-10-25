import SupercriticalLQGUniqueness.B2.DG20Lim.LSCFromJointLaw

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_finite_length_and_range_of_joint_coord_laws
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : ℕ → Ω → ContMetric)
    (hD : ∀ n, AEMeasurable (D n) P)
    (hLen : ∀ n, ∀ᵐ ω ∂P, (D n ω).IsLength)
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (hYm : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω))) :
    ∀ᵐ ω ∂P', ∀ n,
      finiteCircleCoords (circleCoordsInv (Y n ω).2.1) = (Y n ω).2.1 ∧
      (circleCoordsInv (Y n ω).2.1).IsLength := by
  apply ae_all_iff.mpr
  intro n
  let π : (CoordJ → ℝ) × RatCoords →
      (RatCircle × RatCircle → ℝ≥0∞) := fun q => q.2.1
  have hπ : Measurable π := measurable_fst.comp measurable_snd
  have hSource : Measurable (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)) :=
    ((measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion (D n) (hD n))
  have hCircleLaw : P'.map (fun ω => (Y n ω).2.1) =
      P.map (fun ω => (measurableRatCoordsVersion (D n) (hD n) ω).1) := by
    calc
      P'.map (fun ω => (Y n ω).2.1) = (P'.map (Y n)).map π :=
        (Measure.map_map hπ (hYm n)).symm
      _ = (P.map (fun ω =>
          (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω))).map π :=
        by rw [hLaw n]
      _ = P.map (fun ω =>
          (measurableRatCoordsVersion (D n) (hD n) ω).1) :=
        Measure.map_map hπ hSource
  have hRange := ae_circleCoords_range_of_coord_law (D n) (hD n)
    (fun ω => (Y n ω).2.1) (hπ.comp (hYm n)) hCircleLaw
  have hLength := ae_isLength_of_finite_pair_law P P' h hh (D n) (hD n)
    (hLen n) (Y n) (hYm n)
    (joint_finite_pair_law_of_coord_law h hh (D n) (hD n)
      (Y n) (hYm n) (hLaw n))
  filter_upwards [hRange, hLength] with ω hr hl
  exact ⟨hr, hl⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
