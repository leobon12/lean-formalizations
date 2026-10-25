import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoordRange
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLengthTransfer
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoupling

 


set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_finiteCircle_chain_of_joint_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (Y : Ω' → (CoordJ → ℝ) × RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω))) :
    ∀ᵐ ω ∂P', ∀ (k : ℕ) (O : Fin (k + 1) → RatCircle),
      (∀ i j : Fin (k + 1), i ≠ j →
        Disjoint (O i).toSet (O j).toSet) →
      (∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
        Disconnects (O ⟨j, by omega⟩).toSet
          (O ⟨j - 1, by omega⟩).toSet
          (O ⟨j + 1, by omega⟩).toSet) →
      (∑ j : Fin k,
        (Y ω).2.1 (O ⟨j.val, by omega⟩, O ⟨j.val + 1, by omega⟩)) ≤
        (Y ω).2.1 (O ⟨0, by omega⟩, O ⟨k, by omega⟩) := by
  let π : (CoordJ → ℝ) × RatCoords →
      (RatCircle × RatCircle → ℝ≥0∞) := fun q => q.2.1
  have hπ : Measurable π := measurable_fst.comp measurable_snd
  have hSource : Measurable (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)) :=
    ((measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion D hD)
  have hCircleLaw : P'.map (fun ω => (Y ω).2.1) =
      P.map (fun ω => (measurableRatCoordsVersion D hD ω).1) := by
    calc
      P'.map (fun ω => (Y ω).2.1) = (P'.map Y).map π :=
        (Measure.map_map hπ hY).symm
      _ = (P.map (fun ω =>
          (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω))).map π :=
        by rw [hLaw]
      _ = P.map (fun ω => (measurableRatCoordsVersion D hD ω).1) :=
        Measure.map_map hπ hSource
  have hRange := ae_circleCoords_range_of_coord_law D hD
    (fun ω => (Y ω).2.1) (hπ.comp hY) hCircleLaw
  have hPair := joint_finite_pair_law_of_coord_law h hh D hD Y hY hLaw
  have hLen' := ae_isLength_of_finite_pair_law P P' h hh D hD hLen Y hY hPair
  exact ae_finiteCircleCoords_chain P' (fun ω => (Y ω).2.1) hRange hLen'

 

theorem ae_all_finiteCircle_chain_of_joint_coord_laws
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : ℕ → Ω → ContMetric)
    (hD : ∀ n, AEMeasurable (D n) P)
    (hLen : ∀ n, ∀ᵐ ω ∂P, (D n ω).IsLength)
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (hY : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω))) :
    ∀ᵐ ω ∂P', ∀ n (k : ℕ) (O : Fin (k + 1) → RatCircle),
      (∀ i j : Fin (k + 1), i ≠ j →
        Disjoint (O i).toSet (O j).toSet) →
      (∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
        Disconnects (O ⟨j, by omega⟩).toSet
          (O ⟨j - 1, by omega⟩).toSet
          (O ⟨j + 1, by omega⟩).toSet) →
      (∑ j : Fin k,
        (Y n ω).2.1 (O ⟨j.val, by omega⟩, O ⟨j.val + 1, by omega⟩)) ≤
        (Y n ω).2.1 (O ⟨0, by omega⟩, O ⟨k, by omega⟩) := by
  exact ae_all_iff.mpr (fun n =>
    ae_finiteCircle_chain_of_joint_coord_law P P' h hh (D n) (hD n)
      (hLen n) (Y n) (hY n) (hLaw n))

end SupercriticalLQGUniqueness.B2.DG20Lim
