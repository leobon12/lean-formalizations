import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAroundSource
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteJointCoords
import SupercriticalLQGUniqueness.B2.DG20Lim.CoordSpace

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_finiteAround_bound_of_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsFiniteMeasure P] {P' : Measure Ω'}
    (D : Ω → LQGMetric.ContMetric) (hD : AEMeasurable D P)
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (Y : Ω' → RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (measurableRatCoordsVersion D hD))
    (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle)
    (h₁ : A.OppositeSides O₁ O₁')
    (h₂ : A.OppositeSides O₂ O₂') :
    ∀ᵐ ω ∂P', (Y ω).1 (O₁, O₂) ≤
      (Y ω).1 (O₁, O₁') + (Y ω).1 (O₂, O₂') + (Y ω).2 A := by
  let E : Set RatCoords := {q | q.1 (O₁, O₂) ≤
    q.1 (O₁, O₁') + q.1 (O₂, O₂') + q.2 A}
  have hC (O P : RatCircle) : Measurable (fun q : RatCoords => q.1 (O, P)) :=
    (measurable_pi_apply (O, P)).comp measurable_fst
  have hB : Measurable (fun q : RatCoords => q.2 A) :=
    (measurable_pi_apply A).comp measurable_snd
  have hE : MeasurableSet E :=
    measurableSet_le (hC O₁ O₂) (((hC O₁ O₁').add (hC O₂ O₂')).add hB)
  have hSm : Measurable (measurableRatCoordsVersion D hD) :=
    measurable_measurableRatCoordsVersion D hD
  have hSource : ∀ᵐ ω ∂P, measurableRatCoordsVersion D hD ω ∈ E := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD, hLen] with ω hEq hωLen
    change (measurableRatCoordsVersion D hD ω).1 (O₁, O₂) ≤ _
    rw [← hEq]
    exact finiteCircleDist_le_across_across_around (D ω) hωLen A
      O₁ O₁' O₂ O₂' h₁ h₂
  have hSourceMap : ∀ᵐ q ∂P.map (measurableRatCoordsVersion D hD), q ∈ E :=
    (ae_map_iff hSm.aemeasurable hE).2 hSource
  exact (ae_map_iff hY.aemeasurable hE).1 (hLaw ▸ hSourceMap)

 

theorem ae_all_finiteAround_bounds_of_coord_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsFiniteMeasure P] {P' : Measure Ω'}
    (D : Ω → LQGMetric.ContMetric) (hD : AEMeasurable D P)
    (hLen : ∀ᵐ ω ∂P, (D ω).IsLength)
    (Y : Ω' → RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (measurableRatCoordsVersion D hD)) :
    ∀ᵐ ω ∂P', ∀ (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle),
      A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
      (Y ω).1 (O₁, O₂) ≤
        (Y ω).1 (O₁, O₁') + (Y ω).1 (O₂, O₂') + (Y ω).2 A := by
  apply ae_all_iff.mpr
  intro A
  apply ae_all_iff.mpr
  intro O₁
  apply ae_all_iff.mpr
  intro O₁'
  apply ae_all_iff.mpr
  intro O₂
  apply ae_all_iff.mpr
  intro O₂'
  by_cases h₁ : A.OppositeSides O₁ O₁'
  · by_cases h₂ : A.OppositeSides O₂ O₂'
    · filter_upwards [ae_finiteAround_bound_of_coord_law D hD hLen
        Y hY hLaw A O₁ O₁' O₂ O₂' h₁ h₂] with ω hω
      exact fun _ _ => hω
    · exact Filter.Eventually.of_forall fun _ _ h => False.elim (h₂ h)
  · exact Filter.Eventually.of_forall fun _ h _ => False.elim (h₁ h)

 

theorem ae_all_finiteAround_bounds_of_joint_coord_laws
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → LQGMetric.DistC) (hh : Measurable h)
    (D : ℕ → Ω → LQGMetric.ContMetric)
    (hD : ∀ n, AEMeasurable (D n) P)
    (hLen : ∀ n, ∀ᵐ ω ∂P, (D n ω).IsLength)
    (Y : ℕ → Ω' → (LQGMetric.CoordJ → ℝ) × RatCoords)
    (hY : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (LQGMetric.pairJ ⊤ (h ω),
        measurableRatCoordsVersion (D n) (hD n) ω))) :
    ∀ᵐ ω ∂P', ∀ n (A : RatAnnulus) (O₁ O₁' O₂ O₂' : RatCircle),
      A.OppositeSides O₁ O₁' → A.OppositeSides O₂ O₂' →
      (Y n ω).2.1 (O₁, O₂) ≤
        (Y n ω).2.1 (O₁, O₁') +
          (Y n ω).2.1 (O₂, O₂') + (Y n ω).2.2 A := by
  apply ae_all_iff.mpr
  intro n
  have hSource : Measurable (fun ω =>
      (LQGMetric.pairJ ⊤ (h ω),
        measurableRatCoordsVersion (D n) (hD n) ω)) :=
    ((LQGMetric.measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion (D n) (hD n))
  have hRatLaw : P'.map (fun ω => (Y n ω).2) =
      P.map (measurableRatCoordsVersion (D n) (hD n)) := by
    calc
      P'.map (fun ω => (Y n ω).2) = (P'.map (Y n)).map Prod.snd :=
        (Measure.map_map measurable_snd (hY n)).symm
      _ = (P.map (fun ω =>
          (LQGMetric.pairJ ⊤ (h ω),
            measurableRatCoordsVersion (D n) (hD n) ω))).map Prod.snd := by
        rw [hLaw n]
      _ = P.map (measurableRatCoordsVersion (D n) (hD n)) :=
        Measure.map_map measurable_snd hSource
  exact ae_all_finiteAround_bounds_of_coord_law (D n) (hD n)
    (hLen n) (fun ω => (Y n ω).2) (measurable_snd.comp (hY n)) hRatLaw

end SupercriticalLQGUniqueness.B2.DG20Lim
