import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteJointCoords
import LQGMetric.Field.StandardBorelRange

 


set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_circle_coord_symm_of_joint_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (Y : Ω' → (CoordJ → ℝ) × RatCoords) (hY : Measurable Y)
    (hLaw : P'.map Y = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)))
    (O Pcircle : RatCircle) :
    ∀ᵐ ω ∂P', (Y ω).2.1 (O, Pcircle) =
      (Y ω).2.1 (Pcircle, O) := by
  let E : Set ((CoordJ → ℝ) × RatCoords) :=
    {q | q.2.1 (O, Pcircle) = q.2.1 (Pcircle, O)}
  have hC (A B : RatCircle) : Measurable
      (fun q : (CoordJ → ℝ) × RatCoords => q.2.1 (A, B)) :=
    (measurable_pi_apply (A, B)).comp
      (measurable_fst.comp measurable_snd)
  have hE : MeasurableSet E := measurableSet_eq_fun (hC O Pcircle) (hC Pcircle O)
  let S : Ω → (CoordJ → ℝ) × RatCoords :=
    fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion D hD ω)
  have hSm : Measurable S :=
    ((measurable_pairJ ⊤).comp hh).prodMk
      (measurable_measurableRatCoordsVersion D hD)
  have hSource : ∀ᵐ ω ∂P, S ω ∈ E := by
    filter_upwards [ae_eq_measurableRatCoordsVersion D hD] with ω hω
    have hs : finiteCircleCoords (D ω) (O, Pcircle) =
        finiteCircleCoords (D ω) (Pcircle, O) := by
      simp only [finiteCircleCoords, LQGMetric.Blueprint.setDist]
      exact LQGMetric.MetricGeometry.setEDist_comm _ _
    simpa only [S, E, finiteRatCoords] using (hω ▸ hs)
  have hSourceMap : ∀ᵐ q ∂P.map S, q ∈ E :=
    (ae_map_iff hSm.aemeasurable hE).2 hSource
  exact (ae_map_iff hY.aemeasurable hE).1 (hLaw ▸ hSourceMap)

theorem ae_all_circle_coord_symm_of_joint_laws
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : ℕ → Ω → ContMetric)
    (hD : ∀ n, AEMeasurable (D n) P)
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (hY : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω))) :
    ∀ᵐ ω ∂P', ∀ n O Pcircle,
      (Y n ω).2.1 (O, Pcircle) = (Y n ω).2.1 (Pcircle, O) := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro O
  apply ae_all_iff.mpr
  intro Pcircle
  exact ae_circle_coord_symm_of_joint_law P P' h hh
    (D n) (hD n) (Y n) (hY n) (hLaw n) O Pcircle

end SupercriticalLQGUniqueness.B2.DG20Lim
