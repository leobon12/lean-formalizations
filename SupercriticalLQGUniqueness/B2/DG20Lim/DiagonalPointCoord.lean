import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteZeroCirclePoint
import SupercriticalLQGUniqueness.B2.DG20Lim.CircleSymmetryCoupling

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_diagonal_point_coord_zero_of_joint_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) [IsProbabilityMeasure P]
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (h : Ω → DistC) (hh : Measurable h)
    (D : ℕ → Ω → ContMetric)
    (hD : ∀ n, AEMeasurable (D n) P)
    (Y : ℕ → Ω' → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω' → (CoordJ → ℝ) × RatCoords)
    (hY : ∀ n, Measurable (Y n))
    (hLaw : ∀ n, P'.map (Y n) = P.map (fun ω =>
      (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)))
    (hConv : ∀ᵐ ω ∂P', Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω))) :
    ∀ᵐ ω ∂P', ∀ Z : RatCircle, Z.radius = 0 →
      (Ylim ω).2.1 (Z, Z) = 0 := by
  have hfinite (n : ℕ) (Z : RatCircle) (hZ : Z.radius = 0) :
      ∀ᵐ ω ∂P', (Y n ω).2.1 (Z, Z) = 0 := by
    let E : Set ((CoordJ → ℝ) × RatCoords) :=
      {q | q.2.1 (Z, Z) = 0}
    have hE : MeasurableSet E := by
      apply measurableSet_eq_fun
      · exact (measurable_pi_apply (Z, Z)).comp
          (measurable_fst.comp measurable_snd)
      · exact measurable_const
    let S : Ω → (CoordJ → ℝ) × RatCoords :=
      fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)
    have hSm : Measurable S :=
      ((measurable_pairJ ⊤).comp hh).prodMk
        (measurable_measurableRatCoordsVersion (D n) (hD n))
    have hSource : ∀ᵐ ω ∂P, S ω ∈ E := by
      filter_upwards [ae_eq_measurableRatCoordsVersion (D n) (hD n)] with ω hω
      have hc := congrArg (fun q : RatCoords => q.1 (Z, Z)) hω
      have hz : finiteCircleCoords (D n ω) (Z, Z) = 0 := by
        rw [finiteCircleCoords_zero_zero (D n ω) Z Z hZ hZ, edist_self]
      change (measurableRatCoordsVersion (D n) (hD n) ω).1 (Z, Z) = 0
      exact hc.symm.trans hz
    have hSourceMap : ∀ᵐ q ∂P.map S, q ∈ E :=
      (ae_map_iff hSm.aemeasurable hE).2 hSource
    exact (ae_map_iff (hY n).aemeasurable hE).1 (hLaw n ▸ hSourceMap)
  filter_upwards [hConv, ae_all_iff.mpr (fun n =>
    ae_all_iff.mpr (fun Z => ae_all_iff.mpr (fun hZ => hfinite n Z hZ)))] with
      ω hω hzero Z hZ
  have hcoord := circle_coord_tendsto hω Z Z
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_nhds_unique hcoord
    (hconst.congr' (Eventually.of_forall fun n => (hzero n Z hZ).symm))

end SupercriticalLQGUniqueness.B2.DG20Lim
