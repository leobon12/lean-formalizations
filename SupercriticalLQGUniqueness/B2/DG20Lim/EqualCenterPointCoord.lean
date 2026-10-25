import SupercriticalLQGUniqueness.B2.DG20Lim.DiagonalPointCoord

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_equal_center_point_coord_zero_of_joint_law
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
    ∀ᵐ ω ∂P', ∀ Z W : RatCircle, Z.radius = 0 → W.radius = 0 →
      Z.center = W.center → (Ylim ω).2.1 (Z, W) = 0 := by
  have hfinite (n : ℕ) (Z W : RatCircle)
      (hZ : Z.radius = 0) (hW : W.radius = 0)
      (hZW : Z.center = W.center) :
      ∀ᵐ ω ∂P', (Y n ω).2.1 (Z, W) = 0 := by
    let E : Set ((CoordJ → ℝ) × RatCoords) :=
      {q | q.2.1 (Z, W) = 0}
    have hE : MeasurableSet E := by
      apply measurableSet_eq_fun
      · exact (measurable_pi_apply (Z, W)).comp
          (measurable_fst.comp measurable_snd)
      · exact measurable_const
    let S : Ω → (CoordJ → ℝ) × RatCoords :=
      fun ω => (pairJ ⊤ (h ω), measurableRatCoordsVersion (D n) (hD n) ω)
    have hSm : Measurable S :=
      ((measurable_pairJ ⊤).comp hh).prodMk
        (measurable_measurableRatCoordsVersion (D n) (hD n))
    have hSource : ∀ᵐ ω ∂P, S ω ∈ E := by
      filter_upwards [ae_eq_measurableRatCoordsVersion (D n) (hD n)] with ω hω
      have hc := congrArg (fun q : RatCoords => q.1 (Z, W)) hω
      have hz : finiteCircleCoords (D n ω) (Z, W) = 0 := by
        rw [finiteCircleCoords_zero_zero (D n ω) Z W hZ hW, hZW, edist_self]
      change (measurableRatCoordsVersion (D n) (hD n) ω).1 (Z, W) = 0
      exact hc.symm.trans hz
    have hSourceMap : ∀ᵐ q ∂P.map S, q ∈ E :=
      (ae_map_iff hSm.aemeasurable hE).2 hSource
    exact (ae_map_iff (hY n).aemeasurable hE).1 (hLaw n ▸ hSourceMap)
  have hzero : ∀ᵐ ω ∂P', ∀ n Z W, Z.radius = 0 → W.radius = 0 →
      Z.center = W.center → (Y n ω).2.1 (Z, W) = 0 := by
    apply ae_all_iff.mpr; intro n
    apply ae_all_iff.mpr; intro Z
    apply ae_all_iff.mpr; intro W
    by_cases hZ : Z.radius = 0
    · by_cases hW : W.radius = 0
      · by_cases hZW : Z.center = W.center
        · filter_upwards [hfinite n Z W hZ hW hZW] with ω hω _ _ _
          exact hω
        · exact ae_of_all _ (fun ω _ _ h => (hZW h).elim)
      · exact ae_of_all _ (fun ω _ h => (hW h).elim)
    · exact ae_of_all _ (fun ω h => (hZ h).elim)
  filter_upwards [hConv, hzero] with ω hω hzeroω Z W hZ hW hZW
  have hcoord := circle_coord_tendsto hω Z W
  have hconst : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
  exact tendsto_nhds_unique hcoord
    (hconst.congr' (Eventually.of_forall fun n =>
      (hzeroω n Z W hZ hW hZW).symm))

end SupercriticalLQGUniqueness.B2.DG20Lim
