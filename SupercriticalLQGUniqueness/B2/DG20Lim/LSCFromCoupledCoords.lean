import SupercriticalLQGUniqueness.B2.DG20Lim.Section51RDataExist
import SupercriticalLQGUniqueness.B2.DG20Lim.LSCConvergence
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCoordRange

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem ae_lscTendsto_of_rdata_coords
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : ℕ → Ω → (CoordJ → ℝ) × RatCoords)
    (Ylim : Ω → (CoordJ → ℝ) × RatCoords)
    (hConv : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)))
    (hRange : ∀ᵐ ω ∂P, ∀ n,
      finiteCircleCoords (circleCoordsInv (Y n ω).2.1) = (Y n ω).2.1)
    (hLen : ∀ᵐ ω ∂P, ∀ n,
      (circleCoordsInv (Y n ω).2.1).IsLength)
    (hRData : ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Pcircle => (Ylim ω).2.1 (O, Pcircle)) ∧
      R.around = (Ylim ω).2.2) :
    ∀ᵐ ω ∂P, ∃ R : RData,
      R.across = (fun O Pcircle => (Ylim ω).2.1 (O, Pcircle)) ∧
      R.around = (Ylim ω).2.2 ∧
      LSCTendsto
        (fun n => finiteMetricE (circleCoordsInv (Y n ω).2.1))
        R.toLSCFun.1 := by
  filter_upwards [hRange, hLen, hRData] with ω hrange hlen hR
  obtain ⟨R, hAcross, hAround⟩ := hR
  refine ⟨R, hAcross, hAround, ?_⟩
  apply R.lscTendsto_of_circleDist
    (fun n => circleCoordsInv (Y n ω).2.1) hlen
  intro O Pcircle
  have hcoord : Tendsto (fun n => (Y n ω).2.1 (O, Pcircle)) atTop
      (𝓝 ((Ylim ω).2.1 (O, Pcircle))) :=
    ((continuous_apply (O, Pcircle)).comp
      (continuous_fst.comp continuous_snd)).tendsto _ |>.comp (hConv ω)
  change Tendsto
    (fun n => finiteCircleCoords (circleCoordsInv (Y n ω).2.1) (O, Pcircle))
    atTop (𝓝 (R.across O Pcircle))
  rw [show (fun n => finiteCircleCoords (circleCoordsInv (Y n ω).2.1)
      (O, Pcircle)) = (fun n => (Y n ω).2.1 (O, Pcircle)) from
    funext fun n => congrFun (hrange n) (O, Pcircle), hAcross]
  exact hcoord

end SupercriticalLQGUniqueness.B2.DG20Lim
