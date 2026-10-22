import HigherDimLQGMetric.Limits.JointInternalDet
import HigherDimLQGMetric.Limits.RandomPrecompact

/-! Tightness of internal coordinates from a coupled ambient limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_internal_tight_of_ae_ambient_tendsto {d : ℕ}
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [IsProbabilityMeasure Q]
    (Dn : ℕ → E → ContMetric d) (D : E → ContMetric d)
    (hDn : ∀ n e, (Dn n e).IsLength)
    (hconv : ∀ᵐ e ∂Q, Tendsto (fun n => (Dn n e).1) atTop (𝓝 (D e).1))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U)
    (Y : ℕ → E → C(U × U, ℝ))
    (hY : ∀ n, Measurable (Y n))
    (hgraph : ∀ n e, Y n e = internalC (Dn n e) (hDn n e) hU hUc) :
    IsTightMeasureSet {ν : Measure C(U × U, ℝ) |
      ∃ n, ν = Q.map (Y n)} := by
  letI := hU.locallyCompactSpace
  letI : PolishSpace C(U × U, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable C(U × U, ℝ)
  have hc : ∀ᵐ e ∂Q, IsCompact (closure (range fun n => Y n e)) := by
    filter_upwards [hconv] with e he
    have heq : (fun n => Y n e) =
        (fun n => internalC (Dn n e) (hDn n e) hU hUc) :=
      funext fun n => hgraph n e
    rw [heq]
    exact l6c_internal_relcompact_of_ambient_tendsto
      (fun n => Dn n e) (D e) (fun n => hDn n e) he hU hUc
  exact l6c_random_precompact_tight Q Y hY hc

end HigherDimLQGMetric
