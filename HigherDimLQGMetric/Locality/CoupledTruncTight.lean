import HigherDimLQGMetric.Locality.CoupledTight
import HigherDimLQGMetric.Locality.ConvergenceC

/-! Tight internal coordinates of a truncated LFPP sequence coupled to an
ambient metric limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_coupled_trunc_internal_tight {d : ℕ}
    (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [IsProbabilityMeasure Q]
    (g : ℕ → E → DistRd d) (hg : ∀ n, Measurable (g n))
    (D : E → ContMetric d)
    (hballs : ∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun n (p : Rd d × Rd d) =>
          (aEps κ ξ (εs n))⁻¹ *
            fieldLfpp ξ (truncMollify κ (εs n) (g n e)) p)
        ⇑(D e).1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsTightMeasureSet {ν : Measure C(U × U, ℝ) |
      ∃ n, ν = Q.map (fun e => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs n) (g n e))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs n) (g n e))
        hU hUc)} := by
  let Dn : ℕ → E → ContMetric d := fun n e =>
    l7a_truncScaledMetric hd κ hκ ξ (hεs n) (g n e)
  let Y : ℕ → E → C(U × U, ℝ) := fun n e =>
    internalC (Dn n e) (l7a_truncScaledMetric_isLength hd κ hκ ξ
      (hεs n) (g n e)) hU hUc
  have hDn : ∀ n e, (Dn n e).IsLength := fun n e =>
    l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs n) (g n e)
  have hconv : ∀ᵐ e ∂Q,
      Tendsto (fun n => (Dn n e).1) atTop (𝓝 (D e).1) := by
    filter_upwards [hballs] with e he
    exact l7a_tendsto_truncScaledMetric_of_balls hd κ hκ ξ εs hεs
      (fun n => g n e) (D e) he
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    let Uo : TopologicalSpace.Opens (Rd d) := ⟨U, hU⟩
    exact (l7a_measurable_truncScaledInternal hd κ hκ ξ (hεs n)
      Uo hUc).comp (hg n)
  exact l7a_internal_tight_of_ae_ambient_tendsto Q Dn D hDn hconv
    hU hUc Y hY (fun _ _ => rfl)

end HigherDimLQGMetric
