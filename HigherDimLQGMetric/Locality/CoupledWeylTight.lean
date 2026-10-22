import HigherDimLQGMetric.Locality.CoupledTruncTight
import HigherDimLQGMetric.Metric.WeylMetric

/-! Tight internal coordinates when truncated LFPP converges to a Weyl
transform of an almost-sure length metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_coupled_weyl_trunc_internal_tight {d : ℕ}
    (hd : 2 ≤ d) (κ : Rd d → ℝ)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    {E : Type*} [MeasurableSpace E] (Q : Measure E) [IsProbabilityMeasure Q]
    (g : ℕ → E → DistRd d) (hg : ∀ n, Measurable (g n))
    (D : E → ContMetric d) (f : E → C(Rd d, ℝ))
    (hD : ∀ᵐ e ∂Q, (D e).IsLength)
    (hballs : ∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun n (p : Rd d × Rd d) =>
          (aEps κ ξ (εs n))⁻¹ *
            fieldLfpp ξ (truncMollify κ (εs n) (g n e)) p)
        (fun p => (weylScale ξ (f e) (D e) p.1 p.2).toReal) atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsTightMeasureSet {ν : Measure C(U × U, ℝ) |
      ∃ n, ν = Q.map (fun e => internalC
        (l7a_truncScaledMetric hd κ hκ ξ (hεs n) (g n e))
        (l7a_truncScaledMetric_isLength hd κ hκ ξ (hεs n) (g n e))
        hU hUc)} := by
  classical
  let D' : E → ContMetric d := fun e =>
    if h : (D e).IsLength then weylMetric ξ (f e) (D e) h
    else fieldLfppMetric 0 (0 : C(Rd d, ℝ))
  have hballs' : ∀ᵐ e ∂Q, ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn
        (fun n (p : Rd d × Rd d) =>
          (aEps κ ξ (εs n))⁻¹ *
            fieldLfpp ξ (truncMollify κ (εs n) (g n e)) p)
        ⇑(D' e).1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    filter_upwards [hD, hballs] with e hDe he R hR
    have hEq (p : Rd d × Rd d) :
        (D' e).1 p = (weylScale ξ (f e) (D e) p.1 p.2).toReal := by
      simpa [D', hDe] using weylMetric_apply hDe p
    convert he R hR using 1
    ext p
    exact hEq p
  exact l7a_coupled_trunc_internal_tight hd κ hκ ξ εs hεs Q g hg
    D' hballs' hU hUc

end HigherDimLQGMetric
