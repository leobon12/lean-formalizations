import HigherDimLQGContinuity.Improve.SourceGood
import HigherDimLQGContinuity.SiteEvents.UnitsGeom

/-!
# The site-unit window from fixed source geometry
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- For a covered site, the fixed global source event and the local site
references put its primary normalization in a polynomial mesh window. -/
theorem q11_site_unit_window {d : ℕ} (hd : 3 ≤ d)
    {G : ContMetric d} (hLength : G.IsLength)
    {U0 R H σ β Hup σup Hlo b mc A0 : ℝ}
    (hGood : Q11SourceGood G U0 R H σ β)
    (hR : 16 ≤ R) (hH : 1 ≤ H) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hβ : 1 ≤ β) (hmc : 0 < mc) (hA0 : 0 < A0)
    {z : Rd d} (hz : z ∈ ball (0 : Rd d) 3)
    {s S Δ : ℝ} (hs : 0 < s) (hs4 : s ≤ 1 / 4) (hS : 0 < S)
    (hRefs : SiteRefs Hup σup Hlo b mc A0
      ((G.affine s hs.ne' z).smul S⁻¹ (inv_pos.mpr hS)))
    (hΔ : 0 < Δ)
    (hΔmax : Δ ≤ min (1 / 4) (min (4 ^ β / (H * A0)) (mc / H)))
    (hscale : Δ ^ (2 : ℕ) ≤ s ∧ s ≤ Δ) :
    Δ ^ (2 * β + 1) ≤ S ∧ S ≤ Δ ^ (-(2 * β + 1)) := by
  have hR' : 16 ≤ R + 1 := by linarith
  exact (siteUnit_bounds hd G hLength hs hs4 hS hR' (by linarith) hσ hσ1
    hβ hmc hA0 hz hGood.2.2.1 hGood.2.2.2 hRefs).2
      Δ hΔ hΔmax hscale.1 hscale.2

end HigherDimLQGContinuity
