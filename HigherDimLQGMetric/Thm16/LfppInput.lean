import HigherDimLQGMetric.Thm16.LfppLower
import HigherDimLQGMetric.Main.ExponentBridge
import HigherDimLQGMetric.Sphere.Conv

/-! The B2/B3 interface provides tight normalized LFPP under the canonical field law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l9c_normLfpp_tight {d : ℕ} (hd : 3 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ) :
    TightFamily (normLGFLaw d)
      (fun ε H => toCMapRd ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε H))
      (Ioo (0 : ℝ) 1) := by
  have hnorm : IsNormalizedLGF (fun H : DistRd d => H) (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).2.1
  letI : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  have hDGZ : DGZ.DGZHyp d κ ξ (distExp d ξ) :=
    l10a_dgzHyp (by omega : 2 ≤ d) hκ hξ hsub
  exact (hL6a d ξ κ ⟨distExp d ξ, hDGZ,
    hB2 d κ ξ (distExp d ξ)⟩ (normLGFLaw d) id
      hnorm.1.isLGFPlusBddCont).2

end HigherDimLQGMetric
