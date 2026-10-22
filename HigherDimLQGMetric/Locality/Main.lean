import HigherDimLQGMetric.Locality.InsideMain
import HigherDimLQGMetric.Locality.FromInside
import HigherDimLQGMetric.LfppTight.TightMain
import HigherDimLQGMetric.Trunc.Main

/-! Subsequental LFPP limits satisfy the exact ξ-additive locality interface. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric

/-- [1] Lemma 3.11 in the corrected MA5 formulation. -/
theorem l7a_locality_of : ∀ d ξ κ, L7a_locality d ξ κ := by
  intro d ξ κ hB2 hDM εs hεs hεt Ω mΩ P hP h Dh hh hDh hstable
  obtain ⟨q, hDGZ, hAdapter⟩ := hB2
  have hd : 2 ≤ d := hDGZ.dim
  have hκ : HigherDimLFPP.IsLFPPKernel κ := hDGZ.kernel
  have hB2' : ∃ q : ℝ, DGZ.DGZHyp d κ ξ q ∧
      DGZ.RealEpsAdapterShape d κ ξ q :=
    ⟨q, hDGZ, hAdapter⟩
  have hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength :=
    (l7a_ae_stable_limit_good l6a_tight' ξ κ hB2' εs hεs hεt
      P h Dh hh hDh hstable).mono (fun _ hω => hω.1)
  exact l7a_additive_of_inside_locality hd P h Dh hh hDh hlen ξ
    (fun V hV z₀ ρ hρ hsph =>
      l7a_inside_locality l6a_tight' l2c_trunc hd ξ κ hκ hB2'
        hDM εs hεs hεt P h Dh hh hDh hstable V hV z₀ ρ hρ hsph)

end HigherDimLQGMetric
