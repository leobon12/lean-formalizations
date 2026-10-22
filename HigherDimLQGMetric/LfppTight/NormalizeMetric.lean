import HigherDimLQGMetric.LfppTight.PerturbCompare
import HigherDimLQGMetric.LfppTight.CrossCompare
import HigherDimLQGMetric.ConvField.Shifts

/-! The additive constant of an LGF multiplies every convolution LFPP distance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_ae_lfppDist_addConst_normalized {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : Ω → DistRd d) (hg : IsNormalizedLGF g P)
    (b : Ω → DistRd d) (c : Ω → ℝ)
    (hbc : ∀ ω, b ω = addConst (g ω) (c ω)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ p : Rd d × Rd d,
      lfppDist κ ξ ε (b ω) p =
        Real.exp (ξ * c ω) * lfppDist κ ξ ε (g ω) p := by
  filter_upwards [l2b_ae_convMollify_addConst d hd κ hκ P g hg] with ω hw
  intro ε hε p
  have hfield : (fun z => convMollify κ ε (b ω) z) =
      fun z => convMollify κ ε (g ω) z + c ω := by
    funext z
    rw [hbc]
    exact hw ε hε z (c ω)
  change HigherDimLFPP.lfppDistOn ξ (fun z => convMollify κ ε (b ω) z)
    Set.univ p.1 p.2 = _
  rw [hfield, HigherDimLFPP.lfppDistOn_add_const]
  rfl

end HigherDimLQGMetric
