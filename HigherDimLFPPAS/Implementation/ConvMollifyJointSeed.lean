import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Signed.Radial
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLQGMetric.ConvField.RadialMain

/-!
# Provider of the frozen theorem `HigherDimLFPPAS.convMollify_joint_seed`

`convMollify_joint_seed_impl` states the frozen anchor `HigherDimLFPPAS/Frozen/ConvMollifyJointSeed.lean` verbatim
(for the normalized LGF, a.s., for every `ε > 0` and `z` the truncated pairings converge to `h*_ε(z)`, and
`(ε, z) ↦ h*_ε(z)` is continuous on `(0, ∞) × ℝ^d`; rulings L7, L8). Proof (the statement audit's witness
`w_joint_nonneg`, `planning/audits/S1-statement-audit.md`, with the sign-free copies of packet G1): on one
probability-one event, `Signed.l2b_ae_convMollify_tendsto_seed` gives the convergence of the truncated pairings
to the radial integral times the sphere area, `Signed.l2b_radial_seed` identifies that limit with
`convMollify` (the host's `l2b_sphere_area` converts the constant), and
`Signed.l2b_ae_convMollify_continuousOn_seed` gives the joint continuity. This module imports no frozen theorem
anchor of this library.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLFPPAS.Implementation

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The frozen statement of `convMollify_joint_seed`, proved. -/
theorem convMollify_joint_seed_impl :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P,
          (∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
            Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z))) ∧
          ContinuousOn (fun p : ℝ × Rd d => convMollify κ p.1 (h ω) p.2) (Ioi 0 ×ˢ univ) := by
  intro d hd κ hκ Ω _ P _ h hh
  filter_upwards [Signed.l2b_ae_convMollify_tendsto_seed d hd κ hκ P h hh,
    Signed.l2b_radial_seed d hd κ hκ P h hh,
    Signed.l2b_ae_convMollify_continuousOn_seed d hd κ hκ P h hh] with ω h1 h2 h3
  refine ⟨fun ε hε z => ?_, h3⟩
  rw [h2 ε hε z, ← l2b_sphere_area d hd]
  exact h1 ε hε z

end HigherDimLFPPAS.Implementation
