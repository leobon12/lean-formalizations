import HigherDimLFPPAS.Core.Interfaces
import HigherDimLFPPAS.Signed.KernelDecay
import HigherDimLFPPAS.Signed.Radial
import HigherDimLFPPAS.Signed.Sec4
import HigherDimLFPPAS.Signed.LFPP
import HigherDimLQGMetric.ConvField.Basic
import HigherDimLQGMetric.Kernel.ConvKernelMain
import HigherDimLQGMetric.ConvField.RadialMain
import HigherDimLQGMetric.ConvField.JointMain
import HigherDimLQGMetric.Sec4.Scale
import HigherDimLQGMetric.Sec4.Lemma43Meas
import HigherDimLQGMetric.Main.Cor104

/-!
# Seed facts assembled from existing kernel and convolution-field results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Glue

open HigherDimLQGMetric HigherDimLFPPAS.Core HigherDimLFPPAS.Signed
open HigherDimLFPP

theorem seedFacts_of_admissible {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPPAS.IsAdmissibleSeed κ) : Core.SeedFacts d κ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := l1c_convKernel_seed d (by omega) κ hκ
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω _ P _ h hh
    exact l2b_radial_seed d (by omega) κ hκ P h hh
  · intro Ω _ P _ h hh
    filter_upwards [l2b_ae_convMollify_tendsto_seed d (by omega) κ hκ P h hh] with ω hω
    intro ε hε z
    have hlim := hω ε hε z
    rw [l2b_convMollify_eq_of_tendsto hlim]
    exact hlim
  · intro Ω _ P _ h hh
    exact l2b_ae_convMollify_continuousOn_seed d (by omega) κ hκ P h hh
  · intro Ω _ P _ h hh u r hr
    exact l9b_ae_convMollify_affine_seed (by omega) hκ hh u hr
  · intro ξ ε hε
    exact l10a_aEps_pos_seed (by omega) hκ ξ hε
  · exact l9b_eventually_locHyp_seed (by omega) hκ
  · intro CK hCK0 hCK ε s hε hε1 hs ha hZ g z C hC0 hφ hψ hcont hgrowth
    exact l9b_locField_error_seed (by omega) hκ hCK0 hCK hε hε1 hs ha hZ hC0 hφ hψ hcont hgrowth
  · intro ξ D c hD Ω _ P _ h hh ε hrad hZ r hr24 u C hC
    exact ref1_lemma43_aeEventIn_seed hd hκ hD hh hrad hZ hr24 u hC

theorem seedFacts_of_isLFPPKernel {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) : Core.SeedFacts d κ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := l1c_convKernel d (by omega) κ hκ
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Ω _ P _ h hh
    exact l2b_radial d (by omega) κ hκ P h hh
  · intro Ω _ P _ h hh
    filter_upwards [l2b_ae_convMollify_tendsto d (by omega) κ hκ P h hh] with ω hω
    intro ε hε z
    have hlim := hω ε hε z
    rw [l2b_convMollify_eq_of_tendsto hlim]
    exact hlim
  · intro Ω _ P _ h hh
    exact l2b_ae_convMollify_continuousOn d (by omega) κ hκ P h hh
  · intro Ω _ P _ h hh u r hr
    exact l9b_ae_convMollify_affine (by omega) hκ hh u hr
  · intro ξ ε hε
    exact l10a_aEps_pos (by omega) hκ ξ hε
  · exact l9b_eventually_locHyp (by omega) hκ
  · intro CK hCK0 hCK ε s hε hε1 hs ha hZ g z C hC0 hφ hψ hcont hgrowth
    exact l9b_locField_error (by omega) hκ hCK0 hCK hε hε1 hs ha hZ hC0 hφ hψ hcont hgrowth
  · intro ξ D c hD Ω _ P _ h hh ε hrad hZ r hr24 u C hC
    exact ref1_lemma43_aeEventIn hd hκ hD hh hrad hZ hr24 u hC

end HigherDimLFPPAS.Glue
