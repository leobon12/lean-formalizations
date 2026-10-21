import SmallGammaGeodesics.CC.BiLip
import SmallGammaGeodesics.CC.Improve
import SmallGammaGeodesics.CC.GoodAnnulusProb
import SmallGammaGeodesics.CC.Prop21

/-!
# The one-sided master theorem from [3] Prop 2.1 (track CC, ruling G29)

`confCovLE_of_biLip_improve` (the iteration replacing `C*`, `Core/Interfaces.lean`) applied to
* the one-sided domain bi-Lipschitz bound `confBiLipLE_of_smallScale` (CC8), and
* the improvement step `confImprove_of_goodAnnulus` (CC10) fed by the good-annulus input
  `goodAnnulusInput_holds` (CC9a/CC9b),
all three from `ConfSmallScale` ([3] Prop 2.1), which `confSmallScale_holds` proves (CC6b). Hence
`masterCCLE_holds : MasterCCLE`, the keystone of track CC.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- **[3] Prop 3.6 (one-sided conformal covariance)** for one canonical metric, from [3] Prop 2.1 -/
theorem confCovLE_of_confSmallScale {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : GaussianLQG.IsCanonicalLQGMetric γ D) (hS : ConfSmallScale γ D) : ConfCovLE γ D :=
  confCovLE_of_biLip_improve (confBiLipLE_of_smallScale hγ hγ2 hD hS)
    (confImprove_of_goodAnnulus hγ hγ2 hD (goodAnnulusInput_holds hγ hγ2 hD hS))

/-- `MasterCCLE` from [3] Prop 2.1 for every canonical metric -/
theorem masterCCLE_of_confSmallScale
    (hS : ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ D : DistC → ContMetric,
      GaussianLQG.IsCanonicalLQGMetric γ D → ConfSmallScale γ D) : MasterCCLE :=
  fun γ hγ hγ2 D hD => confCovLE_of_confSmallScale hγ hγ2 hD (hS γ hγ hγ2 D hD)

/-- **The one-sided master theorem of track CC** (canonical metrics), unconditionally -/
theorem masterCCLE_holds : MasterCCLE :=
  masterCCLE_of_confSmallScale fun _ hγ hγ2 _ hD => confSmallScale_holds hγ hγ2 hD

end SmallGammaGeodesics.CC
