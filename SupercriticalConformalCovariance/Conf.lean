import SupercriticalConformalCovariance.Tangent.Conf
import SupercriticalConformalCovariance.Small.TargetConfinedLSC
import SupercriticalConformalCovariance.Good.TargetConfinedLSC

/-!
# Shared diagonal-corrected confinement interface

`SupercriticalConformalCovariance.Small` and `SupercriticalConformalCovariance.Good` arrived as independent snapshots. `SupercriticalConformalCovariance.Small.conf`
and `SupercriticalConformalCovariance.Small.confPullCompact` are the chosen constructors; the Tangent
names abbreviate them. These equalities identify the older Good constructors.
Consumers should import this module rather than add another constructor.
-/

noncomputable section
open SupercriticalLQGUniqueness

namespace SupercriticalConformalCovariance.Conf

theorem confDisk_eq_small (M : LSCMetric) (R : ℝ) :
    SupercriticalConformalCovariance.Tangent.confDisk M R = SupercriticalConformalCovariance.Small.conf M 0 R := by
  rfl

theorem confPull_eq_small (M : LSCMetric) (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K, L)) (hj : Function.Injective j) :
    SupercriticalConformalCovariance.Tangent.confPull M L K hK hL j hj =
      SupercriticalConformalCovariance.Small.confPullCompact M L K hK hL j hj := by
  apply Subtype.ext
  funext p
  rfl

theorem small_conf_eq_good (M : LSCMetric) (c : ℂ) (R : ℝ) :
    SupercriticalConformalCovariance.Small.conf M c R = SupercriticalConformalCovariance.Good.ConfinedLSC.conf M c R := by
  apply Subtype.ext
  funext p
  rfl

theorem small_confPull_eq_good (M : LSCMetric) (L K : Set ℂ) (hK : IsCompact K)
    (hL : IsCompact L) (j : C(K, L)) (hj : Function.Injective j) :
    SupercriticalConformalCovariance.Small.confPullCompact M L K hK hL j hj =
      SupercriticalConformalCovariance.Good.TargetConfinedLSC.confPullCompact M L K hK hL j hj := by
  apply Subtype.ext
  funext p
  rfl

end SupercriticalConformalCovariance.Conf
