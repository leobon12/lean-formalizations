import SupercriticalConformalCovariance.ZBConformal.Covariance
import SupercriticalConformalCovariance.Frozen.IsGreenian

set_option autoImplicit false
noncomputable section

open TopologicalSpace
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GPull

/-- Greenian admissibility transports through the conformal bijection. -/
theorem isGreenian_of_conf {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (hV : IsGreenian V) : IsGreenian U :=
  SupercriticalConformalCovariance.ZBConformal.zbAdmissible_of_conf hφ hV


end SupercriticalConformalCovariance.GPull
