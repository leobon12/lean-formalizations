import SupercriticalLQGUniqueness.B2.Iface.Statements
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3

/-!
# Set-distance notation bridge

The Pfeffer interface and the uniqueness library use separate names for the
same nested infimum of an `LSCMetric` over two sets.  This adapter records the
definitional equality used by the rational-circle packet.
-/

set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLFPPAS

/-- Pfeffer's set-distance observable is definitionally the uniqueness
library's ambient set-distance. -/
theorem iface_setDistance_eq_setDist
    (D : SupercriticalLQGUniqueness.LSCMetric) (A B : Set ℂ) :
    SupercriticalLQGUniqueness.B2.Iface.setDistance D.1 A B =
      SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist D A B := by
  rfl

end SupercriticalLFPPAS
