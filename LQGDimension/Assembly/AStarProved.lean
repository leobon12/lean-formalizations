import LQGDimension.Assembly.AStar
import LQGDimension.Gaussian.Basic
import LQGDimension.Gaussian.SudakovFernique
import LQGDimension.Section2.ZCovPSD
import LQGDimension.Section2.Finite
import LQGDimension.Section2.Subadditive
import LQGDimension.Section2.LowerBound

/-!
# The first assertion of Theorem 1.1, unconditionally

`a_n` is finite and subadditive, and `0 < a* = lim a_n / n = inf_{n ≥ 1} a_n / n`.
-/

namespace LQGDimension

theorem aOneFinite : Blueprint.AOneFinite :=
  aOneFinite_of sudakovFernique gramBridge gramRepresentation maxIntegrable zCovPSD

theorem aSubadditiveE : Blueprint.ASubadditiveE :=
  aSubadditiveE_of sudakovFernique gramBridge gramRepresentation maxIntegrable zCovPSD

theorem aLinearLowerBound : Blueprint.ALinearLowerBound :=
  aLinearLowerBound_of sudakovFernique gramBridge gramRepresentation maxIntegrable zCovPSD

/-- **Theorem 1.1, first assertion.** -/
theorem theorem11_aStar : Theorem11_AStar :=
  theorem11_aStar_of aOneFinite aSubadditiveE aLinearLowerBound

end LQGDimension
