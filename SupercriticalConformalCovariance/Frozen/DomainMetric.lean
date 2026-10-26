import SupercriticalConformalCovariance.Frozen.WeylScaleOn
import LQGMetric.Statement.Field

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `domainMetric`. Declaration unchanged from the candidate `CandDomainMetric.lean` (sha256 6ae042c464c3f370…). -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalConformalCovariance

open SupercriticalLQGUniqueness (LSCMetric)

/-- The **domain metric** `D_h(·, ·; V)` of a field `h = h₀|_V + f` on the open set `V`, given through a
realization `(h₀, f)` (`IsDomainRealization`): Gwynne–Miller 1905.00384v2 l. 310–321 (`D_{h|_U} :=
D_h(·, ·; U)`, `D_{h̊^U} := e^{−ξ 𝔥^U} · D_{h|_U}`, then `D_{h̊^U + f}`) and GMU Remark 1.5; paper l. 18–20
(`D_h(x, y; W)` infimizes `D_h`-length over paths in `W`, `+∞` allowed) and l. 26. It is the Weyl scaling
`e^{ξ f} · D_{h₀}(·, ·; V)` of the internal metric of the whole-plane metric `D_{h₀}` on `V` (`weylScaleOn`):
the infimum over curves in `V` of `∫ e^{ξ f} d len(·; D_{h₀})`. For `f = 0` it is the internal metric
`D_{h₀}(·, ·; V)`. Almost surely it does not depend on the realization
(`domainMetric_ae_eq_of_isDomainRealization`). -/
def domainMetric (ξ : ℝ) (D : DistC → LSCMetric) (V : Opens ℂ) (h₀ : DistC) (f : C(V, ℝ)) :
    V × V → ℝ≥0∞ :=
  weylScaleOn ξ f (D h₀)

end SupercriticalConformalCovariance
