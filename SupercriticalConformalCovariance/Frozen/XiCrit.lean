import SupercriticalLQGUniqueness.Frozen.IsLFPPExponent

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `xiCrit`. Declaration unchanged from the candidate `CandXiCrit.lean` (sha256 a7d5394767b41a9d…). -/

set_option autoImplicit false

noncomputable section

open Set

namespace SupercriticalConformalCovariance

open SupercriticalLQGUniqueness (IsLFPPExponent)

/-- DG (1.7), l. 345–348: the critical parameter `ξ_crit := inf {ξ > 0 : Q(ξ) = 2}`, where `Q(ξ)` is the
LFPP distance exponent of DG (1.5) (l. 330–333). Here `Q(ξ) = 2` is read as `IsLFPPExponent ξ 2`, which is
equivalent because the exponent is unique (sealed `existsUnique_isLFPPExponent`). The set is bounded
below by `0`; if it were empty, mathlib's `sInf ∅ = 0` would make the premise `ξ_crit < ξ` hold for every
`ξ > 0`, which only strengthens a theorem assuming it. Paper l. 17 ("Fix `ξ > ξ_crit`"). -/
def xiCrit : ℝ :=
  sInf {x : ℝ | ∃ hx : 0 < x, IsLFPPExponent ⟨x, hx⟩ 2}

end SupercriticalConformalCovariance
