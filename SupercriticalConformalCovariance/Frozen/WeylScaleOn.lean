import SupercriticalLQGUniqueness.Frozen.WeylScale

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `weylScaleOn`. Declaration unchanged from the candidate `CandWeylScaleOn.lean` (sha256 10eb1c0dcdbe6cf4…). -/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance

open SupercriticalLQGUniqueness (LSCMetric)

/-- Weyl scaling on a domain (Gwynne–Miller 1905.00384v2 (1.7), l. 281–286, applied to the internal
metric `D (·, ·; V)` as in GM l. 310–321 and GMU Remark 1.5; DG (1.11), l. 448–452, with paths confined to
`V`): for a continuous function `f` on `V`, which may be unbounded near `∂V`, `(e^{ξ f} · D)(x, y; V)` is the
infimum, over curves `P` in `V` from `x` to `y` parametrized by `D`-length (unit speed on `[0, L]`), of
`∫₀ᴸ e^{ξ f (P t)} dt`, with `inf ∅ = ∞`. The curve and unit-speed conditions are those of the sealed
`SupercriticalLQGUniqueness.weylScale`, read for the `ℂ`-valued path `t ↦ (P t : ℂ)`; for a path in `V`
its `D`-length equals its length for the internal metric `D (·, ·; V)`. -/
def weylScaleOn (ξ : ℝ) {V : Set ℂ} (f : C(V, ℝ)) (D : LSCMetric) (p : V × V) : ℝ≥0∞ :=
  ⨅ (P : ℝ → V) (L : ℝ) (_ : D.IsCurve (fun t => (P t : ℂ)) 0 L)
    (_ : HasUnitSpeedOn (D.pt ∘ fun t => (P t : ℂ)) (Icc 0 L)) (_ : P 0 = p.1) (_ : P L = p.2),
    ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))

end SupercriticalConformalCovariance
