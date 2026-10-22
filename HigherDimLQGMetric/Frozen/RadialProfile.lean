import HigherDimLQGMetric.Frozen.TestRd
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Frozen definition: `radialProfile`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 57–59, [1] (1.2) and (2.19) (radial mollifiers and radial cutoffs; audit MA5 §3.3 note 3):
the radial profile `ρ(y) = s(2 - ‖y‖)` (`s` = mathlib's `smoothTransition`), i.e. mathlib's explicit
`ContDiffBumpBase.ofInnerProductSpace` at ratio `2`: smooth, radial, values in `[0,1]`, `1` on `B̄(0,1)`,
support `B(0,2)`. Used instead of mathlib's `ContDiffBump`, whose profile is chosen by
`Classical.choice` and is not provably radial (LQGMetric deviation DEV-DFB2c).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The radial profile `ρ(y) = smoothTransition((2 - ‖y‖)/(2 - 1))`: a smooth radial test function,
`1` on `B̄(0,1)`, supported in `B(0,2)`, with values in `[0,1]`. -/
def radialProfile (d : ℕ) : TestRd d where
  toFun := (ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun 2
  contDiff' := by
    have hs := (ContDiffBumpBase.ofInnerProductSpace (Rd d)).smooth
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    have hA : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry (ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun)
        ((2, x) : ℝ × Rd d) :=
      hs.contDiffAt (prod_mem_nhds (Ioi_mem_nhds one_lt_two) Filter.univ_mem)
    have hB : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Rd d => ((2, y) : ℝ × Rd d)) x :=
      contDiffAt_const.prodMk contDiffAt_id
    exact hA.comp x hB
  hasCompactSupport' := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) 2) fun x hx => ?_
    have hsupp := (ContDiffBumpBase.ofInnerProductSpace (Rd d)).support 2 one_lt_two
    have hx' : x ∉ Function.support ((ContDiffBumpBase.ofInnerProductSpace (Rd d)).toFun 2) := by
      rw [hsupp]
      exact fun h => hx (Metric.ball_subset_closedBall h)
    exact Function.notMem_support.1 hx'
  tsupport_subset' := subset_univ _

end HigherDimLQGMetric
