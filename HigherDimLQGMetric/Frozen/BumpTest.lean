import HigherDimLQGMetric.Frozen.RadialProfile
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Frozen definition: `bumpTest`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 57–59 (spherical averages of a distribution are limits of mollified ones): the radial mollifier
`ψ_{n,x}` at scale `2^{-n}` centred at `x`, normalized to unit mass: `ψ_{n,x}(y) = c_n⁻¹ ρ(2^{n+1}(y - x))`
with `c_n = ∫ ρ(2^{n+1}(w - x)) dw > 0`; it is constant on `B̄(x, 2^{-n-1})` and supported in
`B(x, 2^{-n})` (audit MA5 §3.3 note 3: radial mollifiers).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The radial mollifier at scale `2^{-n}` centred at `x`, of unit mass, as a test function. -/
def bumpTest {d : ℕ} (n : ℕ) (x : Rd d) : TestRd d where
  toFun y := (∫ w, radialProfile d ((2 : ℝ) ^ (n + 1) • (w - x)))⁻¹ *
    radialProfile d ((2 : ℝ) ^ (n + 1) • (y - x))
  contDiff' := contDiff_const.mul
    ((radialProfile d).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _))
  hasCompactSupport' := by
    have h1 : HasCompactSupport (fun y : Rd d => radialProfile d ((2 : ℝ) ^ (n + 1) • (y - x))) :=
      (radialProfile d).hasCompactSupport.comp_homeomorph
        ((Homeomorph.subRight x).trans
          (Homeomorph.smulOfNeZero ((2 : ℝ) ^ (n + 1)) (by positivity)))
    exact h1.mul_left
  tsupport_subset' := subset_univ _

end HigherDimLQGMetric
