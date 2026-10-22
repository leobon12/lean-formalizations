import HigherDimLQGMetric.Frozen.ConvKernelEps
import HigherDimLQGMetric.Frozen.RadialProfile

/-!
# Frozen definition: `convTrunc`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M6, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[1] (1.2) (`h * K_ε(x) = ∫ h(w) K_ε(x - w) dw`, an improper pairing: `K` is not compactly supported):
the truncation `w ↦ K_ε(z - w) χ_n(w - z)` with the radial cutoff `χ_n = ρ(·/(n+1))` (`1` on
`B̄(0, n+1)`, supported in `B(0, 2(n+1))`), centred at `z` (audit MA5 §3.3 note 3: then the pairing is
radial about `z`). Junk `0` unless `K` is smooth (`dite`; excluded for admissible kernels by the frozen
sanity theorem `convKernel_smooth_integral`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

open Classical in
/-- `w ↦ K_ε(z - w) χ_n(w - z)` as a test function (junk `0` unless `K` is smooth). -/
def convTrunc {d : ℕ} (κ : Rd d → ℝ) (ε : ℝ) (z : Rd d) (n : ℕ) : TestRd d :=
  if hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) then
    { toFun := fun w => convKernelEps κ ε (z - w) * radialProfile d (((n : ℝ) + 1)⁻¹ • (w - z))
      contDiff' := by
        refine ContDiff.mul ?_
          ((radialProfile d).contDiff.comp ((contDiff_id.sub contDiff_const).const_smul _))
        simp only [convKernelEps]
        exact contDiff_const.mul (hK.comp ((contDiff_const.sub contDiff_id).const_smul _))
      hasCompactSupport' := by
        have h1 : HasCompactSupport
            (fun w : Rd d => radialProfile d (((n : ℝ) + 1)⁻¹ • (w - z))) :=
          (radialProfile d).hasCompactSupport.comp_homeomorph
            ((Homeomorph.subRight z).trans
              (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (by positivity)))
        exact h1.mul_left
      tsupport_subset' := subset_univ _ }
  else 0

end HigherDimLQGMetric
