import HigherDimLQGContinuity.Caps.Locality
import HigherDimLQGMetric.Events.ShellCoverGeom
import HigherDimLQGMetric.Growth.DyadicCells

/-!
# Geometry for the shell covering estimate (packet P4)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Recentring at a point within `r/20` of the anchor sends the local annulus
`ann 0 ½ max(7/2, s+1)` (the event domain of EB20, ruling N22) into the wider concentric shell used by Gaussian
decoupling. -/
theorem p4_affine_ann_subset {d : ℕ} {r s : ℝ} (hr : 0 < r)
    (_hs : 1 ≤ s) (hs10 : s ≤ 10) {a z : Rd d} (haz : ‖z - a‖ ≤ r / 20) :
    affinePt r z '' ann (0 : Rd d) (1 / 2) (max (7 / 2) (s + 1)) ⊆
      ann a (r / 4) (12 * r) := by
  rintro y ⟨x, hx, rfl⟩
  simp only [ann, sub_zero] at hx
  change r / 4 < ‖affinePt r z x - a‖ ∧ ‖affinePt r z x - a‖ < 12 * r
  have heq : affinePt r z x - a = r • x + (z - a) := by
    rw [affinePt_apply]
    abel
  have hupper : ‖affinePt r z x - a‖ ≤ r * ‖x‖ + ‖z - a‖ := by
    rw [heq]
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr] using norm_add_le (r • x) (z - a)
  have hlower : r * ‖x‖ ≤ ‖affinePt r z x - a‖ + ‖z - a‖ := by
    have he : r • x = (affinePt r z x - a) - (z - a) := by rw [heq]; abel
    calc
      r * ‖x‖ = ‖r • x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      _ = ‖(affinePt r z x - a) - (z - a)‖ := congrArg norm he
      _ ≤ ‖affinePt r z x - a‖ + ‖z - a‖ := norm_sub_le _ _
  have hm : max (7 / 2 : ℝ) (s + 1) ≤ 11 := max_le (by norm_num) (by linarith)
  constructor
  · nlinarith only [hlower, haz, hx.1, hr]
  · nlinarith only [hupper, haz, hx.2, hm, hr]

/-- Coordinatewise lattice rounding at mesh `r/(20√d)` lies within `r/20`
of its anchor. -/
theorem p4_round_center {d : ℕ} (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r)
    (a : Rd d) :
    ‖a - HigherDimLFPP.DGZ.latPt ((1 / (20 * Real.sqrt d)) * r)
      (HigherDimLFPP.DGZ.roundLat ((1 / (20 * Real.sqrt d)) * r) a)‖ ≤ r / 20 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsqr : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdpos
  have hmesh : 0 < (1 / (20 * Real.sqrt d)) * r := by positivity
  have h := shellCover_roundLat_dist_le hmesh a
  have heq : Real.sqrt (d : ℝ) * ((1 / (20 * Real.sqrt d)) * r) = r / 20 := by
    field_simp
  exact heq ▸ h

end HigherDimLQGContinuity
