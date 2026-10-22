import HigherDimLQGMetric.Growth.PointTail
import HigherDimLQGMetric.Sphere.Scaling
import HigherDimLFPP.Field.OscBlock

/-!
# Dyadic block tails for sphere averages

Packet L2a. This specializes F3's compact Gaussian supremum tail to dyadically rescaled
sphere-average differences. The scaling identity is deterministic for dyadic factors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistRd d}

/-- The compact-block Gaussian tail persists after every dyadic affine change of scale. -/
theorem l2a_exists_dyadic_block_tail (hd : 2 ≤ d) {L : Set (ℝ × Rd d)}
    (hL : IsCompact L) (hL0 : ∀ p ∈ L, 0 < p.1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (k : ℤ) (w : Rd d)
      {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ A : ℝ, 0 ≤ A →
        P {ω | A ≤ ⨆ p : L, |sphereAvg (h ω) ((2 : ℝ) ^ k * p.1.1)
          (((2 : ℝ) ^ k) • p.1.2 + w) - sphereAvg (h ω) ((2 : ℝ) ^ k) w|} ≤
          ENNReal.ofReal (C * Real.exp (-c * A ^ 2)) := by
  obtain ⟨c, C, hc, hC, htail⟩ := exists_tail_iSup_sphereAvg_sub_le hd hL hL0
  refine ⟨c, C, hc, hC, fun k w {Ω} _ {P} {h} hh A hA => ?_⟩
  have hρ : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) _
  have hg := hh.affineComp hρ w
  have ht := htail hg A hA
  simpa only [sphereAvg_affineComp_two_zpow, mul_one, smul_zero, zero_add] using ht

end HigherDimLQGMetric
