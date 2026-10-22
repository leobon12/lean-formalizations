import HigherDimLQGMetric.Growth.LargePoint

/-!
# Uniform dyadic block tails at large radii

Packet L2a. F3's compact block tail gives an inverse-square tail when the threshold grows
like the square root of the logarithm of the block index.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

def l2a_largeBlock (R : ℝ) : Set (ℝ × Rd d) :=
  Icc (1 / 2 : ℝ) 1 ×ˢ closedBall (0 : Rd d) R

theorem l2a_isCompact_largeBlock (R : ℝ) : IsCompact (l2a_largeBlock (d := d) R) :=
  isCompact_Icc.prod (isCompact_closedBall _ _)

theorem l2a_largeBlock_pos (R : ℝ) (p : ℝ × Rd d)
    (hp : p ∈ l2a_largeBlock R) : 0 < p.1 := by
  have := hp.1.1
  linarith

theorem l2a_exists_large_block_tail (hd : 2 ≤ d) (R : ℝ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      {P : Measure Ω} {h : Ω → DistRd d}, IsWholeSpaceLGF h P → ∀ k : ℕ,
        P.real {ω | Real.sqrt ((2 / c) * Real.log ((k : ℝ) + 1)) ≤
          ⨆ p : l2a_largeBlock R,
            |sphereAvg (h ω) ((2 : ℝ) ^ k * p.1.1) (((2 : ℝ) ^ k) • p.1.2) -
              sphereAvg (h ω) ((2 : ℝ) ^ k) 0|} ≤
          C * (((k : ℝ) + 1) ^ 2)⁻¹ := by
  obtain ⟨c, C, hc, hC, ht⟩ := l2a_exists_dyadic_block_tail hd
    (l2a_isCompact_largeBlock R) (l2a_largeBlock_pos R)
  refine ⟨c, C, hc, hC, fun {Ω} _ {P} {h} hh k => ?_⟩
  have hA : 0 ≤ Real.sqrt ((2 / c) * Real.log ((k : ℝ) + 1)) := Real.sqrt_nonneg _
  have htail := ht (k : ℤ) (0 : Rd d) hh _ hA
  simp only [zpow_natCast, add_zero] at htail
  rw [l2a_exp_sqrt_log hc k] at htail
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) htail

end HigherDimLQGMetric
