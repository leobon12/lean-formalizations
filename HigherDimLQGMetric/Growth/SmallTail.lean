import HigherDimLQGMetric.Growth.SmallPoint

/-!
# Uniform tails for the small-radius grid

Packet L2a. The thresholds are linear in the dyadic level and their failure probabilities
decay like `exp(-(d+2)(k+1))`, enough to pay for the `O(2^(dk))` grid points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem l2a_exists_small_grid_tails (hd : 2 ≤ d) {R : ℝ} (hR : 0 ≤ R) :
    ∃ Ap Ab C : ℝ, 0 < Ap ∧ 0 < Ab ∧ 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {h : Ω → DistRd d}, IsWholeSpaceLGF h P → ∀ (k : ℕ) (g : Rd d),
        g ∈ HigherDimLFPP.Osc.grid 0 R (l2a_smallScale k) →
        P.real {ω | Ap * ((k : ℝ) + 1) ≤
          |sphereAvg (h ω) (l2a_smallScale k) g - sphereAvg (h ω) 1 0|} ≤
          2 * Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) ∧
        P.real {ω | Ab * ((k : ℝ) + 1) ≤
          ⨆ p : l2a_largeBlock (Real.sqrt (d : ℝ)),
            |sphereAvg (h ω) (l2a_smallScale k * p.1.1)
              (l2a_smallScale k • p.1.2 + g) -
              sphereAvg (h ω) (l2a_smallScale k) g|} ≤
          C * Real.exp (-((d : ℝ) + 2) * ((k : ℝ) + 1)) := by
  obtain ⟨M, hM, hvar⟩ := l2a_exists_small_point_variance hd hR
  obtain ⟨c, C, hc, hC, hblock⟩ := l2a_exists_dyadic_block_tail hd
    (l2a_isCompact_largeBlock (Real.sqrt (d : ℝ)))
    (l2a_largeBlock_pos (Real.sqrt (d : ℝ)))
  set D : ℝ := (d : ℝ) + 2 with hD
  have hD0 : 0 < D := by positivity
  set Ap : ℝ := Real.sqrt (2 * M * D) with hAp
  set Ab : ℝ := Real.sqrt (D / c) with hAb
  have hAp0 : 0 < Ap := Real.sqrt_pos.2 (by positivity)
  have hAb0 : 0 < Ab := Real.sqrt_pos.2 (by positivity)
  refine ⟨Ap, Ab, C, hAp0, hAb0, hC, fun {Ω} _ {P} {h} hh k g hg => ?_⟩
  have hk : 0 < (k : ℝ) + 1 := by positivity
  constructor
  · have hvar' := hvar hh k g hg
    have hAp2 : Ap ^ 2 = 2 * M * D := Real.sq_sqrt (by positivity)
    have he : -(Ap * ((k : ℝ) + 1)) ^ 2 /
        (2 * (M * ((k : ℝ) + 1))) = -D * ((k : ℝ) + 1) := by
      rw [mul_pow, hAp2]
      field_simp
    have ht := l2a_point_tail hd hh (l2a_smallScale_pos k) one_pos g
      (0 : Rd d) hvar' (by positivity : 0 ≤ Ap * ((k : ℝ) + 1))
    rw [sub_add_cancel, he] at ht
    exact ht
  · have hAb2 : Ab ^ 2 = D / c := Real.sq_sqrt (by positivity)
    have hA : 0 ≤ Ab * ((k : ℝ) + 1) := by positivity
    have ht := hblock (-(k : ℤ)) g hh (Ab * ((k : ℝ) + 1)) hA
    rw [← l2a_smallScale_eq_zpow k] at ht
    have hreal := ENNReal.toReal_le_of_le_ofReal
      (by positivity : 0 ≤ C * Real.exp (-c * (Ab * ((k : ℝ) + 1)) ^ 2)) ht
    have he : -c * (Ab * ((k : ℝ) + 1)) ^ 2 =
        -D * ((k : ℝ) + 1) ^ 2 := by
      rw [mul_pow, hAb2]
      field_simp
    rw [he] at hreal
    have hsq : (k : ℝ) + 1 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    have hexp : Real.exp (-D * ((k : ℝ) + 1) ^ 2) ≤
        Real.exp (-D * ((k : ℝ) + 1)) :=
      Real.exp_monotone (mul_le_mul_of_nonpos_left hsq (by linarith))
    exact hreal.trans (mul_le_mul_of_nonneg_left hexp hC.le)

end HigherDimLQGMetric
