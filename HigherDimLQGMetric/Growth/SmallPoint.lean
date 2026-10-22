import HigherDimLQGMetric.Growth.LargeLimit

/-!
# Sphere-average point variances at small dyadic radii

Packet L2a. The variance bound is uniform over the spatial grid used for the thick-point
estimate; it follows from F3's `log(1/r) + O_R(1)` theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem l2a_exists_small_point_variance (hd : 2 ≤ d) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 < M ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {h : Ω → DistRd d}, IsWholeSpaceLGF h P → ∀ (k : ℕ)
      (g : Rd d), g ∈ HigherDimLFPP.Osc.grid 0 R (l2a_smallScale k) →
        Var[fun ω => sphereAvg (h ω) (l2a_smallScale k) g -
          sphereAvg (h ω) 1 0; P] ≤ M * ((k : ℝ) + 1) - 1 := by
  obtain ⟨K, hK⟩ := exists_abs_variance_sphereAvg_sub_sub_log_le hd
    (Real.sqrt (d : ℝ) * R)
  set M : ℝ := 2 + |K| with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M, hM0, fun {Ω} _ {P} {h} hh k g hg => ?_⟩
  have ha : 0 < l2a_smallScale k := l2a_smallScale_pos k
  have ha1 : l2a_smallScale k ≤ 1 := by
    unfold l2a_smallScale
    exact (inv_le_one₀ (by positivity : (0 : ℝ) < 2 ^ k)).2
      (one_le_pow₀ (by norm_num))
  have hbox := HigherDimLFPP.Osc.grid_subset_box 0 hR ha hg
  have hnorm : ‖g - (0 : Rd d)‖ ≤ Real.sqrt (d : ℝ) * R :=
    HigherDimLFPP.Osc.norm_sub_le_of_mem_box hR hbox
  have hvar0 := hK hh ha ha1 g (0 : Rd d) (by simpa only [mul_one] using hnorm)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlog : Real.log (1 / l2a_smallScale k) = (k : ℝ) * Real.log 2 := by
    rw [l2a_smallScale, one_div, inv_inv, Real.log_pow]
  have hvar : Var[fun ω => sphereAvg (h ω) (l2a_smallScale k) g -
      sphereAvg (h ω) 1 0; P] ≤ (k : ℝ) * Real.log 2 + K := by
    rw [hlog] at hvar0
    have := (abs_le.mp hvar0).2
    linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hKle : K ≤ |K| := le_abs_self K
  have hmul : (k : ℝ) * Real.log 2 ≤ (k : ℝ) := by nlinarith
  dsimp [M]
  nlinarith [mul_nonneg (abs_nonneg K) hk]

end HigherDimLQGMetric
