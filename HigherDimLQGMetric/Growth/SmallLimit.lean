import HigherDimLQGMetric.Growth.SmallEventual

/-!
# Thick-point logarithmic bound for sphere averages

Packet L2a, cited input I8 of Lemma 2.13. Grid cells cover every small positive radius
and every center in a fixed closed ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistRd d}

/-- **Thick-point bound I8.** There is a deterministic slope such that almost surely,
at all sufficiently small radii and uniformly over the fixed closed ball,
the absolute sphere average is bounded by that slope times log(1/r). -/
theorem l2a_small_radius_log_bound (hd : 2 ≤ d) (hh : IsNormalizedLGF h P)
    {R : ℝ} (hR : 0 < R) :
    ∃ A : ℝ, 0 < A ∧ ∀ᵐ ω ∂P, ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        ∀ z ∈ closedBall (0 : Rd d) R,
          |sphereAvg (h ω) r z| ≤ A * Real.log r⁻¹ := by
  obtain ⟨Ap, Ab, hAp, hAb, hgrid⟩ :=
    l2a_ae_eventually_small_grid hd hh.1 hR.le
  set A : ℝ := 4 * (Ap + Ab) with hA
  have hA0 : 0 < A := by positivity
  refine ⟨A, hA0, ?_⟩
  filter_upwards [hgrid, hh.2] with ω hgrid hnorm
  obtain ⟨K, hK⟩ := eventually_atTop.1 hgrid
  refine ⟨l2a_smallScale (K + 2), l2a_smallScale_pos _, fun r hr hr₀ z hz => ?_⟩
  have hr1 : r ≤ 1 := hr₀.trans (by
    rw [l2a_smallScale_eq_half_pow]
    exact pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨k, hklo, hkhi⟩ :=
    exists_nat_pow_near_of_lt_one hr hr1 (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  have hkK : K + 1 ≤ k := by
    by_contra hc
    have hkk : k + 1 ≤ K + 2 := by omega
    have hbase : (2 : ℝ) ^ (k + 1) ≤ 2 ^ (K + 2) :=
      pow_le_pow_right₀ (by norm_num) hkk
    have hpow : (1 / 2 : ℝ) ^ (K + 2) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
      have hi := (inv_le_inv₀ (pow_pos (by norm_num : (0 : ℝ) < 2) (K + 2))
        (pow_pos (by norm_num : (0 : ℝ) < 2) (k + 1))).2 hbase
      simpa only [one_div, inv_pow] using hi
    rw [l2a_smallScale_eq_half_pow] at hr₀
    linarith only [hpow, hklo, hr₀]
  have ha : 0 < l2a_smallScale k := l2a_smallScale_pos k
  have hrhi : r ≤ l2a_smallScale k := by
    rw [l2a_smallScale_eq_half_pow]
    exact hkhi
  have hrlo : l2a_smallScale k / 2 ≤ r := by
    have he : l2a_smallScale k / 2 = (1 / 2 : ℝ) ^ (k + 1) := by
      rw [l2a_smallScale_eq_half_pow, pow_succ]
      ring
    rw [he]
    exact hklo.le
  let g : Rd d := HigherDimLFPP.Osc.gridOf 0 R (l2a_smallScale k) z
  have hg : g ∈ HigherDimLFPP.Osc.grid 0 R (l2a_smallScale k) :=
    l2a_gridOf_mem ha hz
  obtain ⟨hp, hb⟩ := hK k (by omega) g hg
  obtain ⟨hmem, hrad, hspace⟩ := l2a_small_cell ha hrlo hrhi hz
  let p : l2a_largeBlock (Real.sqrt (d : ℝ)) :=
    ⟨(r / l2a_smallScale k, (l2a_smallScale k)⁻¹ • (z - g)), hmem⟩
  have hbd := hb p
  simp only [p, hrad] at hbd
  rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul, sub_add_cancel] at hbd
  rw [hnorm, sub_zero] at hp
  have htri : |sphereAvg (h ω) r z| ≤
      |sphereAvg (h ω) r z - sphereAvg (h ω) (l2a_smallScale k) g| +
        |sphereAvg (h ω) (l2a_smallScale k) g| := by
    have := abs_add_le
      (sphereAvg (h ω) r z - sphereAvg (h ω) (l2a_smallScale k) g)
      (sphereAvg (h ω) (l2a_smallScale k) g)
    simpa only [sub_add_cancel] using this
  have hk1 : (1 : ℝ) ≤ k := by
    have : 1 ≤ k := by omega
    exact_mod_cast this
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hinv : (2 : ℝ) ^ k ≤ r⁻¹ := by
    have := (inv_le_inv₀ ha hr).2 hrhi
    simpa only [l2a_smallScale, inv_inv] using this
  have hlog : (k : ℝ) * Real.log 2 ≤ Real.log r⁻¹ := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hinv
  have hklog : (k : ℝ) + 1 ≤ 4 * Real.log r⁻¹ := by
    nlinarith
  dsimp [A]
  have hprod := mul_le_mul_of_nonneg_left hklog (add_pos hAp hAb).le
  nlinarith only [htri, hp, hbd, hprod]

end HigherDimLQGMetric
