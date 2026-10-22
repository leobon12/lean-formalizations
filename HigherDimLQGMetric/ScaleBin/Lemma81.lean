import HigherDimLQGMetric.ScaleBin.Lattice

/-!
# Lemma 8.1: the global scale-bin event

The probability is evaluated by outer measure. The event is covered by a
countable union of finite grid events; no measurability of the displayed
existential event is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)
open scoped ENNReal

/-- Lemma 8.1, with a polynomial rate uniform in the macroscopic radius and the LGF law. -/
theorem lemma81 {d : ℕ} (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q) :
    ∃ B a C : ℝ, 0 < B ∧ 0 < a ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ R : ℝ, 0 < R → ∀ ε ∈ Set.Ioo (0 : ℝ) (1 / 3),
        P {ω | ∃ r ∈ scaleLattice, ε ^ 2 * R ≤ r ∧ r ≤ ε * R ∧ ∃ z : Rd d, ‖z‖ < 5 * R ∧
            (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z = fun i => r / (100 * d) * m i) ∧
            ¬ (ε ^ B ≤ sNorm ξ Q (h ω) r z / macroS ξ Q (h ω) R ∧
                sNorm ξ Q (h ω) r z / macroS ξ Q (h ω) R ≤ ε ^ (-B))} ≤
          ENNReal.ofReal (C * ε ^ a) := by
  obtain ⟨D, hD, hvar⟩ := ScaleBin.exists_point_variance_bound (by omega : 2 ≤ d)
  let K : ℝ := D + (d : ℝ) + 2
  let B : ℝ := 2 * ξ * Q + 3 * ξ * K + 1
  let c : ℝ := 2 * (1004 * (d : ℝ)) ^ d
  let C : ℝ := 2 * c * Real.exp 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : 1 ≤ c := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hbase : 1 ≤ 1004 * (d : ℝ) := by nlinarith
    dsimp [c]
    have := one_le_pow₀ hbase (n := d)
    nlinarith
  refine ⟨B, 1, C, hB, by norm_num, ?_⟩
  intro Ω _ P _ h hh R hR ε hε
  have hε0 : 0 < ε := hε.1
  have hε1 : ε < 1 := hε.2.trans (by norm_num)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  by_cases hsmall : ε ≤ Real.exp (-1)
  · let J : ℤ := ScaleBin.topIndex (ε * R)
    let rN : ℕ → ℝ := fun n => (64 : ℝ) ^ (J - n)
    let badN : ℕ → Set Ω := fun n =>
      {ω | ∃ z : Rd d, ‖z‖ < 5 * R ∧
        (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z =
          fun i => rN n / (100 * d) * m i) ∧
        K * (1 + Real.log (R / rN n)) ≤
          |sphereAvg (h ω) (rN n) z - sphereAvg (h ω) (8 * R) 0|}
    have hJ : (64 : ℝ) ^ J ≤ ε * R :=
      ScaleBin.zpow_topIndex_le (mul_pos hε0 hR)
    have hrN : ∀ n, 0 < rN n := fun n =>
      zpow_pos (by norm_num : (0 : ℝ) < 64) _
    have hrNR : ∀ n, rN n ≤ R := by
      intro n
      have hnJ : J - (n : ℤ) ≤ J := by omega
      have hscale : rN n ≤ (64 : ℝ) ^ J :=
        zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 64) hnJ
      have hεR : ε * R ≤ R := by
        have := mul_le_mul_of_nonneg_right hε1.le hR.le
        nlinarith
      exact hscale.trans (hJ.trans hεR)
    have hsub : {ω | ∃ r ∈ scaleLattice, ε ^ 2 * R ≤ r ∧ r ≤ ε * R ∧
        ∃ z : Rd d, ‖z‖ < 5 * R ∧
          (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z =
            fun i => r / (100 * d) * m i) ∧
          ¬ (ε ^ B ≤ sNorm ξ Q (h ω) r z / macroS ξ Q (h ω) R ∧
              sNorm ξ Q (h ω) r z / macroS ξ Q (h ω) R ≤ ε ^ (-B))} ⊆
        ⋃ n, badN n := by
      intro ω hω
      obtain ⟨r, ⟨j, hj⟩, hrlo, hrhi, z, hz, hm, hbad⟩ := hω
      have hjUpper : (64 : ℝ) ^ j ≤ ε * R := by simpa only [← hj] using hrhi
      have hjJ : j ≤ J := ScaleBin.index_le_topIndex hjUpper
      obtain ⟨n, hn⟩ := ScaleBin.exists_nat_index hjJ
      have hre : r = rN n := by rw [hj, hn]
      have htail : K * (1 + Real.log (R / r)) ≤
          |sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0| := by
        by_contra hnot
        have hx : |sphereAvg (h ω) r z - sphereAvg (h ω) (8 * R) 0| <
            K * (1 + Real.log (R / r)) := lt_of_not_ge hnot
        exact hbad (by
          simpa only [B, K] using
            (ScaleBin.ratio_bounds_of_small_increment hξ hQ (le_trans (by norm_num) hD)
              hR hε0 hsmall
              hrlo hrhi (h ω) z hx))
      apply Set.mem_iUnion.mpr
      refine ⟨n, ?_⟩
      change ∃ z : Rd d, ‖z‖ < 5 * R ∧
        (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z =
          fun i => rN n / (100 * d) * m i) ∧
        K * (1 + Real.log (R / rN n)) ≤
          |sphereAvg (h ω) (rN n) z - sphereAvg (h ω) (8 * R) 0|
      rw [hre] at hm htail
      exact ⟨z, hz, hm, htail⟩
    have hpoint : ∀ n, P (badN n) ≤ ENNReal.ofReal (c * (rN n / R) ^ 4) := by
      intro n
      have hscale := ScaleBin.scale_point_bad_le (by omega : 2 ≤ d) hvar hh
        (hrN n) (hrNR n)
      have hcount := ScaleBin.grid_count_factor_le (by omega : 2 ≤ d) (hrN n) (hrNR n)
      calc
        P (badN n) ≤ ENNReal.ofReal (2 * (2 * (⌈500 * d * R / rN n⌉₊ : ℝ) + 1) ^ d *
            (rN n / R) ^ (2 * (d + 2))) := hscale
        _ ≤ ENNReal.ofReal (c * (rN n / R) ^ 4) := by
          apply ENNReal.ofReal_le_ofReal
          simpa only [c] using hcount
    have hsum : Summable fun n : ℕ => c * (rN n / R) ^ 4 := by
      exact (ScaleBin.summable_scale_four J R).mul_left c
    have hnonneg : ∀ n : ℕ, 0 ≤ c * (rN n / R) ^ 4 := fun _ => by positivity
    have hreal : (∑' n : ℕ, c * (rN n / R) ^ 4) ≤ c * (2 * ε ^ 4) := by
      rw [tsum_mul_left]
      exact mul_le_mul_of_nonneg_left (ScaleBin.sum_scale_four_le hε0 hR) hc0
    have hpow : ε ^ 4 ≤ ε := by
      calc
        ε ^ 4 = ε * ε ^ 3 := by ring
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ hε0.le hε1.le) hε0.le
        _ = ε := by ring
    have hcoef : c * (2 * ε ^ 4) ≤ C * ε := by
      have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      dsimp [C]
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hpow),
        mul_nonneg (mul_nonneg hc0 hε0.le) (sub_nonneg.mpr hexp)]
    calc
      P {ω | ∃ r ∈ scaleLattice, ε ^ 2 * R ≤ r ∧ r ≤ ε * R ∧
          ∃ z : Rd d, ‖z‖ < 5 * R ∧
            (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z = fun i => r / (100 * d) * m i) ∧
            ¬ (ε ^ B ≤ sNorm ξ Q (h ω) r z / macroS ξ Q (h ω) R ∧
                sNorm ξ Q (h ω) r z / macroS ξ Q (h ω) R ≤ ε ^ (-B))}
          ≤ P (⋃ n, badN n) := measure_mono hsub
      _ ≤ ∑' n, P (badN n) := measure_iUnion_le badN
      _ ≤ ∑' n, ENNReal.ofReal (c * (rN n / R) ^ 4) := ENNReal.tsum_le_tsum hpoint
      _ = ENNReal.ofReal (∑' n, c * (rN n / R) ^ 4) :=
        (ENNReal.ofReal_tsum_of_nonneg hnonneg hsum).symm
      _ ≤ ENNReal.ofReal (C * ε ^ (1 : ℝ)) := by
        rw [Real.rpow_one]
        exact ENNReal.ofReal_le_ofReal (hreal.trans hcoef)
  · have hlarge : Real.exp (-1) < ε := lt_of_not_ge hsmall
    have hbase : 1 < Real.exp 1 * ε := by
      calc
        (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by
          rw [← Real.exp_add]
          norm_num
        _ < Real.exp 1 * ε := mul_lt_mul_of_pos_left hlarge (Real.exp_pos 1)
    have hCε : 1 ≤ C * ε := by
      have hc2 : (1 : ℝ) ≤ 2 * c := by linarith
      calc
        (1 : ℝ) ≤ Real.exp 1 * ε := hbase.le
        _ = 1 * (Real.exp 1 * ε) := by ring
        _ ≤ (2 * c) * (Real.exp 1 * ε) :=
          mul_le_mul_of_nonneg_right hc2 (by linarith)
        _ = C * ε := by dsimp [C]; ring
    calc
      P {ω | ∃ r ∈ scaleLattice, ε ^ 2 * R ≤ r ∧ r ≤ ε * R ∧
          ∃ z : Rd d, ‖z‖ < 5 * R ∧
            (∃ m : Fin d → ℤ, EuclideanSpace.equiv (Fin d) ℝ z = fun i => r / (100 * d) * m i) ∧
            ¬ (ε ^ B ≤ sNorm ξ Q (h ω) r z / macroS ξ Q (h ω) R ∧
                sNorm ξ Q (h ω) r z / macroS ξ Q (h ω) R ≤ ε ^ (-B))}
          ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := IsProbabilityMeasure.measure_univ
      _ ≤ ENNReal.ofReal (C * ε ^ (1 : ℝ)) := by
        rw [Real.rpow_one]
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hCε

end HigherDimLQGMetric
