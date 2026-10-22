import HigherDimLQGMetric.Growth.LargeEventual
import LQGMetric.Papers.DFGPS.L2_3

/-!
# Lemma 2.14: sphere averages at large radius

Packet L2a. The dyadic Borel--Cantelli bound is converted to a uniform little-o estimate.
The analytic comparison follows the certified 2D proof of DFGPS Lemma 2.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistRd d}

/-- **Lemma 2.14.** For every positive `ζ`, the sphere-average supremum over a fixed
closed ball is little-o of `(log r)^(1/2+ζ)` as `r → ∞`. -/
theorem l2a_large_radius_littleO (hd : 2 ≤ d) (hh : IsNormalizedLGF h P)
    {R ζ : ℝ} (hR : 0 < R) (hζ : 0 < ζ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun r : ℝ => (⨆ z : closedBall (0 : Rd d) R, |sphereAvg (h ω) r z|) /
        Real.log r ^ (1 / 2 + ζ)) atTop (𝓝 0) := by
  obtain ⟨c, C, M, hc, hC, hM, hbound⟩ := l2a_ae_eventually_large_dyadic hd hh R
  have : Nonempty (closedBall (0 : Rd d) R) := ⟨⟨0, by simpa using hR.le⟩⟩
  filter_upwards [hbound] with ω hω
  obtain ⟨K, hK⟩ := eventually_atTop.1 hω
  set B : ℝ := Real.sqrt (24 * M) + Real.sqrt (4 / c) with hB
  have hT := (LQGMetric.DFGPS.tendsto_aux 0 B hζ).comp Real.tendsto_log_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with r hr
    exact div_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _)
      (Real.rpow_nonneg (Real.log_nonneg hr.le) _)
  filter_upwards [eventually_ge_atTop ((2 : ℝ) ^ (K + 2)), eventually_gt_atTop 1]
    with r hr hr1
  have hL0 : 0 < Real.log r := Real.log_pos hr1
  simp only [Function.comp, zero_add]
  refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg hL0.le _)
  refine ciSup_le fun z => ?_
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hr1.le (by norm_num : (1 : ℝ) < 2)
  set k := n + 1
  have hkK : K ≤ k := by
    by_contra hc'
    have hpow : (2 : ℝ) ^ k ≤ 2 ^ (K + 2) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hrlo : (2 : ℝ) ^ k / 2 ≤ r := by
    rw [pow_succ]
    nlinarith
  have hrhi : r ≤ (2 : ℝ) ^ k := hn2.le
  have hb := hK k hkK r hrlo hrhi z.1 z.2
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(k : ℕ).cast_nonneg (α := ℝ)]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hnL : (n : ℝ) * Real.log 2 ≤ Real.log r := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hn1
  have hL1 : Real.log 2 ≤ Real.log r := by
    have h2 : (2 : ℝ) ≤ r := le_trans (by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (K + 2) := pow_le_pow_right₀ (by norm_num) (by omega)) hr
    exact Real.log_le_log (by norm_num) h2
  have hkL : (k : ℝ) + 1 ≤ 6 * Real.log r := by
    have hn : (n : ℝ) ≤ 2 * Real.log r := by
      nlinarith [(n : ℕ).cast_nonneg (α := ℝ)]
    push_cast [k]
    linarith
  have hL : (1 / 2 : ℝ) ≤ Real.log r := hlog2.trans hL1
  set X : ℝ := Real.log r * Real.log (6 * Real.log r) with hXdef
  have hl6 : 0 ≤ Real.log (6 * Real.log r) := Real.log_nonneg (by linarith)
  have hX : 0 ≤ X := mul_nonneg hL0.le hl6
  have hlk0 : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg hk1
  have hlk : Real.log ((k : ℝ) + 1) ≤ Real.log (6 * Real.log r) :=
    Real.log_le_log (by linarith) hkL
  have hprod : ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1) ≤
      6 * Real.log r * Real.log (6 * Real.log r) :=
    mul_le_mul hkL hlk hlk0 (by linarith)
  have he1 : Real.sqrt (4 * M * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1)) ≤
      Real.sqrt (24 * M) * Real.sqrt X := by
    calc Real.sqrt (4 * M * ((k : ℝ) + 1) * Real.log ((k : ℝ) + 1))
        ≤ Real.sqrt ((24 * M) * X) := by
          apply Real.sqrt_le_sqrt
          dsimp [X]
          nlinarith [mul_nonneg (sub_nonneg.2 hprod) hM.le]
      _ = Real.sqrt (24 * M) * Real.sqrt X :=
        Real.sqrt_mul (by positivity : 0 ≤ 24 * M) X
  have hlkX : Real.log ((k : ℝ) + 1) ≤ 2 * X := by
    have h1 : Real.log (6 * Real.log r) ≤ 2 * X := by
      dsimp [X]
      nlinarith
    linarith
  have he2 : Real.sqrt ((2 / c) * Real.log ((k : ℝ) + 1)) ≤
      Real.sqrt (4 / c) * Real.sqrt X := by
    calc Real.sqrt ((2 / c) * Real.log ((k : ℝ) + 1))
        ≤ Real.sqrt ((4 / c) * X) := by
          apply Real.sqrt_le_sqrt
          calc (2 / c) * Real.log ((k : ℝ) + 1) ≤ (2 / c) * (2 * X) :=
                mul_le_mul_of_nonneg_left hlkX (by positivity : 0 ≤ 2 / c)
            _ = (4 / c) * X := by ring
      _ = Real.sqrt (4 / c) * Real.sqrt X :=
        Real.sqrt_mul (by positivity : 0 ≤ 4 / c) X
  dsimp [B]
  linarith only [hb, he1, he2]

end HigherDimLQGMetric
