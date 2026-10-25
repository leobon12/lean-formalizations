import SupercriticalLQGUniqueness.B2.Median.Penalty

 





set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal
open LQGMetric (lfppLen)

namespace SupercriticalLQGUniqueness.B2.Median

def distanceRatio (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) : C(ℂ, ℝ) :=
  ⟨fun z => Metric.infDist z N / (ρ : ℝ),
    (Metric.continuous_infDist_pt N).div_const _⟩

def distanceBarrier (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) : C(ℂ, ℝ) :=
  ⟨fun z => min 1 (Metric.infDist z N / (ρ : ℝ)),
    continuous_const.min ((Metric.continuous_infDist_pt N).div_const _)⟩

def penaltyField (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) (M : ℝ) : C(ℂ, ℝ) :=
  M • distanceBarrier N ρ

theorem distanceRatio_eq_zero_of_mem {N : Set ℂ} {ρ : Set.Ioi (0 : ℝ)}
    {z : ℂ} (hz : z ∈ N) : distanceRatio N ρ z = 0 := by
  simp [distanceRatio, Metric.infDist_zero_of_mem hz]

theorem distanceRatio_half_one_sep (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ))
    {z w : ℂ} (hz : distanceRatio N ρ z = 1 / 2)
    (hw : distanceRatio N ρ w = 1) :
    (ρ : ℝ) / 2 ≤ dist z w := by
  have hρ : 0 < (ρ : ℝ) := ρ.property
  have hzi : Metric.infDist z N = (ρ : ℝ) / 2 := by
    have h := (div_eq_iff hρ.ne').mp hz
    linarith
  have hwi : Metric.infDist w N = (ρ : ℝ) := by
    have h := (div_eq_iff hρ.ne').mp hw
    linarith
  have hLip := Metric.infDist_le_infDist_add_dist (x := w) (y := z) (s := N)
  rw [dist_comm] at hLip
  linarith

theorem distanceRatio_half_mem_thickening (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ))
    {z : ℂ} (hz : distanceRatio N ρ z = 1 / 2) :
    Metric.infDist z N ≤ (ρ : ℝ) := by
  have hρ : 0 < (ρ : ℝ) := ρ.property
  have h := (div_eq_iff hρ.ne').mp hz
  linarith

theorem distanceRatio_one_mem_thickening (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ))
    {z : ℂ} (hz : distanceRatio N ρ z = 1) :
    Metric.infDist z N ≤ (ρ : ℝ) := by
  have hρ : 0 < (ρ : ℝ) := ρ.property
  have h := (div_eq_iff hρ.ne').mp hz
  linarith

theorem distanceBarrier_eq_zero_of_mem {N : Set ℂ} {ρ : Set.Ioi (0 : ℝ)}
    {z : ℂ} (hz : z ∈ N) : distanceBarrier N ρ z = 0 := by
  simp [distanceBarrier, Metric.infDist_zero_of_mem hz]

theorem distanceBarrier_nonneg (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) (z : ℂ) :
    0 ≤ distanceBarrier N ρ z := by
  change 0 ≤ min 1 (Metric.infDist z N / (ρ : ℝ))
  exact le_min zero_le_one (div_nonneg Metric.infDist_nonneg ρ.property.le)

theorem distanceBarrier_le_one (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) (z : ℂ) :
    distanceBarrier N ρ z ≤ 1 := min_le_left _ _

theorem distanceBarrier_ge_half_of_ratio (N : Set ℂ)
    (ρ : Set.Ioi (0 : ℝ)) {z : ℂ}
    (hz : 1 / 2 ≤ distanceRatio N ρ z) :
    1 / 2 ≤ distanceBarrier N ρ z := by
  change 1 / 2 ≤ min 1 (Metric.infDist z N / (ρ : ℝ))
  exact le_min (by norm_num) hz

theorem penaltyField_abs_le (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ))
    {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    |penaltyField N ρ M z| ≤ M := by
  change |M * distanceBarrier N ρ z| ≤ M
  have hlow : 0 ≤ M * distanceBarrier N ρ z :=
    mul_nonneg hM (distanceBarrier_nonneg N ρ z)
  rw [abs_of_nonneg hlow]
  nlinarith [distanceBarrier_le_one N ρ z]

theorem penaltyField_nonneg (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ))
    {M : ℝ} (hM : 0 ≤ M) (z : ℂ) :
    0 ≤ penaltyField N ρ M z :=
  mul_nonneg hM (distanceBarrier_nonneg N ρ z)

theorem penaltyField_ge_half (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ))
    {M : ℝ} (hM : 0 ≤ M) {z : ℂ}
    (hz : 1 / 2 ≤ distanceRatio N ρ z) :
    M / 2 ≤ penaltyField N ρ M z := by
  change M / 2 ≤ M * distanceBarrier N ρ z
  nlinarith [distanceBarrier_ge_half_of_ratio N ρ hz]

theorem distanceBarrier_half_one_sep (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ))
    {z w : ℂ}
    (hz : distanceBarrier N ρ z = 1 / 2)
    (hw : distanceBarrier N ρ w = 1) :
    (ρ : ℝ) / 2 ≤ dist z w := by
  have hzi : Metric.infDist z N / (ρ : ℝ) = 1 / 2 := by
    have hmin : min 1 (Metric.infDist z N / (ρ : ℝ)) = 1 / 2 := hz
    rcases le_total 1 (Metric.infDist z N / (ρ : ℝ)) with hle | hle
    · rw [min_eq_left hle] at hmin
      norm_num at hmin
    · rwa [min_eq_right hle] at hmin
  have hwi : 1 ≤ Metric.infDist w N / (ρ : ℝ) := by
    have hmin : min 1 (Metric.infDist w N / (ρ : ℝ)) = 1 := hw
    exact (min_eq_left_iff.mp hmin)
  have hLip := Metric.infDist_le_infDist_add_dist (x := w) (y := z) (s := N)
  rw [dist_comm] at hLip
  have hρ : 0 < (ρ : ℝ) := ρ.property
  have hzEq : Metric.infDist z N = (ρ : ℝ) / 2 := by
    apply (div_eq_iff hρ.ne').mp at hzi
    linarith
  have hwLo : (ρ : ℝ) ≤ Metric.infDist w N := by
    apply (le_div_iff₀ hρ).mp at hwi
    linarith
  linarith

 

theorem crossing_le_shifted_path_of_barrier {ξ δ : ℝ} (hξ : 0 ≤ ξ)
    (a : Set.Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ))
    (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) (μ : ℝ≥0∞)
    {P : ℝ → ℂ} {z w : ℂ}
    (hP : LQGMetric.IsPiecewiseC1Path P z w)
    (hzN : z ∈ N) (hz : z.re ≤ 0) (hw : 1 ≤ w.re)
    (hmetric : ∀ u v : ℂ,
      Metric.infDist u N ≤ (ρ : ℝ) →
      Metric.infDist v N ≤ (ρ : ℝ) →
      (ρ : ℝ) / 2 ≤ dist u v →
      μ ≤ lfppMetric ξ a φ (u, v))
    (hψ : ∀ u ∈ Icc (0 : ℝ) 1,
      1 / 2 ≤ distanceRatio N ρ (P u) →
      distanceRatio N ρ (P u) ≤ 1 → δ ≤ ψ (P u))
    (hψnonneg : ∀ u : ℂ, 0 ≤ ψ u)
    (hstrip : ∀ u ∈ Icc (0 : ℝ) 1,
      distanceRatio N ρ (P u) < 1 →
        0 ≤ (P u).im ∧ (P u).im ≤ 1)
    (hcost : ENNReal.ofReal ((a : ℝ)⁻¹) *
        lfppLen ξ (fun u => φ u + ψ u) P <
          ENNReal.ofReal (Real.exp (ξ * δ)) * μ) :
    ENNReal.ofReal ((a : ℝ)⁻¹) * lfppCrossingLength ξ φ ≤
      ENNReal.ofReal ((a : ℝ)⁻¹) *
        lfppLen ξ (fun u => φ u + ψ u) P := by
  have hstart : distanceRatio N ρ (P 0) ≤ 1 / 2 := by
    rw [hP.source, distanceRatio_eq_zero_of_mem hzN]
    norm_num
  have hpair : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      distanceRatio N ρ (P u) = 1 / 2 →
      distanceRatio N ρ (P v) = 1 →
        μ ≤ lfppMetric ξ a φ (P u, P v) := by
    intro u _ v _ hu hv
    exact hmetric (P u) (P v)
      (distanceRatio_half_mem_thickening N ρ hu)
      (distanceRatio_one_mem_thickening N ρ hv)
      (distanceRatio_half_one_sep N ρ hu hv)
  have hstay := path_avoids_barrier_of_pair_lower hξ a φ ψ
    (distanceRatio N ρ) hP hstart hψ hpair hcost
  exact crossing_le_shifted_strip_path hξ a φ ψ hP
    (fun u hu => hstrip u hu (hstay u hu)) hz hw hψnonneg

end SupercriticalLQGUniqueness.B2.Median
