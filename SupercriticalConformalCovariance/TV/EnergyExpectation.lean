import SupercriticalConformalCovariance.TV.SpatialMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric QuantumZipper ProbabilityTheory Filter
open scoped ENNReal

namespace SupercriticalConformalCovariance.TV

/-- The expected Dirichlet energy of the canonical harmonic cutoff is bounded
by the disk variance envelope, with a constant depending only on the observed ball. -/
theorem exists_lintegral_cutoff_energy_le
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        {h hH hZ G : Ω → DistC} (hh : IsWholePlaneGFF h P)
        (hGm : Measurable G) (hGeq : hH =ᵐ[P] G)
        (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ))
        {L : ℝ} (hL : 2 * R + 6 < L)
        (hBD : ball (0 : ℂ) L ⊆ D)
        (X : BddOn (D : Set ℂ) → Ω → ℝ)
        (hX : IsZBGFFProcessExt D X P)
        (hEq : ∀ φ : TestOn D, X φ.toBddOn =ᵐ[P]
          fun ω => restrictTo D (hZ ω) φ)
        (hind : IndepFun hH hZ P)
        (s : ℝ) (z : ℂ)
        (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω)
        (hharm : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
          InnerProductSpace.HarmonicOnNhd g (D : Set ℂ) ∧
          ∀ φ : TestOn D, restrictTo D (hH ω) φ = ∫ x, g x * φ x),
        let hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D :=
          (closedBall_subset_ball_zero_of_norm_add_lt (y := (0 : ℂ)) (by
            simp only [norm_zero, zero_add]; linarith)).trans hBD
        ∫⁻ ω, ENNReal.ofReal
          (dirichletEnergyOn D
            (canonicalShift R hR (1 / 4) (1 / 4) (by norm_num) (by norm_num)
              D hball (G ω)).1) ∂P ≤
          C * ENNReal.ofReal (diskVarianceEnvelope L (2 * R + 4)) := by
  obtain ⟨K, hK0, hK⟩ := exists_energy_bound_fixed_cutoff R hR
  let c : ℝ := expNegInvGlue ((1 / 2 : ℝ) ^ 2) / (∫ y, LQGMetric.GM.radProf (1 / 2) y)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (expNegInvGlue.nonneg _)
      (LQGMetric.GM.integral_radProf_pos (by norm_num)).le
  let q : ℝ := K * c ^ 2
  have hq : 0 ≤ q := mul_nonneg hK0 (sq_nonneg _)
  let V : ℝ≥0∞ := volume (closedBall (0 : ℂ) (2 * R + 4))
  have hV : V ≠ ⊤ := (isCompact_closedBall (0 : ℂ) (2 * R + 4)).measure_lt_top.ne
  refine ⟨ENNReal.ofReal q * V ^ 2, ?_, ?_⟩
  · rw [pow_two]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hV hV)
  intro Ω _ P _ h hH hZ G hh hGm hGeq D hDb L hL hBD X hX hEq hind s z hsum hharm
  dsimp only
  let hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D :=
    (closedBall_subset_ball_zero_of_norm_add_lt (y := (0 : ℂ)) (by
      simp only [norm_zero, zero_add]; linarith)).trans hBD
  let f := canonicalShift R hR (1 / 4) (1 / 4) (by norm_num) (by norm_num) D hball
  have hgood : ∀ᵐ ω ∂P,
      dirichletEnergyOn D (f (G ω)).1 ≤ q * (spatialIncrementIntegral R (G ω)) ^ 2 := by
    filter_upwards [hharm, hGeq] with ω ⟨g, hg, hpair⟩ heq
    have hpairG : ∀ φ : TestOn D,
        restrictTo D (G ω) φ = ∫ x, g x * φ x := by
      rw [← heq]
      exact hpair
    have hA : 0 ≤ spatialIncrementIntegral R (G ω) :=
      spatialIncrementIntegral_nonneg R (G ω)
    have hb : ∀ y ∈ closedBall (0 : ℂ) (2 * R + 3),
        |g y - g 0| ≤ c * spatialIncrementIntegral R (G ω) := by
      intro y hy
      exact harmonic_increment_le_spatial_integral R L hR (by linarith) D
        hBD hg (G ω) hpairG hy
    have henergy := hK (by linarith) hBD hg hpairG
      (mul_nonneg hc hA) hb
    change dirichletEnergyOn D (f (G ω)).1 ≤
      K * (c * spatialIncrementIntegral R (G ω)) ^ 2 at henergy
    calc
      _ ≤ K * (c * spatialIncrementIntegral R (G ω)) ^ 2 := henergy
      _ = q * (spatialIncrementIntegral R (G ω)) ^ 2 := by dsimp [q]; ring
  have hmoment := lintegral_sq_spatialIncrementIntegral_le hh hGm hGeq D hDb
    R L hR hL hBD X hX hEq hind s z hsum
  have hm : Measurable (fun ω =>
      ENNReal.ofReal ((spatialIncrementIntegral R (G ω)) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_spatialIncrementIntegral R).comp hGm).pow_const 2)
  calc
    ∫⁻ ω, ENNReal.ofReal (dirichletEnergyOn D (f (G ω)).1) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal q *
            ENNReal.ofReal ((spatialIncrementIntegral R (G ω)) ^ 2) ∂P := by
          apply lintegral_mono_ae
          filter_upwards [hgood] with ω he
          rw [← ENNReal.ofReal_mul hq]
          exact ENNReal.ofReal_le_ofReal he
    _ = ENNReal.ofReal q *
          (∫⁻ ω, ENNReal.ofReal ((spatialIncrementIntegral R (G ω)) ^ 2) ∂P) := by
          rw [lintegral_const_mul _ hm]
    _ ≤ ENNReal.ofReal q *
          (V ^ 2 * ENNReal.ofReal (diskVarianceEnvelope L (2 * R + 4))) := by
          exact mul_le_mul_of_nonneg_left hmoment bot_le
    _ = (ENNReal.ofReal q * V ^ 2) *
          ENNReal.ofReal (diskVarianceEnvelope L (2 * R + 4)) := by ring

end SupercriticalConformalCovariance.TV
