import SupercriticalConformalCovariance.TV.SpatialOsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric QuantumZipper Filter ProbabilityTheory
open scoped ENNReal

namespace SupercriticalConformalCovariance.TV

/-- Spatial Cauchy–Schwarz followed by Tonelli gives a uniform second moment
for the integral of a random continuous field. -/
theorem lintegral_sq_spatial_abs_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Set ℂ) (hK : IsCompact K) (hKm : MeasurableSet K)
    (u : Ω → ℂ → ℝ)
    (hu : Measurable (fun p : Ω × ℂ => u p.1 p.2))
    (huc : ∀ ω, ContinuousOn (u ω) K)
    (b : ℝ) (hb : 0 ≤ b)
    (hui : ∀ y ∈ K, Integrable (fun ω => u ω y ^ 2) P)
    (hub : ∀ y ∈ K, ∫ ω, u ω y ^ 2 ∂P ≤ b) :
    ∫⁻ ω, ENNReal.ofReal ((∫ y in K, |u ω y|) ^ 2) ∂P ≤
      volume K * volume K * ENNReal.ofReal b := by
  let m := (volume K).toReal
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hmfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hJ (ω : Ω) : IntegrableOn (fun y => u ω y ^ 2) K :=
    (huc ω).pow 2 |>.integrableOn_compact hK
  have hJ0 (ω : Ω) : 0 ≤ ∫ y in K, u ω y ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hpoint (ω : Ω) :
      ENNReal.ofReal ((∫ y in K, |u ω y|) ^ 2) ≤
        ENNReal.ofReal m *
          ∫⁻ y in K, ENNReal.ofReal (u ω y ^ 2) := by
    have hcs := sq_setIntegral_abs_le_measure_mul_setIntegral_sq K hK hKm
      (u ω) (huc ω)
    have heq : ENNReal.ofReal (m * ∫ y in K, u ω y ^ 2) =
        ENNReal.ofReal m * ∫⁻ y in K, ENNReal.ofReal (u ω y ^ 2) := by
      rw [ENNReal.ofReal_mul hm, ofReal_integral_eq_lintegral_ofReal
        (hJ ω) (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact (ENNReal.ofReal_le_ofReal hcs).trans_eq heq
  have hjoint : Measurable (fun p : Ω × ℂ =>
      ENNReal.ofReal (u p.1 p.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hu.pow_const 2)
  have hinnerMeas : Measurable (fun ω =>
      ∫⁻ y in K, ENNReal.ofReal (u ω y ^ 2)) :=
    hjoint.lintegral_prod_right' (ν := (volume : Measure ℂ).restrict K)
  calc
    ∫⁻ ω, ENNReal.ofReal ((∫ y in K, |u ω y|) ^ 2) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal m *
            (∫⁻ y in K, ENNReal.ofReal (u ω y ^ 2)) ∂P :=
          lintegral_mono hpoint
    _ = ENNReal.ofReal m *
          (∫⁻ ω, ∫⁻ y in K, ENNReal.ofReal (u ω y ^ 2) ∂volume ∂P) := by
          rw [lintegral_const_mul _ hinnerMeas]
    _ = ENNReal.ofReal m *
          (∫⁻ y in K, ∫⁻ ω, ENNReal.ofReal (u ω y ^ 2) ∂P) := by
          rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ ≤ ENNReal.ofReal m * (∫⁻ _y in K, ENNReal.ofReal b) := by
          have hset : (∫⁻ y in K, ∫⁻ ω, ENNReal.ofReal (u ω y ^ 2) ∂P) ≤
              ∫⁻ _y in K, ENNReal.ofReal b := by
            refine setLIntegral_mono measurable_const (fun y hy => ?_)
            rw [← ofReal_integral_eq_lintegral_ofReal (hui y hy)
              (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (hub y hy)
          exact mul_le_mul_of_nonneg_left hset bot_le
    _ = volume K * volume K * ENNReal.ofReal b := by
          rw [setLIntegral_const]
          rw [ENNReal.ofReal_toReal hmfin]
          ring

/-- The square of the common spatial oscillation proxy has expectation controlled
by the disk variance envelope. -/
theorem lintegral_sq_spatialIncrementIntegral_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hH hZ G : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hGm : Measurable G) (hGeq : hH =ᵐ[P] G)
    (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ))
    (R L : ℝ) (hR : 0 < R) (hL : 2 * R + 6 < L)
    (hBD : ball (0 : ℂ) L ⊆ D)
    (X : BddOn (D : Set ℂ) → Ω → ℝ)
    (hX : IsZBGFFProcessExt D X P)
    (hEq : ∀ φ : TestOn D, X φ.toBddOn =ᵐ[P]
      fun ω => restrictTo D (hZ ω) φ)
    (hind : IndepFun hH hZ P)
    (s : ℝ) (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω) :
    ∫⁻ ω, ENNReal.ofReal ((spatialIncrementIntegral R (G ω)) ^ 2) ∂P ≤
      volume (closedBall (0 : ℂ) (2 * R + 4)) ^ 2 *
        ENNReal.ofReal (diskVarianceEnvelope L (2 * R + 4)) := by
  let K : Set ℂ := closedBall (0 : ℂ) (2 * R + 4)
  let u : Ω → ℂ → ℝ := fun ω y =>
    rawCenteredRepresentative (1 / 4) (by norm_num) (G ω) y
  have hu : Measurable (fun p : Ω × ℂ => u p.1 p.2) :=
    (measurable_rawCenteredRepresentative (1 / 4) (by norm_num)).comp
      ((hGm.comp measurable_fst).prodMk measurable_snd)
  have huc (ω : Ω) : ContinuousOn (u ω) K :=
    (continuous_rawCenteredRepresentative (1 / 4) (by norm_num) (G ω)).continuousOn
  have hL0 : 0 < L := by linarith
  have hSr : (2 * R + 4) + (1 / 4 : ℝ) < 2 * R + 5 := by linarith
  have hrL : 2 * R + 5 < L := by linarith
  have hui (y : ℂ) (hy : y ∈ K) :
      Integrable (fun ω => u ω y ^ 2) P := by
    have hyn : ‖y‖ ≤ 2 * R + 4 := by
      simpa [K, mem_closedBall, dist_zero_right] using hy
    have hmem := memLp_rawCenteredRepresentative hh hGeq D hL0
      (by norm_num : (0 : ℝ) < 1 / 4) hBD X hX hEq s z hsum
      (y := y) (by linarith) (by linarith)
    exact hmem.integrable_sq
  have hub (y : ℂ) (hy : y ∈ K) :
      ∫ ω, u ω y ^ 2 ∂P ≤ diskVarianceEnvelope L (2 * R + 4) := by
    have hyn : ‖y‖ ≤ 2 * R + 4 := by
      simpa [K, mem_closedBall, dist_zero_right] using hy
    exact integral_sq_radialRepresentative_sub_zero_le hh hGm hGeq D hDb
      hL0 (by linarith : 0 ≤ 2 * R + 5) hrL
      (by norm_num : (0 : ℝ) < 1 / 4) (by linarith : 0 ≤ 2 * R + 4)
      hSr hBD X hX hEq hind z hsum hyn
  have henv : 0 ≤ diskVarianceEnvelope L (2 * R + 4) := by
    have h0 : (0 : ℂ) ∈ K := mem_closedBall_self (by linarith)
    exact (integral_nonneg fun _ => sq_nonneg _).trans (hub 0 h0)
  have hmain := lintegral_sq_spatial_abs_le P K (isCompact_closedBall _ _)
    measurableSet_closedBall u hu huc
    (diskVarianceEnvelope L (2 * R + 4)) henv hui hub
  simpa only [K, u, spatialIncrementIntegral, pow_two] using hmain

end SupercriticalConformalCovariance.TV
