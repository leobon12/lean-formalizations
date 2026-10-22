import HigherDimLQGMetric.ConvField.Weight

/-! The radial pairing identity for one compactly supported radial test. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistRd d}

set_option maxHeartbeats 1000000 in
theorem l2b_ae_radial_pairing (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (φ : TestRd d) (z : Rd d)
    (hφ : ∀ x : Rd d, φ x = φ (z + ‖x - z‖ • e₁ d)) :
    ∀ᵐ ω ∂P,
      h ω φ = ((volume : Measure (Rd d)).toSphere univ).toReal *
        ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * φ (z + r • e₁ d) *
          sphereAvg (h ω) r z := by
  obtain ⟨A, hA, hrate'⟩ := l2b_exists_lintegral_enorm_sphereAvgSeq_sub_le hd
  let w : ℝ → ℝ := fun r => ((volume : Measure (Rd d)).toSphere univ).toReal *
    r ^ (d - 1) * φ (z + r • e₁ d)
  have hwc : Continuous w := l2b_continuous_radial_weight φ z
  have hK : (∫⁻ r in Ioi (0 : ℝ), ‖w r‖ₑ *
      ENNReal.ofReal (A / Real.sqrt r)) ≠ ⊤ :=
    l2b_lintegral_radial_weight_ne_top hd φ z hA
  have hrate (r : ℝ) (hr : 0 < r) (x : Rd d) (n : ℕ) :
      (∫⁻ ω, ‖sphereAvgSeq (h ω) r x n - sphereAvg (h ω) r x‖ₑ ∂P) ≤
        ENNReal.ofReal (A / Real.sqrt r) *
          ENNReal.ofReal (Real.sqrt (1 / 2 : ℝ)) ^ n *
            (1 - ENNReal.ofReal (Real.sqrt (1 / 2 : ℝ)))⁻¹ :=
    hrate' hh hr x n
  filter_upwards [l2b_ae_tendsto_integral_sphereAvgSeq_sub hd hh z w hwc A hrate hK]
    with ω ⟨hIdiff, hlimdiff⟩
  have hXc (n : ℕ) : Continuous (fun r : ℝ => sphereAvgSeq (h ω) r z n) :=
    l2b_continuous_sphereAvgSeq_radius (h ω) n z
  have hIX (n : ℕ) :
      (∫ r in Ioi (0 : ℝ), w r * sphereAvgSeq (h ω) r z n) =
        ((volume : Measure (Rd d)).toSphere univ).toReal *
          ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * φ (z + r • e₁ d) *
            sphereAvgSeq (h ω) r z n := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp [w]
    ring
  have hXlim : Tendsto (fun n => ∫ r in Ioi (0 : ℝ),
      w r * sphereAvgSeq (h ω) r z n) atTop (𝓝 (h ω φ)) := by
    convert l2b_tendsto_polar_sphBump hd (h ω) φ z hφ using 1
    funext n
    exact hIX n
  have hXI (n : ℕ) : Integrable (fun r : ℝ =>
      w r * sphereAvgSeq (h ω) r z n)
      (volume.restrict (Ioi (0 : ℝ))) :=
    l2b_integrable_radial_weight_mul hd φ z (hXc n)
  have hYI : Integrable (fun r : ℝ => w r * sphereAvg (h ω) r z)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have e : (fun r : ℝ => w r * sphereAvg (h ω) r z) =
        fun r => w r * sphereAvgSeq (h ω) r z 0 -
          w r * (sphereAvgSeq (h ω) r z 0 - sphereAvg (h ω) r z) := by
      funext r
      ring
    rw [e]
    exact (hXI 0).sub (hIdiff 0)
  have hdiff (n : ℕ) :
      (∫ r in Ioi (0 : ℝ), w r * sphereAvgSeq (h ω) r z n) -
        (∫ r in Ioi (0 : ℝ), w r * sphereAvg (h ω) r z) =
      ∫ r in Ioi (0 : ℝ), w r *
        (sphereAvgSeq (h ω) r z n - sphereAvg (h ω) r z) := by
    have e : (fun r : ℝ => w r * sphereAvg (h ω) r z) =
        fun r => w r * sphereAvgSeq (h ω) r z n -
          w r * (sphereAvgSeq (h ω) r z n - sphereAvg (h ω) r z) := by
      funext r
      ring
    rw [e, integral_sub (hXI n) (hIdiff n)]
    ring
  have hlim0 : Tendsto
      (fun n => (∫ r in Ioi (0 : ℝ), w r * sphereAvgSeq (h ω) r z n) -
        (∫ r in Ioi (0 : ℝ), w r * sphereAvg (h ω) r z)) atTop (𝓝 0) := by
    convert hlimdiff using 1
    funext n
    exact hdiff n
  have hlim1 : Tendsto
      (fun n => (∫ r in Ioi (0 : ℝ), w r * sphereAvgSeq (h ω) r z n) -
        (∫ r in Ioi (0 : ℝ), w r * sphereAvg (h ω) r z)) atTop
      (𝓝 (h ω φ - ∫ r in Ioi (0 : ℝ), w r * sphereAvg (h ω) r z)) :=
    hXlim.sub_const _
  have heq : h ω φ = ∫ r in Ioi (0 : ℝ), w r * sphereAvg (h ω) r z := by
    have := tendsto_nhds_unique hlim1 hlim0
    linarith
  rw [heq, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp [w]
  ring

end HigherDimLQGMetric
