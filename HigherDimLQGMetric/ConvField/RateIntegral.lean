import HigherDimLQGMetric.ConvField.Rate

/-! Integrating the sphere-average error against a radial weight. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistRd d}

set_option maxHeartbeats 1000000 in
theorem l2b_ae_tendsto_integral_sphereAvgSeq_sub (_hd : 2 ≤ d)
    (hh : IsWholeSpaceLGF h P) (z : Rd d) (w : ℝ → ℝ) (hwc : Continuous w)
    (A : ℝ)
    (hrate : ∀ (r : ℝ), 0 < r → ∀ (z : Rd d) (n : ℕ),
      (∫⁻ ω, ‖sphereAvgSeq (h ω) r z n - sphereAvg (h ω) r z‖ₑ ∂P) ≤
        ENNReal.ofReal (A / Real.sqrt r) *
          ENNReal.ofReal (Real.sqrt (1 / 2 : ℝ)) ^ n *
            (1 - ENNReal.ofReal (Real.sqrt (1 / 2 : ℝ)))⁻¹)
    (hK : ∫⁻ r in Ioi (0 : ℝ), ‖w r‖ₑ *
      ENNReal.ofReal (A / Real.sqrt r) ≠ ⊤) :
    ∀ᵐ ω ∂P,
      (∀ n : ℕ, Integrable (fun r =>
        w r * (sphereAvgSeq (h ω) r z n - sphereAvg (h ω) r z))
          (volume.restrict (Ioi (0 : ℝ)))) ∧
      Tendsto (fun n : ℕ => ∫ r in Ioi (0 : ℝ),
        w r * (sphereAvgSeq (h ω) r z n - sphereAvg (h ω) r z))
          atTop (𝓝 0) := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let t : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt (1 / 2 : ℝ))
  have ht1 : t < 1 := by
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
    rw [Real.sqrt_lt' one_pos]
    norm_num
  have hinv : (1 - t)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt ht1).ne'
  let X : ℕ → ℝ → Ω → ℝ := fun n r ω => sphereAvgSeq (h ω) r z n
  let F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    ‖w p.2 * (X n p.2 p.1 - sphereAvg (h p.1) p.2 z)‖ₑ
  have hXm : ∀ n, Measurable (fun p : Ω × ℝ => X n p.2 p.1) := by
    intro n
    exact (measurable_sphereAvgSeq n).comp
      ((hh.measurable.comp measurable_fst).prodMk
        (measurable_snd.prodMk measurable_const))
  have hYm : Measurable (fun p : Ω × ℝ => sphereAvg (h p.1) p.2 z) := by
    exact measurable_sphereAvg.comp
      ((hh.measurable.comp measurable_fst).prodMk
        (measurable_snd.prodMk measurable_const))
  have hFm : ∀ n, AEMeasurable (F n) (P.prod ν) := by
    intro n
    exact (((hwc.measurable.comp measurable_snd).mul ((hXm n).sub hYm)).enorm).aemeasurable
  let Δ : ℕ → Ω → ℝ≥0∞ := fun n ω => ∫⁻ r, F n (ω, r) ∂ν
  have hΔm : ∀ n, AEMeasurable (Δ n) P := fun n => (hFm n).lintegral_prod_right'
  let K : ℝ≥0∞ := ∫⁻ r, ‖w r‖ₑ * ENNReal.ofReal (A / Real.sqrt r) ∂ν
  have hK' : K ≠ ⊤ := by
    change (∫⁻ r in Ioi (0 : ℝ), ‖w r‖ₑ *
      ENNReal.ofReal (A / Real.sqrt r) ∂volume) ≠ ⊤
    exact hK
  have hEΔ : ∀ n, ∫⁻ ω, Δ n ω ∂P ≤ K * (t ^ n * (1 - t)⁻¹) := by
    intro n
    calc
      ∫⁻ ω, Δ n ω ∂P = ∫⁻ r, ∫⁻ ω, F n (ω, r) ∂P ∂ν :=
        lintegral_lintegral_swap (f := fun ω r => F n (ω, r)) (hFm n)
      _ ≤ ∫⁻ r, ‖w r‖ₑ * ENNReal.ofReal (A / Real.sqrt r) *
          (t ^ n * (1 - t)⁻¹) ∂ν := by
        refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
        have hr0 : 0 < r := hr
        simp only [F, enorm_mul]
        rw [lintegral_const_mul' _ _ enorm_ne_top, mul_assoc,
          ← mul_assoc (ENNReal.ofReal _)]
        gcongr
        exact hrate r hr0 z n
      _ = K * (t ^ n * (1 - t)⁻¹) :=
        lintegral_mul_const' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top
          (ne_top_of_lt ht1)) hinv)
  have hsum : ∫⁻ ω, ∑' n, Δ n ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum hΔm]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hEΔ)
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top hK' (ENNReal.mul_ne_top hinv hinv)
  filter_upwards [ae_lt_top' (AEMeasurable.tsum hΔm) hsum] with ω hω
  have hΔ0 : Tendsto (fun n => Δ n ω) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have hΔf : ∀ n, Δ n ω < ⊤ := fun n => (ENNReal.le_tsum n).trans_lt hω
  have hYm' : Measurable (Function.uncurry
      (fun (ω : Ω) (r : ℝ) => sphereAvg (h ω) r z)) := hYm
  have hYmeas : Measurable (fun r : ℝ => sphereAvg (h ω) r z) :=
    hYm'.of_uncurry_left (x := ω)
  have hsection : Measurable (fun r : ℝ => ((ω, r) : Ω × ℝ)) :=
    measurable_prodMk_left
  have hI : ∀ n, Integrable (fun r =>
      w r * (X n r ω - sphereAvg (h ω) r z)) ν := by
    intro n
    have hXmeas : Measurable (fun r : ℝ => X n r ω) := (hXm n).comp hsection
    refine ⟨(hwc.measurable.mul (hXmeas.sub hYmeas)).aestronglyMeasurable, ?_⟩
    exact hΔf n
  refine ⟨hI, tendsto_iff_edist_tendsto_0.2
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hΔ0
      (fun n => zero_le) fun n => ?_)⟩
  rw [edist_eq_enorm_sub, sub_zero]
  exact enorm_integral_le_lintegral_enorm _

end HigherDimLQGMetric
