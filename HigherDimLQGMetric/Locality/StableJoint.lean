import HigherDimLQGMetric.Limits.StableCond
import HigherDimLQGMetric.Field.Version
import HigherDimLQGMetric.DGZ.NondegJoint
import LQGMetric.Papers.DFGPS.L2_17CoreS

/-! Stable LFPP convergence gives convergence of the joint field–metric law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_stable_joint_law {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ))
    (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hstable : StablyTendstoLU P h X Y) :
    Tendsto (β := ProbabilityMeasure ((CoordJ → ℝ) × C(Rd d × Rd d, ℝ)))
      (fun n => (⟨P.map (fun ω => (pairJ ⊤ (h ω), X n ω)),
      (Measure.isProbabilityMeasure_map_iff
        (((measurable_pairJ ⊤).comp hh).prodMk (hX n)).aemeasurable).2 inferInstance⟩ :
        ProbabilityMeasure ((CoordJ → ℝ) × C(Rd d × Rd d, ℝ)))) atTop
      (𝓝 (⟨P.map (fun ω => (pairJ ⊤ (h ω), Y ω)),
        (Measure.isProbabilityMeasure_map_iff
          (((measurable_pairJ ⊤).comp hh).prodMk hY).aemeasurable).2 inferInstance⟩ :
        ProbabilityMeasure ((CoordJ → ℝ) × C(Rd d × Rd d, ℝ)))) := by
  let T := C(Rd d × Rd d, ℝ)
  letI : PseudoMetricSpace T := pseudoMetrizableSpacePseudoMetric T
  let H : Ω → CoordJ → ℝ := fun ω => pairJ ⊤ (h ω)
  have hH : Measurable H := (measurable_pairJ ⊤).comp hh
  let μn : ℕ → ProbabilityMeasure ((CoordJ → ℝ) × T) := fun n =>
    ⟨P.map (fun ω => (H ω, X n ω)),
      (Measure.isProbabilityMeasure_map_iff
        (hH.prodMk (hX n)).aemeasurable).2 inferInstance⟩
  let μ : ProbabilityMeasure ((CoordJ → ℝ) × T) :=
    ⟨P.map (fun ω => (H ω, Y ω)),
      (Measure.isProbabilityMeasure_map_iff
        (hH.prodMk hY).aemeasurable).2 inferInstance⟩
  change Tendsto μn atTop (𝓝 μ)
  let Sys : Set (Set ((CoordJ → ℝ) × T)) :=
    {w | ∃ U V, MeasurableSet U ∧ IsOpen V ∧
      P (Y ⁻¹' frontier V) = 0 ∧ w = U ×ˢ V}
  refine IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
    (S := Sys) ?_ ?_ ?_ ?_
  · rintro _ ⟨U, V, hU, hV, hfV, rfl⟩ _ ⟨U', V', hU', hV', hfV', rfl⟩ -
    refine ⟨U ∩ U', V ∩ V', hU.inter hU', hV.inter hV', ?_, prod_inter_prod⟩
    refine measure_mono_null
      (preimage_mono ((frontier_inter_subset V V').trans
        (union_subset_union inter_subset_left inter_subset_right))) ?_
    rw [preimage_union]
    exact measure_union_null hfV hfV'
  · rintro _ ⟨U, V, hU, hV, -, rfl⟩
    exact hU.prod hV.measurableSet
  · rintro u hu ⟨a, y⟩ hay
    obtain ⟨U, V, hU, hV, haU, hyV, hUV⟩ := isOpen_prod_iff.1 hu a y hay
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hV y hyV
    obtain ⟨r, ⟨hr0, hrρ⟩, hnull⟩ :=
      exists_null_frontier_thickening (P.map Y) {y} hρ
    rw [Measure.map_apply hY isClosed_frontier.measurableSet] at hnull
    rw [Metric.thickening_singleton] at hnull
    refine ⟨U ×ˢ Metric.ball y r,
      ⟨U, Metric.ball y r, hU.measurableSet, Metric.isOpen_ball,
        hnull, rfl⟩,
      prod_mem_nhds (hU.mem_nhds haU) (Metric.ball_mem_nhds y hr0), ?_⟩
    exact (prod_mono le_rfl ((Metric.ball_subset_ball hrρ.le).trans hball)).trans hUV
  · rintro _ ⟨U, V, hU, hV, hfV, rfl⟩
    let A : Set (DistRd d) := (pairJ ⊤) ⁻¹' U
    have hA : MeasurableSet A := (measurable_pairJ ⊤) hU
    have hUA : MeasurableSet (H ⁻¹' U) := hH hU
    have hVA : MeasurableSet V := hV.measurableSet
    have hrect : Tendsto
        (fun n => P (H ⁻¹' U ∩ X n ⁻¹' V)) atTop
        (𝓝 (P (H ⁻¹' U ∩ Y ⁻¹' V))) := by
      by_cases hzero : P (H ⁻¹' U) = 0
      · have hzX (n : ℕ) : P (H ⁻¹' U ∩ X n ⁻¹' V) = 0 :=
          measure_mono_null inter_subset_left hzero
        have hzY : P (H ⁻¹' U ∩ Y ⁻¹' V) = 0 :=
          measure_mono_null inter_subset_left hzero
        simp only [hzX, hzY]
        exact tendsto_const_nhds
      let PA := P[|H ⁻¹' U]
      letI : IsProbabilityMeasure PA := cond_isProbabilityMeasure hzero
      have hstableA : StablyTendstoLU PA h X Y :=
        l6c_stable_cond_field P h hh X Y hstable A hA hzero
      let νn : ℕ → ProbabilityMeasure T := fun n =>
        ⟨PA.map (X n), (Measure.isProbabilityMeasure_map_iff
          (hX n).aemeasurable).2 inferInstance⟩
      let ν : ProbabilityMeasure T :=
        ⟨PA.map Y, (Measure.isProbabilityMeasure_map_iff
          hY.aemeasurable).2 inferInstance⟩
      have hν : Tendsto νn atTop (𝓝 ν) :=
        l6c_stable_metric_law PA h X Y
          (fun n => (hX n).aemeasurable) hY.aemeasurable
          hstableA νn ν (fun _ => rfl) rfl
      have hVnull : (ν : Measure T) (frontier V) = 0 := by
        change (PA.map Y) (frontier V) = 0
        rw [Measure.map_apply hY isClosed_frontier.measurableSet]
        rw [ProbabilityTheory.cond_apply hUA]
        rw [measure_mono_null inter_subset_right hfV, mul_zero]
      have hVlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
        hν hVnull
      simp_rw [LQGMetric.DFGPS.L217.measure_inter_eq_mul_cond P hUA hzero
        (hX _) hVA,
        LQGMetric.DFGPS.L217.measure_inter_eq_mul_cond P hUA hzero hY hVA]
      exact ENNReal.Tendsto.const_mul hVlim (Or.inr (measure_ne_top _ _))
    change Tendsto (fun n => μn n (U ×ˢ V)) atTop (𝓝 (μ (U ×ˢ V)))
    have hmapn (n : ℕ) : ((μn n : ProbabilityMeasure ((CoordJ → ℝ) × T)) : Measure _)
        (U ×ˢ V) = P (H ⁻¹' U ∩ X n ⁻¹' V) := by
      change (P.map (fun ω => (H ω, X n ω))) (U ×ˢ V) = _
      exact LQGMetric.DFGPS.L217.map_pair_apply_prod P measurable_id hH
        (hX n) hU hVA
    have hmap : (μ : Measure _) (U ×ˢ V) = P (H ⁻¹' U ∩ Y ⁻¹' V) := by
      change (P.map (fun ω => (H ω, Y ω))) (U ×ˢ V) = _
      exact LQGMetric.DFGPS.L217.map_pair_apply_prod P measurable_id hH hY hU hVA
    have hrect' : Tendsto (fun n => (μn n : Measure _) (U ×ˢ V)) atTop
        (𝓝 ((μ : Measure _) (U ×ˢ V))) := by
      simpa only [hmapn, hmap] using hrect
    exact (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure _) (U ×ˢ V))).comp hrect'

end HigherDimLQGMetric
