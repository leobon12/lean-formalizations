import NV1Evidence
import LQGMetric.Field.CircleAvgBridge
import LQGMetric.Field.CircleAvgCont
import LQGMetric.Field.CircleAvgPairing
import LQGMetric.LFPP.WeylField

 






set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions

namespace SupercriticalLQGUniqueness

open LQGMetric (DistC IsWholePlaneGFF ofCont)

 
theorem isCircleAverage_unique {g : DistC} {r : Ioi (0 : ℝ)} {z : ℂ} {a b : ℝ}
    (ha : IsCircleAverage g r z a) (hb : IsCircleAverage g r z b) : a = b :=
  tendsto_nhds_unique ha hb

 

theorem circleApprox_eq_circBump (g : DistC) (n : ℕ) (r : Ioi (0 : ℝ)) (z : ℂ) :
    Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z (r : ℝ) =
      g (LQGMetric.CircleAvg.circBump n z (r : ℝ)) :=
  LQGMetric.CircleAvg.circleAverage_pairing g n z r

 

theorem isCircleAverage_iff_circBump (g : DistC) (r : Ioi (0 : ℝ))
    (z : ℂ) (a : ℝ) :
    IsCircleAverage g r z a ↔
      Tendsto (fun n : ℕ => g (LQGMetric.CircleAvg.circBump n z (r : ℝ)))
        atTop (𝓝 a) := by
  simp only [IsCircleAverage, circleApprox_eq_circBump]

 

theorem ae_exists_circleAverage {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (r : Ioi (0 : ℝ)) (z : ℂ) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, IsCircleAverage (h ω) r z a := by
  filter_upwards [ae_isCircleAverage_old hh r z] with ω hω
  exact ⟨LQGMetric.circleAvg (h ω) r z, hω⟩

 

theorem isCircleAverage_ofCont_iff (f : C(ℂ, ℝ)) (r : Ioi (0 : ℝ)) (z : ℂ)
    (a : ℝ) :
    IsCircleAverage (ofCont f) r z a ↔ a = Real.circleAverage f z (r : ℝ) := by
  constructor
  · intro ha
    exact isCircleAverage_unique ha
      (LQGMetric.CircleAvg.tendsto_mollAvg_ofCont f r z)
  · intro ha
    rw [ha]
    exact LQGMetric.CircleAvg.tendsto_mollAvg_ofCont f r z

 


theorem exists_circleAverage_process_bridge {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      LQGDimension.IsGFFCircleAverage H P ∧
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)) ∧
      ∀ r : Ioi (0 : ℝ), ∀ z : ℂ, ∀ a : Ω → ℝ,
        (∀ᵐ ω ∂P, IsCircleAverage (h ω) r z (a ω)) →
        (fun ω => H (r : ℝ) z ω) =ᵐ[P]
          (fun ω => a ω - LQGMetric.circleAvg (h ω) 1 0) := by
  obtain ⟨H, hH, hHc, hHae⟩ := LQGMetric.CircleAvg.exists_isGFFCircleAverage hh
  refine ⟨H, hH, hHc, ?_⟩
  intro r z a ha
  filter_upwards [ha, ae_isCircleAverage_old hh r z, hHae r r.2 z]
    with ω hω hold hversion
  rw [hversion, isCircleAverage_unique
    hold hω]

 

theorem exists_normalized_circleAverage_process_bridge {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ,
      LQGDimension.IsGFFCircleAverage H P ∧
      (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)) ∧
      ∀ r : Ioi (0 : ℝ), ∀ z : ℂ, ∀ a : Ω → ℝ,
        (∀ᵐ ω ∂P, IsCircleAverage (h ω) r z (a ω)) →
        (fun ω => H (r : ℝ) z ω) =ᵐ[P] a := by
  obtain ⟨H, hH, hHc, hHae⟩ :=
    LQGMetric.CircleAvg.exists_isGFFCircleAverage_normalized
      (isNormalizedWholePlaneGFF_iff_old.mp hh)
  refine ⟨H, hH, hHc, ?_⟩
  intro r z a ha
  filter_upwards [ha, ae_isCircleAverage_old hh.1 r z, hHae r r.2 z]
    with ω hω hold hversion
  rw [hversion]
  exact (isCircleAverage_unique hold hω)

 

theorem covariance_circleAverage_versions {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (r s : Ioi (0 : ℝ)) (z w : ℂ) (a b : Ω → ℝ)
    (ha : ∀ᵐ ω ∂P, IsCircleAverage (h ω) r z (a ω))
    (hb : ∀ᵐ ω ∂P, IsCircleAverage (h ω) s w (b ω)) :
    cov[a, b; P] = LQGDimension.gffCircleCov r z s w := by
  obtain ⟨H, hH, _, hHeq⟩ := exists_normalized_circleAverage_process_bridge hh
  calc
    cov[a, b; P] = cov[fun ω => H r z ω, fun ω => H s w ω; P] :=
      LQGMetric.CircleAvg.covariance_congr_ae (hHeq r z a ha).symm
        (hHeq s w b hb).symm
    _ = LQGDimension.gffCircleCov r z s w :=
      hH.covariance_eq r r.2 s s.2 z w

 

theorem ae_tendsto_positiveHeatTrunc {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
      atTop (𝓝 (LQGMetric.heatMollify ε (h ω) z)) := by
  simpa only [positiveHeatTrunc] using hh.ae_tendsto_heatMollify ε hε.ne' z

 

theorem ae_positiveHeatTrunc_unique {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (ε : ℝ) (hε : 0 < ε) (z : ℂ) (X : Ω → ℝ)
    (hX : ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => h ω (positiveHeatTrunc
        ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
      atTop (𝓝 (X ω))) :
    X =ᵐ[P] (fun ω => LQGMetric.heatMollify ε (h ω) z) := by
  filter_upwards [hX, ae_tendsto_positiveHeatTrunc hh ε hε z] with ω h1 h2
  exact tendsto_nhds_unique h1 h2

 

theorem tendsto_positiveHeatTrunc_ofCont (f : C(ℂ, ℝ)) (M : ℝ)
    (hM : ∀ w, |f w| ≤ M) (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    Tendsto (fun n : ℕ => ofCont f (positiveHeatTrunc
      ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
      atTop (𝓝 (∫ w, f w * LQGMetric.heatKernel (ε ^ 2 / 2) z w)) := by
  have ht := LQGMetric.LFPP.tendsto_heatMollify_ofCont f M hM hε.ne' z
  rw [LQGMetric.heatMollify_ofCont f M hM ε hε.ne' z] at ht
  simpa only [positiveHeatTrunc] using ht

 


theorem tendsto_positiveHeatTrunc_ofCont_of_integrable (f : C(ℂ, ℝ))
    (ε : ℝ) (hε : 0 < ε) (z : ℂ)
    (hf : Integrable (fun w => LQGMetric.heatKernel (ε ^ 2 / 2) z w * f w)) :
    Tendsto (fun n : ℕ => ofCont f (positiveHeatTrunc
      ⟨ε ^ 2 / 2, Set.mem_Ioi.mpr (div_pos (pow_pos hε 2) two_pos)⟩ z n))
      atTop (𝓝 (∫ w, f w * LQGMetric.heatKernel (ε ^ 2 / 2) z w)) := by
  have hs : 0 < ε ^ 2 / 2 := div_pos (pow_pos hε 2) two_pos
  have ht := LQGMetric.tendsto_ofCont_heatTrunc f (ε ^ 2 / 2) hs z hf
  simp_rw [mul_comm (LQGMetric.heatKernel (ε ^ 2 / 2) z _)] at ht
  simpa only [positiveHeatTrunc] using ht

end SupercriticalLQGUniqueness
