import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.BadScale




 

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC TestC)

theorem badSetGeoCode_null_of_shift_null
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (K₁ K₂ U V : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hU : IsOpen U) (hV : IsOpen V)
    (φ : TestC)
    (h0 : μ {ω | Geodesics.SetGeodesics.BadSetGeoCode
      (D (LQGMetric.addFun (h ω) (LQGMetric.testCont φ))) K₁ K₂ U V} = 0) :
    μ {ω | Geodesics.SetGeodesics.BadSetGeoCode (D (h ω)) K₁ K₂ U V} = 0 := by
  let g : Ω → DistC := fun ω => LQGMetric.addFun (h ω) (LQGMetric.testCont φ)
  let c : ℝ := Real.circleAverage (LQGMetric.testCont φ) 0 1
  let Y : Ω → DistC := fun ω => LQGMetric.addConst (g ω) (-c)
  have hgmeas : Measurable g :=
    (LQGMetric.measurable_addFun_left _).comp hh.1.measurable
  have hYmeas : Measurable Y := by
    refine LQGMetric.GFFInv.measurable_distC_iff.2 fun ψ => ?_
    simp only [Y, LQGMetric.GFFInv.addConst_apply]
    exact ((LQGMetric.GFFInv.measurable_pair ψ).comp hgmeas).add measurable_const
  let E : Set DistC := {x | Geodesics.SetGeodesics.BadSetGeoCode (D x) K₁ K₂ U V}
  have hE : LQGMetric.UMeasurableSet E :=
    Geodesics.SetGeodesics.badSetGeoCode_um D hD.1 K₁ K₂ U V hK₁ hK₂ hU hV
  have h0Y : μ (Y ⁻¹' E) = 0 := by
    have hreg := EndSaving.Choices.ae_regularAt_shift hD μ h hh φ
    have hiff : ∀ᵐ ω ∂μ,
        Geodesics.SetGeodesics.BadSetGeoCode (D (Y ω)) K₁ K₂ U V ↔
        Geodesics.SetGeodesics.BadSetGeoCode (D (g ω)) K₁ K₂ U V := by
      filter_upwards [hreg] with ω hr
      exact (badSetGeoCode_addConst_iff_regular D (ξ : ℝ) ξ.2.le
        (g ω) hr (-c) K₁ K₂ U V).symm
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hiff, measure_eq_zero_iff_ae_notMem.mp h0] with ω hω hnot
    exact fun hy => hnot (hω.mp hy)
  obtain ⟨R, hR, hfix⟩ := LQGMetric.GM.exists_sigma0_fix
    (LQGMetric.measurable_circleAvg_left 1 0)
  have hRX : ∀ᵐ ω ∂μ, R (h ω) = h ω := by
    filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero hh.1,
      hh.2] with ω h1 h2
    exact hfix _ h1 h2.limUnder_eq
  have hRY : ∀ᵐ ω ∂μ, R (Y ω) = Y ω := by
    filter_upwards [LQGMetric.GM.ae_circleAvg_addFun hh.1
      (LQGMetric.testCont φ), hh.2] with ω h1 h2
    have h2' : LQGMetric.circleAvg (h ω) 1 0 = 0 := h2.limUnder_eq
    refine hfix _ (fun d => ?_) ?_
    · simp only [Y, g, LQGMetric.GFFLaw.addConst_addConst]
      rw [h1 (-c + d), h1 (-c), h2']
      ring
    · change LQGMetric.circleAvg (LQGMetric.addConst (g ω) (-c)) 1 0 = 0
      rw [h1, h2']
      ring
  have hpairY : (fun ω => LQGMetric.pair0 (Y ω)) =
      fun ω => LQGMetric.pair0 (g ω) := by
    funext ω
    funext ψ
    change (LQGMetric.addConst (g ω) (-c)) ψ.1 = (g ω) ψ.1
    rw [LQGMetric.GFFInv.addConst_apply, ψ.2, zero_mul, add_zero]
  have hac : μ.map (fun ω => LQGMetric.pair0 (h ω)) ≪
      μ.map (fun ω => LQGMetric.pair0 (Y ω)) := by
    rw [hpairY]
    exact LQGMetric.lawPair0_ac_addFun hh.1 φ
  exact measure_preimage_eq_zero_of_sigma0_um μ hYmeas hh.1.measurable
    hR hac hRY hRX hE h0Y

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
