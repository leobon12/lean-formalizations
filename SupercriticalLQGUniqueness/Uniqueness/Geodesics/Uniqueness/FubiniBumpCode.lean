import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.FubiniUM




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

open LQGMetric (DistC)

theorem exists_amplitude_null_code
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : DistC → LSCMetric} (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (f : C(ℂ, ℝ)) (hf : ∀ z : ℂ, 0 ≤ f z ∧ f z ≤ 1)
    (K₁ K₂ U V : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hU : IsOpen U) (hV : IsOpen V)
    (hV₁ : Disjoint V K₁) (hV₂ : Disjoint V K₂)
    (hfU : ∀ z ∉ U, f z = 0) (hfV : ∀ z ∈ V, f z = 1) :
    ∃ a ∈ Icc (0 : ℝ) 1,
      μ {ω | Geodesics.SetGeodesics.BadSetGeoCode
        (D (LQGMetric.addFun (h ω) (a • f))) K₁ K₂ U V} = 0 := by
  let E : Set DistC := {g | Geodesics.SetGeodesics.BadSetGeoCode (D g) K₁ K₂ U V}
  have hE : LQGMetric.UMeasurableSet E :=
    Geodesics.SetGeodesics.badSetGeoCode_um D hD.1 K₁ K₂ U V hK₁ hK₂ hU hV
  let F : Ω × ℝ → DistC := fun p => LQGMetric.addFun (h p.1) (p.2 • f)
  have hF : Measurable F := by
    exact LQGMetric.measurable_addFun.comp
      ((hh.1.measurable.comp measurable_fst).prodMk
        (measurable_snd.smul_const f))
  have hnull : ∀ᵐ ω ∂μ, volume
      {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ F (ω, a) ∈ E} = 0 := by
    filter_upwards [EndSaving.Choices.ae_regularAt_self hD μ h hh] with ω hreg
    have hiff (a : ℝ) :
        Geodesics.SetGeodesics.BadSetGeoCode (D (LQGMetric.addFun (h ω) (a • f))) K₁ K₂ U V ↔
        Geodesics.SetGeodesics.BadSetGeodesic (D (LQGMetric.addFun (h ω) (a • f))) K₁ K₂ U V := by
      have hmetric : ∀ p : ℂ × ℂ,
          D (LQGMetric.addFun (h ω) (a • f)) p =
            weylScale (ξ : ℝ) (a • f) (D (h ω)) p :=
        fun p => (congrFun (hreg.weyl (a • f)) p).symm
      have hforget := Toolkit.WeylShift.continuous_forget_of_weyl (D (h ω))
        (D (LQGMetric.addFun (h ω) (a • f))) (ξ : ℝ) ξ.2.le
        (a • f) hreg.forget hmetric
      exact (Geodesics.SetGeodesics.badSetGeodesic_iff_code _ K₁ K₂ U V hforget).symm
    have hrawω : volume {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧
      Geodesics.SetGeodesics.BadSetGeodesic
        (D (LQGMetric.addFun (h ω) (a • f))) K₁ K₂ U V} = 0 := by
      
      have hsub := badSetGeodesic_amplitudes_subsingleton D (ξ : ℝ) ξ.2
        (h ω) hreg f hf K₁ K₂ U V hV hV₁ hV₂ hfU hfV
      have hsub' : {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧
        Geodesics.SetGeodesics.BadSetGeodesic
          (D (LQGMetric.addFun (h ω) (a • f))) K₁ K₂ U V}.Subsingleton := by
        intro a ha b hb
        exact hsub ⟨ha.1.1, ha.2⟩ ⟨hb.1.1, hb.2⟩
      exact hsub'.measure_zero volume
    have hset : {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ F (ω, a) ∈ E} =
        {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧
          Geodesics.SetGeodesics.BadSetGeodesic
            (D (LQGMetric.addFun (h ω) (a • f))) K₁ K₂ U V} := by
      ext a
      exact and_congr Iff.rfl (hiff a)
    rw [hset]
    exact hrawω
  simpa only [F, E, mem_ofPred_eq] using
    exists_null_shift_of_ae_null_amplitudes μ E hE F hF hnull

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
