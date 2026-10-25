import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.RationalAmplitude




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

theorem exists_null_shift_of_ae_null_amplitudes
    {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : Set X) (hE : LQGMetric.UMeasurableSet E)
    (F : Ω × ℝ → X) (hF : Measurable F)
    (hnull : ∀ᵐ ω ∂μ, volume
      {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ F (ω, a) ∈ E} = 0) :
    ∃ a ∈ Icc (0 : ℝ) 1, μ {ω | F (ω, a) ∈ E} = 0 := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let S : Set (Ω × ℝ) := F ⁻¹' E
  have hS : LQGMetric.UMeasurableSet S := hE.preimage hF
  have hSnull : NullMeasurableSet S (μ.prod ν) := hS.nullMeasurableSet _
  have hprod : μ.prod ν S = 0 := by
    rw [Measure.prod_apply₀ hSnull]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hnull] with ω hω
    change ν {a | F (ω, a) ∈ E} = 0
    rw [Measure.restrict_apply' measurableSet_Icc]
    have hset : {a : ℝ | F (ω, a) ∈ E} ∩ Icc (0 : ℝ) 1 =
        {a : ℝ | a ∈ Icc (0 : ℝ) 1 ∧ F (ω, a) ∈ E} := by
      ext a
      simp only [mem_inter_iff, mem_ofPred_eq]
      tauto
    rw [hset]
    exact hω
  have hSmap : NullMeasurableSet S (Measure.map Prod.swap (ν.prod μ)) := by
    rw [Measure.prod_swap]
    exact hSnull
  have hswapNull : (ν.prod μ) (Prod.swap ⁻¹' S) = 0 := by
    calc
      (ν.prod μ) (Prod.swap ⁻¹' S)
          = ((ν.prod μ).map Prod.swap) S :=
            (Measure.map_apply₀ measurable_swap.aemeasurable hSmap).symm
      _ = μ.prod ν S := by rw [Measure.prod_swap]
      _ = 0 := hprod
  have hsections : ∀ᵐ a ∂ν, ∀ᵐ ω ∂μ, F (ω, a) ∉ E := by
    have h := Measure.ae_ae_of_ae_prod
      (measure_eq_zero_iff_ae_notMem.mp hswapNull)
    simpa only [mem_preimage, Prod.swap_prod_mk, S] using h
  have hνne : ν ≠ 0 := by
    intro heq
    have huniv : ν Set.univ = 1 := by
      simp only [ν, Measure.restrict_apply_univ, Real.volume_Icc]
      norm_num
    rw [heq] at huniv
    simp at huniv
  have : (ae ν).NeBot := ae_neBot.2 hνne
  obtain ⟨a, ha⟩ := (hsections.and (ae_restrict_mem measurableSet_Icc)).exists
  refine ⟨a, ha.2, ?_⟩
  exact measure_eq_zero_iff_ae_notMem.mpr ha.1

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
