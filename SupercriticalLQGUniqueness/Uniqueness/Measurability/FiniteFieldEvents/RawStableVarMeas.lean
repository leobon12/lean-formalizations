import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.StableCodeVar




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
open LQGMetric (DistC TestC)

theorem rawUniqueStable_var_shifted_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (W : Set ℂ) (hW : IsOpen W) (hWc : IsCompact (closure W))
    (hWne : Wᶜ.Nonempty)
    (V : TopologicalSpace.Opens ℂ) (hVW : closure (V : Set ℂ) ⊆ W)
    (L : DistC → ℝ≥0∞) (hL : Measurable L) (φ : TestC) :
    NullMeasurableSet
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
        SourceStable (D g) P' T W V (L g)}
      (P.map h) := by
  let Db : DistC → LSCMetric := fun g => D (LQGMetric.GM.subTest g φ)
  have hshift : Measurable (fun g : DistC => LQGMetric.GM.subTest g φ) := by
    change Measurable (fun g : DistC =>
      LQGMetric.addFun g (-LQGMetric.testCont φ))
    exact LQGMetric.measurable_addFun_left _
  have hDb : Measurable Db := hD.1.comp hshift
  have hCode : LQGMetric.UMeasurableSet
      {g : DistC | UniqueStableCodeFieldVar Db D K₁ K₂ W V L g} :=
    uniqueStableCodeFieldVar_um Db D hDb hD.1 K₁ K₂ hK₁ hK₂ W hW hWc V L hL
  have hcanonical : IsNormalizedWholePlaneGFF
      (id : DistC → DistC) (P.map h) := Measurability.SetGeodesicCodes.normalizedGFF_id_map P h hh
  have hae :
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (LQGMetric.GM.subTest g φ)) K₁ K₂ P' T ∧
        SourceStable (D g) P' T W V (L g)} =ᵐ[P.map h]
      {g : DistC | UniqueStableCodeFieldVar Db D K₁ K₂ W V L g} := by
    filter_upwards [Toolkit.WeylShift.ae_common_weyl_sample hD (P.map h) id hcanonical,
      Toolkit.WeylShift.ae_all_shift_curves hD (P.map h) id hcanonical]
      with g hg0 hgShift
    have hforgetb := (hgShift (-LQGMetric.testCont φ)).1
    change Continuous (Measurability.SetGeodesicCodes.euclidForget (Db g)) at hforgetb
    have hforgeta : Continuous (Measurability.SetGeodesicCodes.euclidForget (D g)) := hg0.1
    exact propext (uniqueStableSource_iff_code (Db g) (D g)
      hforgetb hforgeta K₁ K₂ W hW hWne V hVW (L g))
  exact (hCode.nullMeasurableSet (P.map h)).congr hae.symm

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
