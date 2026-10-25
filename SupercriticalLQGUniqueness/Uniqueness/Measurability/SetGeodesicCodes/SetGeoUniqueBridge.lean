import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.GeoCodeSourceExact




 
set_option autoImplicit false
noncomputable section
open Set unitInterval MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes

private theorem time_eq_of_setGeodesics
    (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (P P' : ℝ → ℂ) (T T' : ℝ)
    (hP : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T)
    (hP' : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P' T') : T' = T := by
  apply (ENNReal.ofReal_eq_ofReal_iff hP'.1.1.1 hP.1.1.1).mp
  rw [hP'.2.2.2, hP.2.2.2]

private theorem scaled_time_mem (T : ℝ) (hT : 0 ≤ T) (q : unitInterval) :
    T * (q : ℝ) ∈ Icc 0 T :=
  ⟨mul_nonneg hT q.2.1, mul_le_of_le_one_right hT q.2.2⟩

private theorem eqOn_of_same_scaled_path
    (P P' : ℝ → ℂ) (T : ℝ) (hT : 0 ≤ T)
    (R : Measurability.GeodesicCodes.Path)
    (hP : ∀ q : unitInterval, P (T * (q : ℝ)) = R q)
    (hP' : ∀ q : unitInterval, P' (T * (q : ℝ)) = R q) :
    EqOn P' P (Icc 0 T) := by
  intro t ht
  rcases hT.eq_or_lt with hzero | hpos
  · have ht0 : t = 0 := le_antisymm (hzero ▸ ht.2) ht.1
    subst ht0
    have hq := hP (0 : unitInterval)
    have hq' := hP' (0 : unitInterval)
    simpa using hq'.trans hq.symm
  · let q : unitInterval := ⟨t / T,
      ⟨div_nonneg ht.1 hT, (div_le_one hpos).mpr ht.2⟩⟩
    have htime : T * (q : ℝ) = t := by
      change T * (t / T) = t
      field_simp
    rw [← htime]
    exact (hP' q).trans (hP q).symm

theorem uniqueSetGeodesic_iff_unique_candidate
    (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (hforget : Continuous (euclidForget D)) :
    (∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic D K₁ K₂ P T) ↔
    (∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, w)) := by
  constructor
  · rintro ⟨P, T, hUnique⟩
    obtain ⟨R, hR, hscaled⟩ :=
      setGeodesic_scaled_candidate D K₁ K₂ P T hforget hUnique.1
    refine ⟨(R, (P 0, P T)), hR, ?_⟩
    rintro ⟨R', ⟨u', v'⟩⟩ hR'
    obtain ⟨P', T', hP', hscaled'⟩ :=
      setGeoCandidate_has_scaled_source D K₁ K₂ R' u' v' hR'
    obtain ⟨hT', hEq⟩ := hUnique.2 P' T' hP'
    have hRR : R' = R := by
      ext q
      calc
        R' q = P' (T' * (q : ℝ)) := (hscaled' q).symm
        _ = P' (T * (q : ℝ)) := by rw [hT']
        _ = P (T * (q : ℝ)) := hEq (scaled_time_mem T hUnique.1.1.1.1 q)
        _ = R q := (hscaled q).symm
    have hu' : u' = P 0 := by
      calc
        u' = R' 0 := hR'.1.1.symm
        _ = R 0 := by rw [hRR]
        _ = P 0 := by simpa using hscaled (0 : unitInterval)
    have hv' : v' = P T := by
      calc
        v' = R' 1 := hR'.1.2.1.symm
        _ = R 1 := by rw [hRR]
        _ = P T := by simpa using hscaled (1 : unitInterval)
    exact Prod.ext hRR (Prod.ext hu' hv')
  · rintro ⟨⟨R, ⟨u, v⟩⟩, hR, hUnique⟩
    obtain ⟨P, T, hP, hscaled⟩ :=
      setGeoCandidate_has_scaled_source D K₁ K₂ R u v hR
    refine ⟨P, T, hP, ?_⟩
    intro P' T' hP'
    obtain ⟨R', hR', hscaled'⟩ :=
      setGeodesic_scaled_candidate D K₁ K₂ P' T' hforget hP'
    have hW : (R', (P' 0, P' T')) = (R, (u, v)) :=
      hUnique (R', (P' 0, P' T')) hR'
    have hRR : R' = R := congrArg Prod.fst hW
    have hT : T' = T := time_eq_of_setGeodesics D K₁ K₂ P P' T T' hP hP'
    refine ⟨hT, ?_⟩
    have hscaled'' : ∀ q : unitInterval, P' (T * (q : ℝ)) = R q := by
      intro q
      calc
        P' (T * (q : ℝ)) = P' (T' * (q : ℝ)) := by rw [hT]
        _ = R' q := (hscaled' q).symm
        _ = R q := by rw [hRR]
    exact eqOn_of_same_scaled_path P P' T hP.1.1.1 R hscaled hscaled''

 

theorem ae_original_and_all_test_shift_uniqueSetGeodesic_iff_code
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    {D : LQGMetric.DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Qpar D)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h μ) :
    ∀ᵐ ω ∂μ,
      (∀ K₁ K₂ : Set ℂ,
        (∃ P : ℝ → ℂ, ∃ T : ℝ,
          EndSaving.FiniteEvents.UniqueSetGeodesic (D (h ω)) K₁ K₂ P T) ↔
        (∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
          Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D (h ω), w))) ∧
      (∀ φ : LQGMetric.TestC, ∀ K₁ K₂ : Set ℂ,
        (∃ P : ℝ → ℂ, ∃ T : ℝ,
          EndSaving.FiniteEvents.UniqueSetGeodesic
            (D (LQGMetric.GM.subTest (h ω) φ)) K₁ K₂ P T) ↔
        (∃! w : Measurability.GeodesicCodes.Path × (ℂ × ℂ),
          Measurability.ClauseEvents.SetGeoCandidate K₁ K₂
            (D (LQGMetric.GM.subTest (h ω) φ), w))) := by
  filter_upwards [Toolkit.WeylShift.ae_common_weyl_sample hD μ h hh,
    Toolkit.WeylShift.ae_all_shift_curves hD μ h hh] with ω hbase hshift
  constructor
  · intro K₁ K₂
    exact uniqueSetGeodesic_iff_unique_candidate
      (D (h ω)) K₁ K₂ hbase.1
  · intro φ K₁ K₂
    have hcont := (hshift (-LQGMetric.testCont φ)).1
    change Continuous (euclidForget
      (D (LQGMetric.GM.subTest (h ω) φ))) at hcont
    exact uniqueSetGeodesic_iff_unique_candidate
      (D (LQGMetric.GM.subTest (h ω) φ)) K₁ K₂ hcont

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
