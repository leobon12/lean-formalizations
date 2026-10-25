import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.SetGeoExistenceMeas




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory unitInterval
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes

theorem setGeodesic_scaled_candidate
    (D : LSCMetric) (K₁ K₂ : Set ℂ) (P : ℝ → ℂ) (T : ℝ)
    (hforget : Continuous (euclidForget D))
    (hSet : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T) :
    ∃ R : Measurability.GeodesicCodes.Path,
      Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, (R, (P 0, P T))) ∧
      ∀ t : unitInterval, R t = P (T * (t : ℝ)) := by
  have hT : 0 ≤ T := hSet.1.1.1
  have hcont : ContinuousOn P (Icc (0 : ℝ) T) := by
    have htmp := hforget.comp_continuousOn hSet.1.1.2
    change ContinuousOn P (Icc (0 : ℝ) T) at htmp
    exact htmp
  have hmaps : MapsTo (fun t : unitInterval => T * (t : ℝ)) univ (Icc 0 T) := by
    intro t _
    exact ⟨mul_nonneg hT t.2.1, mul_le_of_le_one_right hT t.2.2⟩
  have hRcont : Continuous (fun t : unitInterval => P (T * (t : ℝ))) :=
    hcont.comp_continuous (continuous_const.mul continuous_subtype_val)
      (fun t => hmaps trivial)
  let R : Measurability.GeodesicCodes.Path := ⟨fun t => P (T * (t : ℝ)), hRcont⟩
  have hlen : D.len P 0 T = ENNReal.ofReal T := by
    simpa only [LSCMetric.len, LQGMetric.MetricGeometry.curveLength, sub_zero] using
      (LQGMetric.MetricGeometry.curveLength_of_hasUnitSpeedOn hSet.1.2.1
        ⟨le_refl _, hT⟩ ⟨hT, le_refl _⟩)
  have hcost : D (P 0, P T) = ENNReal.ofReal T := by
    rw [← hSet.1.2.2.1]
    exact hlen
  have hgeo := EndSaving.FiniteEvents.SetGeodesic.isGeodesic D K₁ K₂ P T hSet
  have hcode : Measurability.GeodesicCodes.GeoCode (D, (R, (P 0, P T))) := by
    refine ⟨?_, ?_, hSet.1.2.2.2, ?_⟩
    · change P (T * 0) = P 0
      simp
    · change P (T * 1) = P T
      simp
    · intro s t hs hst ht
      have hsR : 0 ≤ (s : ℝ) := by exact_mod_cast hs
      have hstR : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
      have htR : (t : ℝ) ≤ 1 := by exact_mod_cast ht
      have hx : T * (s : ℝ) ∈ Icc 0 T :=
        ⟨mul_nonneg hT hsR, mul_le_of_le_one_right hT (hstR.trans htR)⟩
      have hy : T * (t : ℝ) ∈ Icc 0 T :=
        ⟨mul_nonneg hT (hsR.trans hstR), mul_le_of_le_one_right hT htR⟩
      have hxy : T * (s : ℝ) ≤ T * (t : ℝ) :=
        mul_le_mul_of_nonneg_left hstR hT
      have hmetric := hgeo.edist_eq_of_hasUnitSpeedOn
        hSet.1.2.1 hx hy hxy
      have hsI : (s : ℝ) ∈ Icc 0 1 := ⟨hsR, hstR.trans htR⟩
      have htI : (t : ℝ) ∈ Icc 0 1 := ⟨hsR.trans hstR, htR⟩
      change D (R (projIcc 0 1 zero_le_one (s : ℝ)),
        R (projIcc 0 1 zero_le_one (t : ℝ))) ≤
          ENNReal.ofReal ((t : ℝ) - s) * D (P 0, P T)
      rw [projIcc_of_mem zero_le_one hsI, projIcc_of_mem zero_le_one htI]
      change D (P (T * (s : ℝ)), P (T * (t : ℝ))) ≤ _
      rw [hcost]
      calc
        D (P (T * (s : ℝ)), P (T * (t : ℝ))) =
            ENNReal.ofReal (T * (t : ℝ) - T * (s : ℝ)) := hmetric
        _ = ENNReal.ofReal (((t : ℝ) - s) * T) := by congr 1; ring
        _ = ENNReal.ofReal ((t : ℝ) - s) * ENNReal.ofReal T := by
          rw [ENNReal.ofReal_mul (sub_nonneg.mpr hstR)]
        _ ≤ ENNReal.ofReal ((t : ℝ) - s) * ENNReal.ofReal T := le_rfl
  refine ⟨R, ?_, ?_⟩
  · exact ⟨hcode, hSet.2.1, hSet.2.2.1,
      hcost.trans hSet.2.2.2⟩
  · intro t
    rfl

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
