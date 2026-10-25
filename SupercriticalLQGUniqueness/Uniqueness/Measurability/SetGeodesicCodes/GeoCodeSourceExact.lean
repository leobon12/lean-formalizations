import SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes.GeoCodeExactSpeed




 
set_option autoImplicit false
noncomputable section
open Set unitInterval
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes

theorem setGeoCandidate_has_scaled_source
    (D : LSCMetric) (K₁ K₂ : Set ℂ) (R : Measurability.GeodesicCodes.Path) (u v : ℂ)
    (h : Measurability.ClauseEvents.SetGeoCandidate K₁ K₂ (D, (R, (u, v)))) :
    ∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T ∧
      ∀ q : unitInterval, P (T * (q : ℝ)) = R q := by
  rcases h with ⟨hcode, hu, hv, hsetdist⟩
  let L : ℝ≥0∞ := D (u, v)
  let T : ℝ := L.toReal
  let P : ℝ → D.Space :=
    fun t => D.pt (R (projIcc 0 1 zero_le_one (t / T)))
  have hfin : L ≠ ∞ := hcode.2.2.1.ne
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hL : ENNReal.ofReal T = L := ENNReal.ofReal_toReal hfin
  have hP0 : P 0 = u := by
    change R (projIcc 0 1 zero_le_one (0 / T)) = u
    rw [zero_div, projIcc_left]
    exact hcode.1
  have hPT : P T = v := by
    rcases hT0.eq_or_lt with hzero | hpos
    · have hLzero : L = 0 := by rw [← hL, ← hzero]; simp
      have huv : u = v := D.isExtMetric.2.1 u v hLzero
      rw [← hzero]
      exact hP0.trans huv
    · change R (projIcc 0 1 zero_le_one (T / T)) = v
      rw [div_self hpos.ne', projIcc_right]
      exact hcode.2.1
  have hdist : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      D (P s, P t) = ENNReal.ofReal |t - s| := by
    intro s hs t ht
    rcases hT0.eq_or_lt with hzero | hpos
    · have hs0 : s = 0 := le_antisymm (hzero ▸ hs.2) hs.1
      have ht0 : t = 0 := le_antisymm (hzero ▸ ht.2) ht.1
      subst hs0; subst ht0
      simpa using D.isExtMetric.1 (P 0)
    · have hsm : s / T ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hs.1 hT0, (div_le_one hpos).2 hs.2⟩
      have htm : t / T ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg ht.1 hT0, (div_le_one hpos).2 ht.2⟩
      rcases le_total s t with hst | hts
      · have horder : (projIcc 0 1 zero_le_one (s / T)) ≤
            (projIcc 0 1 zero_le_one (t / T)) := by
          rw [projIcc_of_mem _ hsm, projIcc_of_mem _ htm]
          exact div_le_div_of_nonneg_right hst hT0
        have hspped := geoCode_exact_speed D R u v hcode
          (projIcc 0 1 zero_le_one (s / T))
          (projIcc 0 1 zero_le_one (t / T)) horder
        calc
          D (P s, P t) = ENNReal.ofReal (t / T - s / T) * L := by
            simpa [P, L, LSCMetric.pt, projIcc_of_mem _ hsm,
              projIcc_of_mem _ htm]
              using hspped
          _ = ENNReal.ofReal |t - s| := by
            rw [← hL, ← ENNReal.ofReal_mul
              (sub_nonneg.mpr (div_le_div_of_nonneg_right hst hT0))]
            congr 1
            rw [abs_of_nonneg (sub_nonneg.mpr hst)]
            field_simp
      · have horder : (projIcc 0 1 zero_le_one (t / T)) ≤
            (projIcc 0 1 zero_le_one (s / T)) := by
          rw [projIcc_of_mem _ htm, projIcc_of_mem _ hsm]
          exact div_le_div_of_nonneg_right hts hT0
        have hspped := geoCode_exact_speed D R u v hcode
          (projIcc 0 1 zero_le_one (t / T))
          (projIcc 0 1 zero_le_one (s / T)) horder
        calc
          D (P s, P t) = D (P t, P s) :=
            D.isExtMetric.2.2.1 (P s) (P t)
          _ = ENNReal.ofReal (s / T - t / T) * L := by
            simpa [P, L, LSCMetric.pt, projIcc_of_mem _ hsm,
              projIcc_of_mem _ htm]
              using hspped
          _ = ENNReal.ofReal |t - s| := by
            rw [← hL, ← ENNReal.ofReal_mul
              (sub_nonneg.mpr (div_le_div_of_nonneg_right hts hT0))]
            congr 1
            rw [abs_of_nonpos (sub_nonpos.mpr hts)]
            field_simp
            ring
  have hmetric : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
      edist ((D.pt ∘ P) s) ((D.pt ∘ P) t) = edist s t := by
    intro s hs t ht
    change D (P s, P t) = edist s t
    rw [hdist s hs t ht, edist_dist, Real.dist_eq, abs_sub_comm]
  have hgeoUnit := LQGMetric.MetricGeometry.isGeodesicCurve_of_edist_eq
    hT0 hmetric
  have hSet : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T := by
    refine ⟨⟨⟨hT0, hgeoUnit.1.2.1⟩, hgeoUnit.2, ?_, ?_⟩, ?_, ?_, ?_⟩
    · exact hgeoUnit.1.2.2
    · rw [hP0, hPT]
      exact hcode.2.2.1
    · rw [hP0]
      exact hu
    · rw [hPT]
      exact hv
    · rw [hL]
      exact hsetdist
  refine ⟨P, T, hSet, ?_⟩
  intro q
  rcases hT0.eq_or_lt with hzero | hpos
  · have hLzero : L = 0 := by rw [← hL, ← hzero]; simp
    have hRzero : R q = u := by
      have hs := geoCode_exact_speed D R u v hcode (0 : unitInterval) q
        (by change (0 : ℝ) ≤ (q : ℝ); exact q.2.1)
      have hq : D (u, R q) = 0 := by
        simpa [L, hLzero, hcode.1] using hs
      exact (D.isExtMetric.2.1 u (R q) hq).symm
    rw [← hzero, zero_mul]
    exact hP0.trans hRzero.symm
  · change R (projIcc 0 1 zero_le_one ((T * (q : ℝ)) / T)) = R q
    rw [mul_div_cancel_left₀ _ hpos.ne']
    exact congrArg R (projIcc_of_mem zero_le_one q.2)

end SupercriticalLQGUniqueness.Uniqueness.Measurability.SetGeodesicCodes
