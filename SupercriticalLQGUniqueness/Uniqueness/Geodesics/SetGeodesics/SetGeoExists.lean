import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeodesicExists
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteEventsV2




 





set_option autoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics

 

theorem setDist_attained (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty) :
    ∃ u ∈ K₁, ∃ v ∈ K₂, OptimalConstants.Ratios.setDist D K₁ K₂ = D (u, v) := by
  let K : Set (ℂ × ℂ) := K₁ ×ˢ K₂
  have hK : IsCompact K := hK₁.prod hK₂
  have hne : K.Nonempty := by
    obtain ⟨u, hu⟩ := hne₁
    obtain ⟨v, hv⟩ := hne₂
    exact ⟨(u, v), hu, hv⟩
  obtain ⟨p, hp, hmin⟩ :=
    (D.lowerSemicontinuous.lowerSemicontinuousOn K).exists_isMinOn hne hK
  refine ⟨p.1, hp.1, p.2, hp.2, ?_⟩
  rw [OptimalConstants.Ratios.setDist_eq_iInf_prod]
  change (⨅ q : ℂ × ℂ, ⨅ _ : q ∈ K, D q) = D p
  calc
    (⨅ q : ℂ × ℂ, ⨅ _ : q ∈ K, D q) =
        ⨅ q : K, D (q : ℂ × ℂ) :=
      (iInf_subtype (f := fun q : K => D (q : ℂ × ℂ))).symm
    _ = D p := hmin.iInf_eq hp

 

theorem setDist_lt_top_of_pair (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (u v : ℂ) (hu : u ∈ K₁) (hv : v ∈ K₂)
    (hfin : D (u, v) < ⊤) :
    OptimalConstants.Ratios.setDist D K₁ K₂ < ⊤ :=
  (iInf₂_le_of_le u hu (iInf₂_le v hv)).trans_lt hfin

 

theorem exists_setGeodesic_of_finite (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hne₁ : K₁.Nonempty) (hne₂ : K₂.Nonempty)
    (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (hfin : OptimalConstants.Ratios.setDist D K₁ K₂ < ⊤) :
    ∃ P : ℝ → ℂ, ∃ T : ℝ, EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T := by
  obtain ⟨u, hu, v, hv, hmin⟩ := setDist_attained D K₁ K₂ hK₁ hK₂ hne₁ hne₂
  have huv : D (u, v) < ⊤ := by rw [← hmin]; exact hfin
  obtain ⟨P, hPcont, hPgeo, hPunit, hP0, hPT⟩ :=
    TwoScale.S36.exists_unit_geodesic D hB hL huv
  refine ⟨P, (D (u, v)).toReal, ?_⟩
  refine ⟨⟨⟨hPgeo.1, hPgeo.2.1⟩, hPunit, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact hPgeo.2.2
  · simpa only [hP0, hPT] using huv
  · simpa only [hP0] using hu
  · simpa only [hPT] using hv
  · rw [hmin]
    exact ENNReal.ofReal_toReal huv.ne

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.SetGeodesics
