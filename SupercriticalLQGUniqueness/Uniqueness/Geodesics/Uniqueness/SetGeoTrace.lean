import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.AmplitudeSet




 





set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

 

theorem SetGeodesic.not_mem_start_of_pos
    (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (P : ℝ → ℂ) (T t : ℝ)
    (hP : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T)
    (ht : t ∈ Icc 0 T) (ht0 : 0 < t) : P t ∉ K₁ := by
  intro hK
  have hgeo := EndSaving.FiniteEvents.SetGeodesic.isGeodesic D K₁ K₂ P T hP
  have hunit := hP.1.2.1
  have hdist := hgeo.edist_eq_of_hasUnitSpeedOn hunit ht
    (right_mem_Icc.mpr hP.1.1.1) ht.2
  change D (P t, P T) = ENNReal.ofReal (T - t) at hdist
  have hset : ENNReal.ofReal T = OptimalConstants.Ratios.setDist D K₁ K₂ := hP.2.2.2
  have hmin : OptimalConstants.Ratios.setDist D K₁ K₂ ≤ D (P t, P T) :=
    iInf₂_le_of_le (P t) hK (iInf₂_le (P T) hP.2.2.1)
  have hstrict : ENNReal.ofReal (T - t) < ENNReal.ofReal T := by
    apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (sub_nonneg.mpr ht.2)).mpr
    linarith
  exact (not_lt_of_ge (hset ▸ hmin)) (hdist ▸ hstrict)

 

theorem SetGeodesic.not_mem_target_of_lt
    (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (P : ℝ → ℂ) (T t : ℝ)
    (hP : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T)
    (ht : t ∈ Icc 0 T) (htT : t < T) : P t ∉ K₂ := by
  intro hK
  have hgeo := EndSaving.FiniteEvents.SetGeodesic.isGeodesic D K₁ K₂ P T hP
  have hunit := hP.1.2.1
  have hdist := hgeo.edist_eq_of_hasUnitSpeedOn hunit
    (left_mem_Icc.mpr hP.1.1.1) ht ht.1
  change D (P 0, P t) = ENNReal.ofReal (t - 0) at hdist
  have hset : ENNReal.ofReal T = OptimalConstants.Ratios.setDist D K₁ K₂ := hP.2.2.2
  have hmin : OptimalConstants.Ratios.setDist D K₁ K₂ ≤ D (P 0, P t) :=
    iInf₂_le_of_le (P 0) hP.2.1 (iInf₂_le (P t) hK)
  have hstrict : ENNReal.ofReal t < ENNReal.ofReal T := by
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1).mpr htT
  have hdist' : D (P 0, P t) = ENNReal.ofReal t := by simpa only [sub_zero] using hdist
  exact (not_lt_of_ge (hset ▸ hmin)) (hdist' ▸ hstrict)

 

theorem SetGeodesic.eqOn_of_trace_subset
    (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (P Q : ℝ → ℂ) (T S : ℝ)
    (hP : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T)
    (hQ : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ Q S)
    (hsub : P '' Icc 0 T ⊆ Q '' Icc 0 S) :
    T = S ∧ Set.EqOn P Q (Icc 0 T) := by
  have hT0 : 0 ≤ T := hP.1.1.1
  have hS0 : 0 ≤ S := hQ.1.1.1
  have htime : T = S := by
    have heq : ENNReal.ofReal T = ENNReal.ofReal S :=
      hP.2.2.2.trans hQ.2.2.2.symm
    exact (ENNReal.ofReal_eq_ofReal_iff hT0 hS0).mp heq
  obtain ⟨s₀, hs₀, hstart⟩ := hsub ⟨0, left_mem_Icc.mpr hT0, rfl⟩
  have hs₀0 : s₀ = 0 := by
    by_contra hne
    have hpos : 0 < s₀ := lt_of_le_of_ne hs₀.1 (Ne.symm hne)
    have hmem : Q s₀ ∈ K₁ := by simpa only [hstart] using hP.2.1
    exact (SetGeodesic.not_mem_start_of_pos D K₁ K₂ Q S s₀ hQ hs₀ hpos) hmem
  have hP0Q0 : P 0 = Q 0 := by simpa only [hs₀0] using hstart.symm
  refine ⟨htime, ?_⟩
  intro t ht
  obtain ⟨s, hs, hpoint⟩ := hsub ⟨t, ht, rfl⟩
  have hPgeo := EndSaving.FiniteEvents.SetGeodesic.isGeodesic D K₁ K₂ P T hP
  have hQgeo := EndSaving.FiniteEvents.SetGeodesic.isGeodesic D K₁ K₂ Q S hQ
  have hPd := hPgeo.edist_eq_of_hasUnitSpeedOn hP.1.2.1
    (left_mem_Icc.mpr hT0) ht ht.1
  have hQd := hQgeo.edist_eq_of_hasUnitSpeedOn hQ.1.2.1
    (left_mem_Icc.mpr hS0) hs hs.1
  change D (P 0, P t) = ENNReal.ofReal (t - 0) at hPd
  change D (Q 0, Q s) = ENNReal.ofReal (s - 0) at hQd
  have hts : t = s := by
    have heq : ENNReal.ofReal t = ENNReal.ofReal s := by
      have hPd' : D (Q 0, Q s) = ENNReal.ofReal t := by
        simpa only [sub_zero, hP0Q0, hpoint] using hPd
      have hQd' : D (Q 0, Q s) = ENNReal.ofReal s := by
        simpa only [sub_zero] using hQd
      exact hPd'.symm.trans hQd'
    exact (ENNReal.ofReal_eq_ofReal_iff ht.1 hs.1).mp heq
  simpa only [hts] using hpoint.symm

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
