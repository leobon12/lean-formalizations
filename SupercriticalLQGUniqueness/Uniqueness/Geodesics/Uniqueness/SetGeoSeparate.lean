import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.RationalBall




 

set_option autoImplicit false
noncomputable section
open Set
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

theorem SetGeodesic.exists_interior_point_off_trace
    (D : LSCMetric) (K₁ K₂ : Set ℂ) (hK : Disjoint K₁ K₂)
    (P Q : ℝ → ℂ) (T S : ℝ)
    (hP : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T)
    (hQ : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ Q S)
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hdiff : ¬ Set.EqOn P Q (Icc 0 T)) :
    ∃ u ∈ Ioo 0 S, Q u ∉ P '' Icc 0 T := by
  have hSpos : 0 < S := by
    have hS0 := hQ.1.1.1
    rcases hS0.eq_or_lt with hzero | hpos
    · have hsame : Q 0 = Q S := by rw [← hzero]
      exact False.elim ((Set.disjoint_left.mp hK hQ.2.1) (hsame ▸ hQ.2.2.1))
    · exact hpos
  have hcontP : ContinuousOn P (Icc 0 T) := by
    have hc := hforget.comp_continuousOn hP.1.1.2
    change ContinuousOn P (Icc 0 T) at hc
    exact hc
  have hcontQ : ContinuousOn Q (Icc 0 S) := by
    have hc := hforget.comp_continuousOn hQ.1.1.2
    change ContinuousOn Q (Icc 0 S) at hc
    exact hc
  have hF : IsClosed (P '' Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn hcontP).isClosed
  by_contra hn
  push Not at hn
  have hinside : Q '' Ioo 0 S ⊆ P '' Icc 0 T := by
    rintro z ⟨u, hu, rfl⟩
    exact hn u hu
  have hclosure : Q '' Icc 0 S ⊆ closure (Q '' Ioo 0 S) := by
    rw [← closure_Ioo hSpos.ne] at hcontQ ⊢
    exact hcontQ.image_closure
  have hsub : Q '' Icc 0 S ⊆ P '' Icc 0 T :=
    hclosure.trans (closure_minimal hinside hF)
  have heq := SetGeodesic.eqOn_of_trace_subset D K₁ K₂ Q P S T hQ hP hsub
  exact hdiff (by
    intro t ht
    exact (heq.2 (by simpa only [heq.1] using ht)).symm)

 

theorem SetGeodesic.exists_rational_bad_bump
    (D : LSCMetric) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hK : Disjoint K₁ K₂)
    (P Q : ℝ → ℂ) (T S : ℝ)
    (hP : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ P T)
    (hQ : EndSaving.FiniteEvents.SetGeodesic D K₁ K₂ Q S)
    (hforget : Continuous (BiLipschitz.Barrier.forget D))
    (hdiff : ¬ Set.EqOn P Q (Icc 0 T)) :
    ∃ a b ρ : ℚ, (0 : ℝ) < ρ ∧
      Geodesics.SetGeodesics.BadSetGeodesic D K₁ K₂
        (Metric.ball (⟨a, b⟩ : ℂ) (3 * (ρ : ℝ)))
        (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) ∧
      Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₁ ∧
      Disjoint (Metric.ball (⟨a, b⟩ : ℂ) (2 * (ρ : ℝ))) K₂ := by
  obtain ⟨u, hu, houtside⟩ :=
    SetGeodesic.exists_interior_point_off_trace D K₁ K₂ hK
      P Q T S hP hQ hforget hdiff
  have hucc : u ∈ Icc 0 S := Ioo_subset_Icc_self hu
  have huK₁ : Q u ∉ K₁ :=
    SetGeodesic.not_mem_start_of_pos D K₁ K₂ Q S u hQ hucc hu.1
  have huK₂ : Q u ∉ K₂ :=
    SetGeodesic.not_mem_target_of_lt D K₁ K₂ Q S u hQ hucc hu.2
  have hcontP : ContinuousOn P (Icc 0 T) := by
    have hc := hforget.comp_continuousOn hP.1.1.2
    change ContinuousOn P (Icc 0 T) at hc
    exact hc
  let F : Set ℂ := (P '' Icc 0 T) ∪ K₁ ∪ K₂
  have hF : IsClosed F :=
    ((isCompact_Icc.image_of_continuousOn hcontP).isClosed.union hK₁.isClosed).union hK₂.isClosed
  have hout : Q u ∉ F := by
    simp only [F, mem_union]
    tauto
  obtain ⟨a, b, ρ, hρ, hnear, hfar⟩ :=
    exists_rat_ball_avoiding_closed F hF (Q u) hout
  let q : ℂ := ⟨a, b⟩
  have hPaway : ∀ t ∈ Icc 0 T, P t ∉ Metric.ball q (3 * (ρ : ℝ)) := by
    intro t ht hmem
    have hfar' := hfar (P t) (by
      exact Or.inl (Or.inl ⟨t, ht, rfl⟩))
    exact not_lt_of_ge hfar' (by simpa only [Metric.mem_ball, dist_eq_norm] using hmem)
  have hV₁ : Disjoint (Metric.ball q (2 * (ρ : ℝ))) K₁ := by
    apply Set.disjoint_left.mpr
    intro z hz hKz
    have hfar' := hfar z (by exact Or.inl (Or.inr hKz))
    have hnear' : ‖z - q‖ < 2 * (ρ : ℝ) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    linarith
  have hV₂ : Disjoint (Metric.ball q (2 * (ρ : ℝ))) K₂ := by
    apply Set.disjoint_left.mpr
    intro z hz hKz
    have hfar' := hfar z (by exact Or.inr hKz)
    have hnear' : ‖z - q‖ < 2 * (ρ : ℝ) := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz
    linarith
  refine ⟨a, b, ρ, hρ, ?_, hV₁, hV₂⟩
  refine ⟨P, T, hP, hPaway, Q, S, hQ, ⟨u, hucc, ?_⟩⟩
  change Q u ∈ Metric.ball q (2 * (ρ : ℝ))
  rw [Metric.mem_ball, dist_eq_norm]
  linarith

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
