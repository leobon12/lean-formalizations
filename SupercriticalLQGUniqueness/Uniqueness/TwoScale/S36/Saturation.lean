import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.Shield




 













set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

 

theorem intGeod_transfer {D₁ D₂ : LSCMetric} {U Y : Set ℂ} (hYU : Y ⊆ U)
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) {P : ℝ → ℂ} {s t : ℝ}
    (h : IsIntGeod D₁ Y P s t) : IsIntGeod D₂ Y P s t := by
  obtain ⟨hc, htr, hlen, hfin⟩ := h
  obtain ⟨hc₂, hlen₂⟩ := curve_len_transfer_eq hI hc (fun τ hτ => hYU (htr τ hτ)) hfin.ne
  refine ⟨hc₂, htr, ?_, ?_⟩
  · rw [hlen₂, hlen, intExt_transfer hYU hI]
  · rw [hlen₂]
    exact hfin

theorem ibg_transfer {D₁ D₂ : LSCMetric} {z : ℂ} {r : ℝ} {U : Set ℂ}
    (hYU : TwoScale.S36Events.eventCarrier z r ⊆ U) (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y)
    {P : ℝ → ℂ} {s t : ℝ} (h : TwoScale.S36Events.InternalBoundaryGeodesic D₁ z r P s t) :
    TwoScale.S36Events.InternalBoundaryGeodesic D₂ z r P s t := by
  obtain ⟨hP, hs, ht⟩ := (ibg_iff D₁ z r P s t).mp h
  exact (ibg_iff D₂ z r P s t).mpr ⟨intGeod_transfer hYU hI hP, hs, ht⟩

theorem around_transfer {D₁ D₂ : LSCMetric} {U : Set ℂ}
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) {A : EuclideanAnnulus}
    (hA : A.toSet ⊆ U) : aroundDist D₁ A = aroundDist D₂ A :=
  BiLipschitz.EqualNormalizer.aroundDist_eq_of_internal_eq D₁ D₂ U (internal_eq_of_intExt_eq hI) A hA

theorem across_transfer {D₁ D₂ : LSCMetric} (hB₁ : BiLipschitz.Barrier.Barrier D₁) (hB₂ : BiLipschitz.Barrier.Barrier D₂)
    (hL₁ : D₁.IsLengthSpace) (hL₂ : D₂.IsLengthSpace) {U : Set ℂ}
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) {A : EuclideanAnnulus} {R : ℝ}
    (hR : A.outerRadius < R)
    (hsub : {y : ℂ | A.innerRadius < ‖y - A.center‖ ∧ ‖y - A.center‖ < R} ⊆ U) :
    acrossDist D₁ A = acrossDist D₂ A :=
  BiLipschitz.Barrier.acrossDist_eq_of_internal_eq D₁ D₂ hB₁ hB₂ hL₁ hL₂ A hR (internal_transfer hsub hI)

 
theorem toSet_subset_ball (A : EuclideanAnnulus) :
    A.toSet ⊆ Metric.ball A.center A.outerRadius := fun _ hy => hy.1

 

section Geometry

variable {z : ℂ} {r : ℝ}

theorem small_annulus_subset {x : ℂ} (hr : 0 < r) (hx : x ∈ TwoScale.S36Events.eventMiddle z r)
    {A : EuclideanAnnulus} (hc : A.center = x) (ho : A.outerRadius ≤ r / 5) :
    A.toSet ⊆ TwoScale.S36Events.eventCarrier z r := by
  intro y hy
  apply closedBall_subset_carrier_of_middle hr hx
  have h := toSet_subset_ball A hy
  rw [hc, Metric.mem_ball] at h
  exact Metric.mem_closedBall.mpr (h.le.trans ho)

theorem small_across_subset {x : ℂ} (hr : 0 < r) (hx : x ∈ TwoScale.S36Events.eventMiddle z r)
    {A : EuclideanAnnulus} (hc : A.center = x) :
    {y : ℂ | A.innerRadius < ‖y - A.center‖ ∧ ‖y - A.center‖ < r / 5} ⊆
      TwoScale.S36Events.eventCarrier z r := by
  intro y hy
  apply closedBall_subset_carrier_of_middle hr hx
  rw [Metric.mem_closedBall, dist_eq_norm, ← hc]
  exact hy.2.le

theorem closedBall_point_subset {x : ℂ} (hr : 0 < r) (hx : x ∈ TwoScale.S36Events.eventMiddle z r)
    {ρ : ℝ} (hρ : ρ ≤ r / 5) : Metric.closedBall x ρ ⊆ TwoScale.S36Events.eventCarrier z r :=
  (Metric.closedBall_subset_closedBall hρ).trans (closedBall_subset_carrier_of_middle hr hx)

theorem ball_union_sphere (x : ℂ) (ρ : ℝ) :
    Metric.ball x ρ ∪ Metric.sphere x ρ = Metric.closedBall x ρ := by
  ext y
  simp only [mem_union, Metric.mem_ball, Metric.mem_sphere, Metric.mem_closedBall]
  constructor
  · rintro (h | h)
    · exact h.le
    · exact h.le
  · intro h
    rcases eq_or_lt_of_le h with h | h
    · exact Or.inr h
    · exact Or.inl h

theorem closure_ball_subset {x : ℂ} {ρ : ℝ} :
    closure (Metric.ball x ρ) ⊆ Metric.ball x ρ ∪ Metric.sphere x ρ := by
  rw [ball_union_sphere]
  exact Metric.closure_ball_subset_closedBall

end Geometry

 
theorem pointSphere_transfer {D₁ D₂ : LSCMetric} (hB₁ : BiLipschitz.Barrier.Barrier D₁) (hB₂ : BiLipschitz.Barrier.Barrier D₂)
    (hL₁ : D₁.IsLengthSpace) (hL₂ : D₂.IsLengthSpace) {U : Set ℂ}
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.closedBall x ρ ⊆ U) :
    OptimalConstants.Ratios.setDist D₁ {x} (Metric.sphere x ρ) = OptimalConstants.Ratios.setDist D₂ {x} (Metric.sphere x ρ) := by
  refine setDist_transfer (fun γ a b hγ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hB₁ hL₁ hγ)
    (fun γ a b hγ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hB₂ hL₂ hγ) hL₁ hL₂
    Metric.isOpen_ball closure_ball_subset Metric.isClosed_sphere ?_ ?_ hI
  · rw [ball_union_sphere]
    exact hsub
  · rintro y rfl
    exact Metric.mem_ball_self hρ

 
theorem middle_transfer {D₁ D₂ : LSCMetric} (hB₁ : BiLipschitz.Barrier.Barrier D₁) (hB₂ : BiLipschitz.Barrier.Barrier D₂)
    (hL₁ : D₁.IsLengthSpace) (hL₂ : D₂.IsLengthSpace) {z : ℂ} {r : ℝ} (hr : 0 < r)
    {U : Set ℂ} (hYU : TwoScale.S36Events.eventCarrier z r ⊆ U)
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) :
    OptimalConstants.Ratios.setDist D₁ (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) =
      OptimalConstants.Ratios.setDist D₂ (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
  refine setDist_transfer (fun γ a b hγ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hB₁ hL₁ hγ)
    (fun γ a b hγ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hB₂ hL₂ hγ) hL₁ hL₂
    (eventOpen_isOpen z r) (closure_eventOpen_subset z r) (isClosed_eventBoundary z r) ?_
    (eventMiddle_subset_open z hr) hI
  rw [eventOpen_union_boundary z hr]
  exact hYU

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
