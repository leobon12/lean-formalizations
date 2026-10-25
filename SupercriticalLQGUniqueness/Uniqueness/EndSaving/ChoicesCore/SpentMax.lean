import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Spent.SurgeryReinstantiation




 






set_option autoImplicit false
noncomputable section

open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.ChoicesCore

 

theorem newDist_around_closed_contacts
    (Dminus Dfull : LSCMetric) (ξ : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hB : BiLipschitz.Barrier.Barrier Dminus)
    (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x)
    (P : ℝ → ℂ) (V : Set ℂ) (z : ℂ) {r L : ℝ} (hr : 0 < r)
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 L)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 L))
    (hV : closure V ⊆ ball z (3 * r))
    (hP0 : 4 * r ≤ dist (P 0) z)
    (hPL : 4 * r ≤ dist (P L) z)
    (hne : (EndSaving.Spent.closedContactTimes P V L).Nonempty)
    (Caround N : ℝ≥0∞)
    (hAroundFull : aroundDist Dfull
      ⟨(z, (3 * r, 4 * r)), by constructor <;> nlinarith⟩ ≤ Caround * N) :
    ENNReal.ofReal
      (EndSaving.Spent.lastClosedContact P V L - EndSaving.Spent.firstClosedContact P V L) ≤
      Caround * N := by
  have hMetric : ∀ x y : ℂ, Dminus (x, y) ≤ Dfull (x, y) :=
    EndSaving.Spent.metric_le_weyl Dminus Dfull ξ hξ f
      (EndSaving.Spent.continuous_euclidForget_of_barrier Dminus hB hL) hWeyl hfn
  calc
    ENNReal.ofReal _ ≤ aroundDist Dminus
      ⟨(z, (3 * r, 4 * r)), by constructor <;> nlinarith⟩ :=
      EndSaving.Spent.closed_contact_time_le_around Dminus hB hL P V z hr hG hu
        hV hP0 hPL hne
    _ ≤ aroundDist Dfull
      ⟨(z, (3 * r, 4 * r)), by constructor <;> nlinarith⟩ :=
      EndSaving.Spent.aroundDist_le_of_metric_le Dminus Dfull hMetric _
    _ ≤ Caround * N := hAroundFull

 


theorem newDist_spent_closed_contacts
    (Dminus Dfull : LSCMetric) (ξ Cmax : ℝ) (hξ : 0 ≤ ξ)
    (f : C(ℂ, ℝ)) (hB : BiLipschitz.Barrier.Barrier Dminus)
    (hL : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, Dfull p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x) (hfmax : ∀ x : ℂ, f x ≤ Cmax)
    (P : ℝ → ℂ) (V : Set ℂ) (z : ℂ) {r L : ℝ} (hr : 0 < r)
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 L)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 L))
    (hV : closure V ⊆ ball z (3 * r))
    (hP0 : 4 * r ≤ dist (P 0) z)
    (hPL : 4 * r ≤ dist (P L) z)
    (hne : (EndSaving.Spent.closedContactTimes P V L).Nonempty)
    (Caround N B : ℝ≥0∞)
    (hAroundFull : aroundDist Dfull
      ⟨(z, (3 * r, 4 * r)), by constructor <;> nlinarith⟩ ≤ Caround * N)
    (hCompare : N ≤ 2 * B) :
    (⨆ u ∈ EndSaving.Spent.closedContactTimes P V L,
      ⨆ v ∈ EndSaving.Spent.closedContactTimes P V L, Dfull (P u, P v)) ⊔
      Dfull.len P (EndSaving.Spent.firstClosedContact P V L)
        (EndSaving.Spent.lastClosedContact P V L) ≤
      (ENNReal.ofReal (Real.exp (ξ * Cmax)) * Caround * 2) * B := by
  have hspent := EndSaving.Spent.spent_first_last_of_around_event Dminus Dfull
    ξ Cmax hξ f hB hL hWeyl hfn hfmax P V z hr hG hu
    hV hP0 hPL hne Caround N B hAroundFull hCompare
  have hcont : ContinuousOn P (Icc 0 L) :=
    EndSaving.Spent.continuousOn_euclid_of_barrier Dminus hB hL ⟨hG.1, hG.2.1⟩
  refine sup_le ?_ hspent
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv => ?_
  exact (EndSaving.Spent.closed_contact_pair_distance_le_window Dfull P V hcont hne hu hv).trans hspent


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.ChoicesCore
