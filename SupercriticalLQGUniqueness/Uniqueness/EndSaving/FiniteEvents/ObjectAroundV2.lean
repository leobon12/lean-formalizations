import SupercriticalLQGUniqueness.Uniqueness.EndSaving.ChoicesCore.SpentMax
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.InterfaceV2




 





set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric LQGMetric.MetricGeometry
open LQGMetric (DistC)
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents

 


theorem objectAtV2_around_closed_contacts
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (obj : EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (ω : Ω) (hE : h ω ∈ obj.E) (c : ℝ)
    (hrz : IsCircleAverage (h ω) r z c)
    (Dminus : LSCMetric) (f : C(ℂ, ℝ))
    (hBarrier : BiLipschitz.Barrier.Barrier Dminus) (hLength : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, D (h ω) p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x)
    (P : ℝ → ℂ) {L : ℝ}
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 L)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 L))
    (hP0 : 4 * (r : ℝ) ≤ dist (P 0) z)
    (hPL : 4 * (r : ℝ) ≤ dist (P L) z)
    (hne : (EndSaving.Spent.closedContactTimes P (obj.V : Set ℂ) L).Nonempty) :
    ENNReal.ofReal
      (EndSaving.Spent.lastClosedContact P (obj.V : Set ℂ) L -
        EndSaving.Spent.firstClosedContact P (obj.V : Set ℂ) L) ≤
      ENNReal.ofReal par.Caround *
        ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * c)) := by
  have hV : closure (obj.V : Set ℂ) ⊆ ball z (3 * (r : ℝ)) := by
    intro x hx
    exact (obj.closure_V_annulus hx).2
  obtain ⟨_, ⟨A, hAz, hAr, hAR, hAroundA⟩, _⟩ := obj.E_bounds (h ω) hE c hrz
  have hr0 : (0 : ℝ) < r := r.property
  have hAeq : A =
      ⟨(z, (3 * (r : ℝ), 4 * (r : ℝ))), by
        constructor <;> nlinarith only [hr0]⟩ := by
    apply Subtype.ext
    rcases A with ⟨⟨a, ⟨s, t⟩⟩, ha⟩
    change a = z at hAz
    change s = 3 * (r : ℝ) at hAr
    change t = 4 * (r : ℝ) at hAR
    simp only [hAz, hAr, hAR]
  have hAround : aroundDist (D (h ω))
      ⟨(z, (3 * (r : ℝ), 4 * (r : ℝ))), by
        constructor <;> nlinarith only [hr0]⟩ ≤
      ENNReal.ofReal par.Caround *
        ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
          Real.exp ((ξ : ℝ) * c)) := by
    simpa only [hAeq] using hAroundA
  exact EndSaving.ChoicesCore.newDist_around_closed_contacts Dminus (D (h ω)) ξ ξ.property.le f
    hBarrier hLength hWeyl hfn P (obj.V : Set ℂ) z hr0
    hG hu hV hP0 hPL hne _ _ hAround

 


theorem objectAtV2_spent_closed_contacts
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (z : ℂ) (r : Set.Ioi (0 : ℝ))
    (obj : EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (ω : Ω) (hE : h ω ∈ obj.E) (circleAvg : ℝ)
    (hrz : IsCircleAverage (h ω) r z circleAvg)
    (Dminus : LSCMetric) (f : C(ℂ, ℝ))
    (hBarrier : BiLipschitz.Barrier.Barrier Dminus) (hLength : Dminus.IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ, D (h ω) p = weylScale ξ f Dminus p)
    (hfn : ∀ x : ℂ, 0 ≤ f x)
    (hfmax : ∀ x : ℂ, f x ≤ par.Cmax)
    (P : ℝ → ℂ) {L : ℝ}
    (hG : IsGeodesicCurve (Dminus.pt ∘ P) 0 L)
    (hu : HasUnitSpeedOn (Dminus.pt ∘ P) (Icc 0 L))
    (hP0 : 4 * (r : ℝ) ≤ dist (P 0) z)
    (hPL : 4 * (r : ℝ) ≤ dist (P L) z)
    (hne : (EndSaving.Spent.closedContactTimes P (obj.V : Set ℂ) L).Nonempty)
    (B : ℝ≥0∞)
    (hCompare :
      ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * circleAvg)) ≤ 2 * B) :
    (⨆ u ∈ EndSaving.Spent.closedContactTimes P (obj.V : Set ℂ) L,
      ⨆ v ∈ EndSaving.Spent.closedContactTimes P (obj.V : Set ℂ) L,
        D (h ω) (P u, P v)) ⊔
      (D (h ω)).len P
        (EndSaving.Spent.firstClosedContact P (obj.V : Set ℂ) L)
        (EndSaving.Spent.lastClosedContact P (obj.V : Set ℂ) L) ≤
      (ENNReal.ofReal (Real.exp ((ξ : ℝ) * par.Cmax)) *
        ENNReal.ofReal par.Caround * 2) * B := by
  have hAround := objectAtV2_around_closed_contacts μ h D D' ξ Q cMid par pbar
    z r obj ω hE circleAvg hrz Dminus f hBarrier hLength hWeyl hfn
    P hG hu hP0 hPL hne
  have hspent := EndSaving.Spent.spent_first_last_closed_contacts Dminus (D (h ω))
    ξ par.Cmax ξ.property.le f hBarrier hLength hWeyl hfn hfmax
    P (obj.V : Set ℂ) hG hu hne (ENNReal.ofReal par.Caround)
    (ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) *
      Real.exp ((ξ : ℝ) * circleAvg))) B hAround hCompare
  have hcont : ContinuousOn P (Icc 0 L) :=
    EndSaving.Spent.continuousOn_euclid_of_barrier Dminus hBarrier hLength
      ⟨hG.1, hG.2.1⟩
  refine sup_le ?_ hspent
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun v => iSup_le fun hv => ?_
  exact (EndSaving.Spent.closed_contact_pair_distance_le_window (D (h ω)) P
    (obj.V : Set ℂ) hcont hne hu hv).trans hspent


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
