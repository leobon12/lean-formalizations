import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.FiniteEventsV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.ObjectAroundV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents.SizeBinV2




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
open LQGMetric (DistC)

 

theorem fV2_spent_closed_contacts
    {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (ω : Ω)
    (hF : FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z (h ω))
    (hBarrier : BiLipschitz.Barrier.Barrier (D
      (subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω))))
    (hLength : (D
      (subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω))).IsLengthSpace)
    (hWeyl : ∀ p : ℂ × ℂ,
      D (h ω) p = weylScale ξ
        (LQGMetric.testCont (bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z))
        (D (subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω))) p) :
    ∃ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr ∧
    ∃ P : ℝ → ℂ, ∃ T : ℝ,
      UniqueSetGeodesic
        (D (subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
        K₁ K₂ P T ∧
      ∀ i ∈ Z,
        ∃ c : ℝ, IsCircleAverage (h ω) r
          (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) c ∧
          ((⨆ u ∈ EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T,
              ⨆ v ∈ EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T,
                D (h ω) (P u, P v)) ⊔
            (D (h ω)).len P
              (EndSaving.Spent.firstClosedContact P ((obj i).V : Set ℂ) T)
              (EndSaving.Spent.lastClosedContact P ((obj i).V : Set ℂ) T)) ≤
            (ENNReal.ofReal (Real.exp ((ξ : ℝ) * par.Cmax)) *
              ENNReal.ofReal par.Caround * 2) *
                ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
                  Real.exp ((ξ : ℝ) * hbr)) := by
  rcases hF with ⟨hbar, P, T, hgeod, hstable⟩
  rcases hbar with ⟨_, hconfig, hbr, havg, hbad, hlocal, P₀, T₀, hgeod₀, hhit⟩
  refine ⟨hbr, havg, P, T, hgeod, ?_⟩
  intro i hi
  obtain ⟨hE, c, hc, hsize⟩ := hlocal i hi
  refine ⟨c, hc, ?_⟩
  let z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
  let dminus := D (subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω))
  let f := LQGMetric.testCont (bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z)
  have hG : IsGeodesicCurve (dminus.pt ∘ P) 0 T :=
    SetGeodesic.isGeodesic dminus K₁ K₂ P T hgeod.1
  have hu : HasUnitSpeedOn (dminus.pt ∘ P) (Icc 0 T) := hgeod.1.1.2.1
  have hP0 : 4 * (r : ℝ) ≤ dist (P 0) z := by
    have hout := Set.disjoint_right.mp (hconfig.2 i hi) (show P 0 ∈ K₁ ∪ K₂ ∪ Metric.sphere (0 : ℂ) b from Or.inl (Or.inl hgeod.1.2.1))
    simpa only [Metric.mem_ball, not_lt] using hout
  have hPT : 4 * (r : ℝ) ≤ dist (P T) z := by
    have hout := Set.disjoint_right.mp (hconfig.2 i hi) (show P T ∈ K₁ ∪ K₂ ∪ Metric.sphere (0 : ℂ) b from Or.inl (Or.inr hgeod.1.2.2.1))
    simpa only [Metric.mem_ball, not_lt] using hout
  obtain ⟨_, _, τprime, τ, _, _, hExc, _⟩ := hstable i hi
  rcases hExc with ⟨h0, h12, h23, h34, h4T, _, _, _, hτcl, _, _, _⟩
  have hne : (EndSaving.Spent.closedContactTimes P ((obj i).V : Set ℂ) T).Nonempty := by
    refine ⟨τ, ?_⟩
    exact ⟨⟨h0.trans h12, h23.trans (h34.trans h4T)⟩, hτcl⟩
  have hfn : ∀ x : ℂ, 0 ≤ f x := by
    intro x
    have hb := finite_bump_values_bounds_v2 μ h D D' ξ Q cMid par pbar r Z
      (fun j => LQGMetric.GM.gridPt ((r : ℝ) / 100) j) obj
      (configuration_V_disjoint_v2 μ h D D' ξ Q cMid par pbar r b K₁ K₂ Z obj hconfig) x
    simpa only [f, bumpSumV2, LQGMetric.testCont, ContinuousMap.coe_mk,
      Finset.sum_apply, _root_.sum_apply] using hb.1
  have hfmax : ∀ x : ℂ, f x ≤ par.Cmax := by
    intro x
    have hb := finite_bump_values_bounds_v2 μ h D D' ξ Q cMid par pbar r Z
      (fun j => LQGMetric.GM.gridPt ((r : ℝ) / 100) j) obj
      (configuration_V_disjoint_v2 μ h D D' ξ Q cMid par pbar r b K₁ K₂ Z obj hconfig) x
    simpa only [f, bumpSumV2, LQGMetric.testCont, ContinuousMap.coe_mk,
      Finset.sum_apply, _root_.sum_apply] using hb.2
  have hCompare := localSizeBin_upper_ennreal ξ Q r b q c hbr hsize
  exact objectAtV2_spent_closed_contacts μ h D D' ξ Q cMid par pbar
    z r (obj i) ω hE c hc dminus f hBarrier hLength hWeyl hfn hfmax
    P hG hu hP0 hPT hne _ hCompare

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FiniteEvents
