import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.FiniteCircleShift
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.ShiftedNormalization
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylSample




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC)

 

theorem event_good_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (hD : IsWeakLQGMetric ξ Q D)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) :
    let ψ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z
    ∀ᵐ ω ∂P, ∀ i ∈ Z,
      EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z
        (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ)) →
      EndSaving.FiniteEvents.GoodSiteV2 P h D D' ξ Q cMid par pbar r b q K₁ K₂ obj i (h ω) := by
  classical
  dsimp only
  let ψ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z
  by_cases hcfg : EndSaving.Interfaces.Configuration r b K₁ K₂ Z
  · have hloc : ∀ᵐ ω ∂P, ∀ i ∈ Z,
        LQGMetric.addFun (h ω) (LQGMetric.testCont ψ) ∈ (obj i).E ↔
        LQGMetric.addFun (h ω) (LQGMetric.testCont (obj i).f) ∈ (obj i).E := by
      apply (Filter.eventually_all_finset Z).2
      intro i hi
      exact shifted_local_event_at_site_ae P h hh D D' ξ Q cMid par pbar
        r b K₁ K₂ obj Z hcfg i hi
    filter_upwards [Toolkit.WeylShift.ae_common_weyl_sample hD P h hh, hloc] with
      ω hw hl i hi hF
    let gZ := LQGMetric.addFun (h ω) (LQGMetric.testCont ψ)
    rcases hF with ⟨hbar, Pg, Tg, hgeo, hstable⟩
    rcases hbar with ⟨_, _, hbr, havgB, _, hsites, _, _, _, _⟩
    obtain ⟨hEi, hrz, havgR, hbin⟩ := hsites i hi
    obtain ⟨hrzSt, havgSt, τ', τ, σ, σ', hexc, hτ, hσ, hineq⟩ := hstable i hi
    let z := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
    let W := Metric.ball z (4 * (r : ℝ))
    have hbrOld : IsCircleAverage (h ω) b 0 hbr :=
      (isCircleAverage_addFun_iff_of_zero_sphere (h ω)
        (LQGMetric.testCont ψ) b 0 hbr
        (fun x hx => bumpSum_zero_on_reference_sphere P h D D' ξ Q cMid
          par pbar r b K₁ K₂ obj Z hcfg x hx)).mp havgB
    have hrzOld : IsCircleAverage (h ω) r z hrz :=
      (isCircleAverage_addFun_iff_of_zero_sphere (h ω)
        (LQGMetric.testCont ψ) r z hrz
        (fun x hx => bumpSum_zero_on_site_sphere P h D D' ξ Q cMid
          par pbar r b K₁ K₂ obj Z hcfg i hi x hx)).mp havgR
    have hstEq : hrzSt = hrz := isCircleAverage_unique havgSt havgR
    subst hrzSt
    have hsub := EndSaving.Scaling.subtractBumpsV2_add_bumpSum P h D D' ξ Q cMid
      par pbar r obj Z (h ω)
    change EndSaving.FiniteEvents.UniqueSetGeodesic
      (D (EndSaving.FiniteEvents.subtractBumpsV2 P h D D' ξ Q cMid par pbar
        r obj Z gZ)) K₁ K₂ Pg Tg at hgeo
    rw [hsub] at hgeo
    have hmetric := finite_shift_internal_eq_at_site P h D D' ξ Q cMid par
      pbar r b K₁ K₂ obj Z hcfg (h ω) hw.1 hw.2.1 hw.2.2
      i hi W (by exact Subset.rfl) (⟨Pg τ, hτ⟩, ⟨Pg σ, hσ⟩)
    change EndSaving.FiniteEvents.GoodSiteV2 P h D D' ξ Q cMid par pbar r b q K₁ K₂ obj i (h ω)
    refine ⟨(hl i hi).mp hEi, hbr, hrz, hbrOld, hrzOld, hbin,
      Pg, Tg, hgeo, τ', τ, σ, σ', hexc, hτ, hσ, ?_⟩
    exact hmetric ▸ hineq
  · filter_upwards [] with ω i hi hF
    exact False.elim (hcfg hF.1.2.1)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
