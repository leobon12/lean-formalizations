import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.OldGeoCountV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.CountInternal




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC)

 

theorem old_geo_count_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D)
    (hD' : IsWeakLQGMetric ξ Q D')
    (cP : NNReal) (hcmid0 : 0 ≤ cMid) (hcmid : cMid < (cP : ℝ))
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cP)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z₀ Z₁ : Finset (ℤ × ℤ))
    (hcfg : EndSaving.Interfaces.Configuration r b K₁ K₂ (Z₀ ∪ Z₁))
    (hdisj : Disjoint Z₀ Z₁) :
    let ψ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z₀
    ∀ᵐ ω ∂P,
      EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid (cP : ℝ≥0∞) par pbar
        r b q K₁ K₂ obj Z₀
        (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ)) →
      (∀ i ∈ Z₁,
        EndSaving.FiniteEvents.GoodSiteV2 P h D D' ξ Q cMid par pbar
          r b q K₁ K₂ obj i (h ω)) →
      ((cP : ℝ) - cMid) * par.Cinc * Z₁.card ≤
        (1 + (cP : ℝ) * EndSaving.Choices.cSpent ξ par) * Z₀.card := by
  dsimp only
  let ψ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z₀
  filter_upwards [EndSaving.Choices.ae_regularAt_self hD P h hh,
    EndSaving.Choices.ae_regularAt_self hD' P h hh,
    EndSaving.Choices.ae_regularAt_shift hD P h hh ψ, hPlus] with
    ω hreg hreg' hregs hopt hF hgood
  have hcp : (0 : ℝ≥0∞) < cP := by
    have : (0 : ℝ) < (cP : ℝ) := lt_of_le_of_lt hcmid0 hcmid
    exact_mod_cast this
  have hcomp : ∀ x y : ℂ, D' (h ω) (x, y) ≤
      (cP : ℝ≥0∞) * D (h ω) (x, y) := by
    intro x y
    rw [← hopt]
    exact EndSaving.Choices.allPairs_le_upperOptimal (D (h ω)) (D' (h ω))
      (hopt.symm ▸ hcp) x y
  exact EndSaving.Choices.old_geo_count_pathwise P h D D' ξ Q cMid (cP : ℝ≥0∞)
    par pbar r b q K₁ K₂ obj Z₀ Z₁ hcfg hdisj (h ω)
    hreg hreg' hregs cP rfl hcmid0 hcmid hcomp hF hgood

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
