import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.OldGeoCount




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
open LQGMetric (DistC)

 

theorem old_geo_length_ae
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
    ∀ᵐ ω ∂P,
      EndSaving.FiniteEvents.FV2 P h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z
        (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ)) →
      ∃ hbr : ℝ,
        IsCircleAverage
          (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ)) b 0 hbr ∧
        ∀ (Pg : ℝ → ℂ) (T : ℝ),
          EndSaving.FiniteEvents.UniqueSetGeodesic (D (h ω)) K₁ K₂ Pg T →
          (D (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ))).len Pg 0 T ≤
            OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ +
              ENNReal.ofReal (EndSaving.Choices.cSpent ξ par *
                EndSaving.Choices.scaleB ξ Q b q hbr * Z.card) := by
  dsimp only
  let ψ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Q cMid par pbar r obj Z
  filter_upwards [EndSaving.Choices.ae_regularAt_self hD P h hh] with ω hreg hF
  rcases hF.1 with ⟨_, hcfg, hbr, havg, _, hlocal, _, _, _, _⟩
  refine ⟨hbr, havg, ?_⟩
  intro Pg T hU
  have hloc : ∀ i ∈ Z,
      ∃ c : ℝ, IsCircleAverage
        (LQGMetric.addFun (h ω) (LQGMetric.testCont ψ)) r
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) c ∧
        EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q c hbr := by
    intro i hi
    obtain ⟨_, c, hc, hbin⟩ := hlocal i hi
    exact ⟨c, hc, hbin⟩
  choose! c hc hbin using hloc
  have hNB : ∀ i ∈ Z,
      EndSaving.Choices.scaleN ξ Q r (c i) ≤ 2 * EndSaving.Choices.scaleB ξ Q b q hbr := by
    intro i hi
    have h := (hbin i hi).2
    change (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c i) ≤
      2 * ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr))
    nlinarith only [h]
  have hlen := EndSaving.Choices.old_geo_length_field P h D D' ξ Q cMid par pbar
    r b K₁ K₂ obj Z hcfg (h ω) hreg
    (fun i hi => (hlocal i hi).1) c hc (EndSaving.Choices.scaleB ξ Q b q hbr)
    hNB Pg T hU.1
  simpa only [hU.1.2.2.2] using hlen

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
