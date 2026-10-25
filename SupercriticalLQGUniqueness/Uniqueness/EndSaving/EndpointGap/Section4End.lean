import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.EndpointGap
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open LQGMetric (DistC)

 

theorem strict_gap_of_lt_tsub {x y error saving : ℝ≥0∞}
    (hbad : x < y - error) (hsaving : saving ≤ error) :
    x + saving < y := by
  have he : x + error < y := (lt_tsub_iff_right (a := x) (b := y) (c := error)).mp hbad
  exact (add_le_add_right hsaving x).trans_lt he

 


theorem strict_gap_of_not_countingBadEvent
    {Ω : Type} [MeasurableSpace Ω] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cPlus : ℝ≥0∞) (R : AdmissibleRadii)
    (event : ∀ _z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii → Set Ω)
    (b ε : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (ω : Ω) (hbr : ℝ)
    (hCircle : IsCircleAverage (h ω) b 0 hbr)
    (hsize : ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      ε ^ 2 * (b : ℝ) ≤ (r : ℝ) → (r : ℝ) ≤ ε * (b : ℝ) →
      ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
        ∃ hrz : ℝ, IsCircleAverage (h ω) r z hrz ∧
          SizeWindow ξ Q ε b r hbr hrz)
    (hcover : ∀ z ∈ Metric.ball (0 : ℂ) (3 * (b : ℝ)),
      ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (i : ℤ × ℤ),
        ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
        LQGMetric.GM.gridPt ((r : ℝ) / 100) i ∈
          Metric.ball z ((r : ℝ) / 25) ∧
        ω ∈ event (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr)
    (hnot : ω ∉ CountingBadEvent h D D' ξ Q cPlus R event b ε K₁ K₂)
    {saving : ℝ≥0∞}
    (hsaving : saving ≤ ENNReal.ofReal ((1 / 2 : ℝ) * (ε : ℝ) ^
      (2 * (ξ : ℝ) * (Q + 3)) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * hbr))) :
    OptimalConstants.Ratios.setDist (D' (h ω)) K₁ K₂ + saving <
      cPlus * OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ := by
  have hstrict : OptimalConstants.Ratios.setDist (D' (h ω)) K₁ K₂ <
      cPlus * OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ -
        ENNReal.ofReal ((1 / 2 : ℝ) * (ε : ℝ) ^
          (2 * (ξ : ℝ) * (Q + 3)) * (b : ℝ) ^ ((ξ : ℝ) * Q) *
            Real.exp ((ξ : ℝ) * hbr)) := by
    by_contra hn
    apply hnot
    exact ⟨hbr, hCircle, le_of_not_gt hn, hsize, hcover⟩
  exact strict_gap_of_lt_tsub hstrict hsaving

 


theorem outer_measure_le_of_good_exclusion
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Good Bad : Set Ω) (η : ℝ≥0∞)
    (hGoodMeas : MeasurableSet Good)
    (hGood : 1 ≤ P Good + η)
    (hExclude : Bad ⊆ Goodᶜ) : P Bad ≤ η := by
  have hGoodFinite : P Good ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
      (measure_mono (Set.subset_univ Good) |>.trans_eq
        (IsProbabilityMeasure.measure_univ (μ := P)))
  calc
    P Bad ≤ P Goodᶜ := measure_mono hExclude
    _ = 1 - P Good := by rw [measure_compl hGoodMeas hGoodFinite,
      IsProbabilityMeasure.measure_univ]
    _ ≤ η := tsub_le_iff_right.mpr (by simpa only [add_comm] using hGood)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.EndpointGap
