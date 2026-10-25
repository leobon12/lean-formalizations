import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.FbarMeas
import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.FiniteStableMeas




 

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
open LQGMetric (DistC)

private theorem ball_compl_nonempty (z : ℂ) (R : ℝ) :
    (Metric.ball z R)ᶜ.Nonempty := by
  refine ⟨z + ((max R 0 + 1 : ℝ) : ℂ), ?_⟩
  change ¬ dist (z + ((max R 0 + 1 : ℝ) : ℂ)) z < R
  rw [dist_eq_norm]
  simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
  have hpos : 0 < max R 0 + 1 := by
    have h := le_max_right R 0
    linarith
  rw [abs_of_pos hpos]
  have hle := le_max_left R 0
  linarith

theorem rawFV2_nullMeasurable {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (D D' : DistC → LSCMetric)
    {ξ : Set.Ioi (0 : ℝ)} {Qpar : ℝ}
    (hD : IsWeakLQGMetric ξ Qpar D)
    (hD' : IsWeakLQGMetric ξ Qpar D')
    (cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 P h D D' ξ Qpar cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) :
    NullMeasurableSet
      {g : DistC | EndSaving.FiniteEvents.FV2 P h D D' ξ Qpar cMid cPlus par pbar
        r b q K₁ K₂ obj Z g} (P.map h) := by
  let φ := EndSaving.FiniteEvents.bumpSumV2 P h D D' ξ Qpar cMid par pbar r obj Z
  let W (i : ℤ × ℤ) :=
    Metric.ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ))
  let V (i : ℤ × ℤ) := (obj i).V
  let z (i : ℤ × ℤ) := LQGMetric.GM.gridPt ((r : ℝ) / 100) i
  have hW : ∀ i ∈ Z, IsOpen (W i) := by
    intro i hi
    exact Metric.isOpen_ball
  have hWc : ∀ i ∈ Z, IsCompact (closure (W i)) := by
    intro i hi
    exact (isCompact_closedBall _ _).of_isClosed_subset
      isClosed_closure Metric.closure_ball_subset_closedBall
  have hWne : ∀ i ∈ Z, (W i)ᶜ.Nonempty := by
    intro i hi
    exact ball_compl_nonempty _ _
  have hVW : ∀ i ∈ Z, closure (V i : Set ℂ) ⊆ W i := by
    intro i hi x hx
    have hx3 := ((obj i).closure_V_annulus hx).2
    dsimp [W]
    exact Metric.mem_ball.mpr (lt_trans hx3 (by
      have hr : (0 : ℝ) < r := r.2
      linarith))
  have hStable := rawFiniteStable_circle_shifted_nullMeasurable
    P h hh hD K₁ K₂ hK₁ hK₂ Z W hW hWc hWne V hVW
    par.Ctime Qpar (fun _ => r) z φ
  have hFbar := fbarV2_nullMeasurable P h hh D D' hD hD'
    cMid cPlus par pbar r b q K₁ K₂ hK₁ hK₂ obj Z
  have hEq :
      {g : DistC | EndSaving.FiniteEvents.FV2 P h D D' ξ Qpar cMid cPlus par pbar
        r b q K₁ K₂ obj Z g} =
      {g : DistC | EndSaving.FiniteEvents.FbarV2 P h D D' ξ Qpar cMid cPlus par pbar
        r b q K₁ K₂ obj Z g} ∩
      {g : DistC | ∃ P' : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D (LQGMetric.GM.subTest g φ))
          K₁ K₂ P' T ∧
        ∀ i ∈ Z, ∃ c : ℝ, IsCircleAverage g r (z i) c ∧
          SourceStable (D g) P' T (W i) (V i)
            (ENNReal.ofReal par.Ctime * ENNReal.ofReal
              ((r : ℝ) ^ ((ξ : ℝ) * Qpar) *
                Real.exp ((ξ : ℝ) * c)))} := by
    ext g
    rfl
  rw [hEq]
  exact hFbar.inter hStable

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
