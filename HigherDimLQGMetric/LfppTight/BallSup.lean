import HigherDimLQGMetric.LfppTight.Confinement
import HigherDimLQGMetric.DGZ.Continuity

/-! Point distances are bounded by the supremum in the adapter confinement event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_lfppMetric_le_supBall {d : ℕ} (ξ : ℝ) (H : Rd d → ℝ)
    (hH : Continuous H) (r : ℝ)
    {x y : Rd d} (hx : x ∈ ball (0 : Rd d) r) (hy : y ∈ ball (0 : Rd d) r) :
    DGZ.lfppMetric ξ H x y ≤
      ⨆ p : ball (0 : Rd d) r × ball (0 : Rd d) r,
        DGZ.lfppMetric ξ H p.1 p.2 := by
  have hK : IsCompact (closedBall (0 : Rd d) r ×ˢ closedBall (0 : Rd d) r) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hK.bddAbove_image (DGZ.continuous_lfppMetric hH ξ).continuousOn
  have hb : BddAbove (range fun p : ball (0 : Rd d) r × ball (0 : Rd d) r =>
      DGZ.lfppMetric ξ H p.1 p.2) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact hB ⟨(p.1.1, p.2.1),
      ⟨ball_subset_closedBall p.1.2, ball_subset_closedBall p.2.2⟩, rfl⟩
  exact le_ciSup hb (⟨x, hx⟩, ⟨y, hy⟩)

/-- The third adapter event gives the pointwise hypothesis of the path
confinement lemma simultaneously for all pairs in the inner ball. -/
theorem l6a_crossing_gap_pointwise {d : ℕ} (ξ : ℝ) (H : Rd d → ℝ)
    (hH : Continuous H) {r R : ℝ}
    (hgap : ¬ DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R) ≤
      ⨆ p : ball (0 : Rd d) r × ball (0 : Rd d) r,
        DGZ.lfppMetric ξ H p.1 p.2)
    {x y : Rd d} (hx : x ∈ ball (0 : Rd d) r) (hy : y ∈ ball (0 : Rd d) r) :
    HigherDimLFPP.lfppDistOn ξ H univ x y <
      DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R) := by
  exact lt_of_le_of_lt (l6a_lfppMetric_le_supBall ξ H hH r hx hy) (lt_of_not_ge hgap)

/-- One adapter confinement event controls the perturbed metric at every
pair in the inner ball. -/
theorem l6a_global_coupled_upper_of_gap {d : ℕ} (ξ M : ℝ)
    (H Ψ : Rd d → ℝ) (hH : Continuous H) (hΨ : Continuous Ψ)
    {r R : ℝ} (hrr : r < R)
    (hgap : ¬ DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R) ≤
      ⨆ p : ball (0 : Rd d) r × ball (0 : Rd d) r,
        DGZ.lfppMetric ξ H p.1 p.2)
    (hM : ∀ z ∈ ball (0 : Rd d) R, |Ψ z| ≤ M)
    {x y : Rd d} (hx : x ∈ ball (0 : Rd d) r) (hy : y ∈ ball (0 : Rd d) r) :
    DGZ.lfppMetric ξ (fun z => H z + Ψ z) x y ≤
      Real.exp (|ξ| * M) * DGZ.lfppMetric ξ H x y := by
  exact l6a_global_coupled_upper ξ M H Ψ hH hΨ hrr hx hy
    (l6a_crossing_gap_pointwise ξ H hH hgap hx hy) hM

end HigherDimLQGMetric
