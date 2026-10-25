import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit.Infimum
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces.Section4Interfaces




 




set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath

 
theorem setDist_le_of_superset (D : LSCMetric) {A B A' B' : Set ℂ}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    OptimalConstants.Ratios.setDist D A' B' ≤ OptimalConstants.Ratios.setDist D A B := by
  unfold OptimalConstants.Ratios.setDist
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  exact iInf₂_le_of_le x (hA hx) (iInf₂_le y (hB hy))

 
theorem setDist_le_of_mem (D : LSCMetric) {A B : Set ℂ}
    {u v : ℂ} (hu : u ∈ A) (hv : v ∈ B) :
    OptimalConstants.Ratios.setDist D A B ≤ D (u, v) := by
  unfold OptimalConstants.Ratios.setDist
  exact iInf₂_le_of_le u hu (iInf₂_le v hv)

 

theorem closedBall_subset_double_ball {z u : ℂ} {s : ℝ}
    (hu : u ∈ Metric.ball z s) :
    Metric.closedBall z s ⊆ Metric.ball u (2 * s) := by
  intro x hx
  rw [Metric.mem_ball] at hu ⊢
  rw [Metric.mem_closedBall] at hx
  calc
    dist x u ≤ dist x z + dist z u := dist_triangle x z u
    _ < s + s := add_lt_add_of_le_of_lt hx (by simpa only [dist_comm] using hu)
    _ = 2 * s := by ring

 

theorem open_tube_gap_of_closed_ball_gap
    (D E : LSCMetric) (C saving : ℝ≥0∞)
    (z w u v : ℂ) (s r : ℝ)
    (hu : u ∈ Metric.closedBall z s)
    (hv : v ∈ Metric.closedBall w s)
    (hzu : Metric.closedBall z s ⊆ Metric.ball u r)
    (hwv : Metric.closedBall w s ⊆ Metric.ball v r)
    (hgap : OptimalConstants.Ratios.setDist E (Metric.closedBall z s) (Metric.closedBall w s) +
      saving < C * OptimalConstants.Ratios.setDist D (Metric.closedBall z s) (Metric.closedBall w s)) :
    OptimalConstants.Ratios.setDist E (Metric.ball u r) (Metric.ball v r) + saving <
      C * D (u, v) := by
  have hE := setDist_le_of_superset E hzu hwv
  have hD := setDist_le_of_mem D hu hv
  calc
    OptimalConstants.Ratios.setDist E (Metric.ball u r) (Metric.ball v r) + saving ≤
        OptimalConstants.Ratios.setDist E (Metric.closedBall z s) (Metric.closedBall w s) + saving :=
      add_le_add_left hE saving
    _ < C * OptimalConstants.Ratios.setDist D (Metric.closedBall z s) (Metric.closedBall w s) := hgap
    _ ≤ C * D (u, v) := by gcongr

 


theorem five_path_closed_ball_bound
    (D E : LSCMetric) (c : NNReal) (hc : 0 < c)
    (hDlen : D.IsLengthSpace) (hElen : E.IsLengthSpace)
    (hDreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      D.IsCurve P a b → ContinuousOn P (Set.Icc a b))
    (hEreg : ∀ (P : ℝ → ℂ) (a b : ℝ),
      E.IsCurve P a b → ContinuousOn P (Set.Icc a b))
    (hcomp : ∀ x y : ℂ, E (x, y) ≤ (c : ℝ≥0∞) * D (x, y))
    (b : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (θ : Set.Ioi (0 : ℝ)) (δInner s : ℝ)
    (hδInner : 0 < δInner)
    (hδB : δInner ≤ (1 - (a : ℝ)) ^ 4)
    (hradius : δInner * (b : ℝ) = 2 * s)
    (u v z w : ℂ)
    (hu : u ∈ Metric.ball z s)
    (hv : v ∈ Metric.ball w s)
    (huSphere : u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * b))
    (hvSphere : v ∈ Metric.sphere (0 : ℂ) b)
    (hlu : OptimalConstants.Ratios.EndpointLoop D b a θ u v u)
    (hlv : OptimalConstants.Ratios.EndpointLoop D b a θ u v v)
    (saving : ℝ≥0∞)
    (hgap : OptimalConstants.Ratios.setDist E (Metric.closedBall z s) (Metric.closedBall w s) +
      saving < (c : ℝ≥0∞) *
        OptimalConstants.Ratios.setDist D (Metric.closedBall z s) (Metric.closedBall w s)) :
    E (u, v) + saving ≤
      (c : ℝ≥0∞) * D (u, v) +
      ENNReal.ofReal (2 * (c : ℝ) *
        (δInner ^ ((θ : ℝ) / 2) + δInner ^ (θ : ℝ))) * D (u, v) := by
  have hsubU : Metric.closedBall z s ⊆ Metric.ball u (δInner * b) := by
    rw [hradius]
    exact closedBall_subset_double_ball hu
  have hsubV : Metric.closedBall w s ⊆ Metric.ball v (δInner * b) := by
    rw [hradius]
    exact closedBall_subset_double_ball hv
  have hOpen := open_tube_gap_of_closed_ball_gap D E (c : ℝ≥0∞)
    saving z w u v s (δInner * b)
    (Metric.ball_subset_closedBall hu) (Metric.ball_subset_closedBall hv)
    hsubU hsubV hgap
  have hSplice := OptimalConstants.FixedUnit.endpointLoop_splice_bound D E c hc hDlen hElen
    hDreg hEreg hcomp b a θ δInner hδInner hδB
    u v huSphere hvSphere hlu hlv
  calc
    E (u, v) + saving ≤
        (OptimalConstants.Ratios.setDist E (Metric.ball u (δInner * b)) (Metric.ball v (δInner * b)) +
          ENNReal.ofReal (2 * (c : ℝ) *
            (δInner ^ ((θ : ℝ) / 2) + δInner ^ (θ : ℝ))) * D (u, v)) +
          saving := by gcongr
    _ = (OptimalConstants.Ratios.setDist E (Metric.ball u (δInner * b)) (Metric.ball v (δInner * b)) +
          saving) +
          ENNReal.ofReal (2 * (c : ℝ) *
            (δInner ^ ((θ : ℝ) / 2) + δInner ^ (θ : ℝ))) * D (u, v) := by ac_rfl
    _ ≤ (c : ℝ≥0∞) * D (u, v) +
          ENNReal.ofReal (2 * (c : ℝ) *
            (δInner ^ ((θ : ℝ) / 2) + δInner ^ (θ : ℝ))) * D (u, v) := by
      exact add_le_add_left hOpen.le _


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath
