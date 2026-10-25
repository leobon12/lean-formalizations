import SupercriticalLQGUniqueness.B2.DG20Lim.CircleLowerTail
import SupercriticalLQGUniqueness.B2.DG20Lim.NormalizedAroundUpperTail
import SupercriticalLQGUniqueness.B2.DG20Lim.AroundMeasurable

 

set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def unitInnerCircle : RatCircle := ⟨0, 0, 1, by norm_num⟩
def unitOuterCircle : RatCircle := ⟨0, 0, 2, by norm_num⟩

private theorem unitInnerCenter : unitInnerCircle.center = (0 : ℂ) := by
  apply Complex.ext <;> simp [RatCircle.center, unitInnerCircle]

private theorem unitOuterCenter : unitOuterCircle.center = (0 : ℂ) := by
  apply Complex.ext <;> simp [RatCircle.center, unitOuterCircle]

def unitRatAnnulus : RatAnnulus := by
  refine ⟨unitInnerCircle, unitOuterCircle, by norm_num [unitInnerCircle], ?_⟩
  constructor
  · norm_num [unitOuterCircle]
  · intro z hz
    have hd : dist z (0 : ℂ) ≤ 1 := by
      rw [RatCircle.closedDisk, unitInnerCenter] at hz
      simpa [unitInnerCircle] using (mem_closedBall.mp hz)
    rw [RatCircle.openDisk, unitOuterCenter]
    have hr : (unitOuterCircle.radius : ℝ) = 2 := rfl
    rw [hr]
    exact mem_ball.mpr (by linarith)

def unitEuclideanAnnulus : EuclideanAnnulus :=
  ⟨((0 : ℂ), (1, 2)), by norm_num, by norm_num⟩

theorem unitEuclidean_toSet_subset_rat :
    unitEuclideanAnnulus.toSet ⊆ unitRatAnnulus.toSet := by
  intro z hz
  have hz' : z ∈ ball (0 : ℂ) 2 \ closure (ball 0 1) := by
    simpa only [EuclideanAnnulus.toSet, unitEuclideanAnnulus,
      EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.outerRadius] using hz
  have hmem : z ∈ closedBall (0 : ℂ) 2 \ ball 0 1 := by
    exact ⟨mem_closedBall.mpr hz'.1.le, fun h => hz'.2 (subset_closure h)⟩
  have hi : unitRatAnnulus.inner = unitInnerCircle := rfl
  have ho : unitRatAnnulus.outer = unitOuterCircle := rfl
  rw [RatAnnulus.toSet, hi, ho, RatCircle.closedDisk, RatCircle.openDisk,
    unitOuterCenter, unitInnerCenter]
  simpa [unitInnerCircle, unitOuterCircle] using hmem

theorem unitAnnulus_inner_eq :
    unitRatAnnulus.inner.toSet = unitEuclideanAnnulus.innerBoundary := by
  have hi : unitRatAnnulus.inner = unitInnerCircle := rfl
  rw [hi, RatCircle.toSet, unitInnerCenter]
  simp [unitInnerCircle, EuclideanAnnulus.innerBoundary, unitEuclideanAnnulus,
    EuclideanAnnulus.center, EuclideanAnnulus.innerRadius]

theorem unitAnnulus_outer_eq :
    unitRatAnnulus.outer.toSet = unitEuclideanAnnulus.outerBoundary := by
  have ho : unitRatAnnulus.outer = unitOuterCircle := rfl
  rw [ho, RatCircle.toSet, unitOuterCenter]
  simp [unitOuterCircle, EuclideanAnnulus.outerBoundary, unitEuclideanAnnulus,
    EuclideanAnnulus.center, EuclideanAnnulus.outerRadius]

theorem unitCircles_disjoint :
    Disjoint unitInnerCircle.toSet unitOuterCircle.toSet := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  have h1 : dist z (0 : ℂ) = 1 := by
    rw [RatCircle.toSet] at hz
    rw [unitInnerCenter] at hz
    simpa [unitInnerCircle] using (mem_sphere.mp hz)
  have h2 : dist z (0 : ℂ) = 2 := by
    rw [RatCircle.toSet] at hw
    rw [unitOuterCenter] at hw
    simpa [unitOuterCircle] using (mem_sphere.mp hw)
  linarith

 

theorem finiteAroundCoords_unit_le_euclidean (D : LQGMetric.ContMetric) :
    finiteAroundCoords D unitRatAnnulus ≤
      D.aroundDist unitEuclideanAnnulus.toSet
        unitEuclideanAnnulus.innerBoundary
        unitEuclideanAnnulus.outerBoundary := by
  rw [finiteAroundCoords, unitAnnulus_inner_eq, unitAnnulus_outer_eq]
  unfold LQGMetric.ContMetric.aroundDist
  refine le_iInf fun a => le_iInf fun b => le_iInf fun γ =>
    le_iInf fun hab => le_iInf fun hγ => le_iInf fun hA =>
      le_iInf fun hsep => ?_
  exact iInf_le_of_le a (iInf_le_of_le b
    (iInf_le_of_le γ (iInf_le_of_le hab
      (iInf_le_of_le hγ
        (iInf_le_of_le (hA.trans unitEuclidean_toSet_subset_rat)
          (iInf_le_of_le hsep le_rfl))))))

end SupercriticalLQGUniqueness.B2.DG20Lim
