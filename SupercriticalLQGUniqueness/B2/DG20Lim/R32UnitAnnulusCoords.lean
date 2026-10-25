import SupercriticalLQGUniqueness.B2.DG20Lim.CircleLowerTail
import SupercriticalLQGUniqueness.B2.DG20Lim.NormalizedAroundUpperTail
import SupercriticalLQGUniqueness.B2.DG20Lim.AroundMeasurable

 



set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def unitInnerCircleR32 : RatCircle := ⟨0, 0, 1, by norm_num⟩
def unitOuterCircleR32 : RatCircle := ⟨0, 0, 3 / 2, by norm_num⟩

private theorem unitInnerCenterR32 : unitInnerCircleR32.center = (0 : ℂ) := by
  apply Complex.ext <;> simp [RatCircle.center, unitInnerCircleR32]

private theorem unitOuterCenterR32 : unitOuterCircleR32.center = (0 : ℂ) := by
  apply Complex.ext <;> simp [RatCircle.center, unitOuterCircleR32]

def unitRatAnnulusR32 : RatAnnulus := by
  refine ⟨unitInnerCircleR32, unitOuterCircleR32, by norm_num [unitInnerCircleR32], ?_⟩
  constructor
  · norm_num [unitOuterCircleR32]
  · intro z hz
    have hd : dist z (0 : ℂ) ≤ 1 := by
      rw [RatCircle.closedDisk, unitInnerCenterR32] at hz
      simpa [unitInnerCircleR32] using (mem_closedBall.mp hz)
    rw [RatCircle.openDisk, unitOuterCenterR32]
    have hr : (unitOuterCircleR32.radius : ℝ) = 3 / 2 := by
      simp [unitOuterCircleR32]
    rw [hr]
    exact mem_ball.mpr (by linarith)

def unitEuclideanAnnulusR32 : EuclideanAnnulus :=
  ⟨((0 : ℂ), (1, 3 / 2)), by norm_num, by norm_num⟩

theorem unitEuclidean_toSet_subset_ratR32 :
    unitEuclideanAnnulusR32.toSet ⊆ unitRatAnnulusR32.toSet := by
  intro z hz
  have hz' : z ∈ ball (0 : ℂ) (3 / 2) \ closure (ball 0 1) := by
    simpa only [EuclideanAnnulus.toSet, unitEuclideanAnnulusR32,
      EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
      EuclideanAnnulus.outerRadius] using hz
  have hmem : z ∈ closedBall (0 : ℂ) (3 / 2) \ ball 0 1 := by
    exact ⟨mem_closedBall.mpr hz'.1.le, fun h => hz'.2 (subset_closure h)⟩
  have hi : unitRatAnnulusR32.inner = unitInnerCircleR32 := rfl
  have ho : unitRatAnnulusR32.outer = unitOuterCircleR32 := rfl
  rw [RatAnnulus.toSet, hi, ho, RatCircle.closedDisk, RatCircle.openDisk,
    unitOuterCenterR32, unitInnerCenterR32]
  simpa [unitInnerCircleR32, unitOuterCircleR32] using hmem

theorem unitAnnulus_inner_eqR32 :
    unitRatAnnulusR32.inner.toSet = unitEuclideanAnnulusR32.innerBoundary := by
  have hi : unitRatAnnulusR32.inner = unitInnerCircleR32 := rfl
  rw [hi, RatCircle.toSet, unitInnerCenterR32]
  simp [unitInnerCircleR32, EuclideanAnnulus.innerBoundary, unitEuclideanAnnulusR32,
    EuclideanAnnulus.center, EuclideanAnnulus.innerRadius]

theorem unitAnnulus_outer_eqR32 :
    unitRatAnnulusR32.outer.toSet = unitEuclideanAnnulusR32.outerBoundary := by
  have ho : unitRatAnnulusR32.outer = unitOuterCircleR32 := rfl
  rw [ho, RatCircle.toSet, unitOuterCenterR32]
  simp [unitOuterCircleR32, EuclideanAnnulus.outerBoundary, unitEuclideanAnnulusR32,
    EuclideanAnnulus.center, EuclideanAnnulus.outerRadius]

theorem unitCircles_disjointR32 :
    Disjoint unitInnerCircleR32.toSet unitOuterCircleR32.toSet := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  have h1 : dist z (0 : ℂ) = 1 := by
    rw [RatCircle.toSet] at hz
    rw [unitInnerCenterR32] at hz
    simpa [unitInnerCircleR32] using (mem_sphere.mp hz)
  have h2 : dist z (0 : ℂ) = 3 / 2 := by
    rw [RatCircle.toSet] at hw
    rw [unitOuterCenterR32] at hw
    simpa [unitOuterCircleR32] using (mem_sphere.mp hw)
  linarith

 

theorem finiteAroundCoords_unit_le_euclideanR32 (D : LQGMetric.ContMetric) :
    finiteAroundCoords D unitRatAnnulusR32 ≤
      D.aroundDist unitEuclideanAnnulusR32.toSet
        unitEuclideanAnnulusR32.innerBoundary
        unitEuclideanAnnulusR32.outerBoundary := by
  rw [finiteAroundCoords, unitAnnulus_inner_eqR32, unitAnnulus_outer_eqR32]
  unfold LQGMetric.ContMetric.aroundDist
  refine le_iInf fun a => le_iInf fun b => le_iInf fun γ =>
    le_iInf fun hab => le_iInf fun hγ => le_iInf fun hA =>
      le_iInf fun hsep => ?_
  exact iInf_le_of_le a (iInf_le_of_le b
    (iInf_le_of_le γ (iInf_le_of_le hab
      (iInf_le_of_le hγ
        (iInf_le_of_le (hA.trans unitEuclidean_toSet_subset_ratR32)
          (iInf_le_of_le hsep le_rfl))))))

end SupercriticalLQGUniqueness.B2.DG20Lim
