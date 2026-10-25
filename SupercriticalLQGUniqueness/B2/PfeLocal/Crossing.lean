import SupercriticalLQGUniqueness.B2.PfeLocal.Endpoint
import SupercriticalLQGUniqueness.B2.PfeLocal.Length
import LQGMetric.Topo.RectCross

 





set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 

theorem crossing_extract {P : ℝ → ℂ} {a b r R : ℝ} {z : ℂ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hrR : r < R) (ha : dist (P a) z < r) (hb : R < dist (P b) z) :
    ∃ σ τ : ℝ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧ dist (P σ) z = r ∧
      dist (P τ) z = R ∧ ∀ u ∈ Icc σ τ, dist (P u) z ∈ Icc r R := by
  have hf : ContinuousOn (fun t => dist (P t) z) (Icc a b) :=
    continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)
  obtain ⟨σ, τ, hασ, hστ, hτβ, hσ, hτ, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hab hf hrR.le ha.le hb.le
  refine ⟨σ, τ, hασ, ?_, hτβ, hσ, hτ, hbetween⟩
  exact lt_of_le_of_ne hστ (by
    intro heq
    have : r = R := by rw [← hσ, ← hτ, heq]
    exact hrR.ne this)

 

theorem crossing_extract_reverse {P : ℝ → ℂ} {a b r R : ℝ} {z : ℂ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hrR : r < R) (ha : R < dist (P a) z) (hb : dist (P b) z < r) :
    ∃ σ τ : ℝ, a ≤ σ ∧ σ < τ ∧ τ ≤ b ∧ dist (P σ) z = R ∧
      dist (P τ) z = r ∧ ∀ u ∈ Icc σ τ, dist (P u) z ∈ Icc r R := by
  have hf : ContinuousOn (fun t => dist (P t) z) (Icc a b) :=
    continuous_dist.comp_continuousOn (hP.prodMk continuousOn_const)
  obtain ⟨σ, τ, hασ, hστ, hτβ, hσ, hτ, hbetween⟩ :=
    LQGMetric.RectCross.exists_sub_crossing' hab hf hrR.le ha.le hb.le
  refine ⟨σ, τ, hασ, ?_, hτβ, hσ, hτ, hbetween⟩
  exact lt_of_le_of_ne hστ (by
    intro heq
    have : R = r := by rw [← hσ, ← hτ, heq]
    exact hrR.ne this.symm)

 

theorem acrossDist_le_internal (D : LSCMetric) (A : EuclideanAnnulus)
    (U : Set ℂ) (x y : ℂ) (hxA : x ∈ A.innerBoundary)
    (hyA : y ∈ A.outerBoundary) (hxU : x ∈ U) (hyU : y ∈ U) :
    acrossDist D A ≤ D.internal U (⟨x, hxU⟩, ⟨y, hyU⟩) := by
  calc
    acrossDist D A ≤ D.1 (x, y) := by
      unfold acrossDist
      exact iInf_le_of_le x <| iInf_le_of_le hxA <|
        iInf_le_of_le y <| iInf_le_of_le hyA le_rfl
    _ ≤ D.internal U (⟨x, hxU⟩, ⟨y, hyU⟩) :=
      edist_le_internal D U (⟨x, hxU⟩, ⟨y, hyU⟩)

end SupercriticalLQGUniqueness.B2.PfeLocal
