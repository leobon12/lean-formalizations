import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding.BlockEventUM
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3




set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding

 

theorem goodSet_eq_of_common_scale (D E D' E' : LSCMetric)
    (k lam : ℝ) (hk : 0 < k)
    (hD : ∀ x y : ℂ, D' (x,y) = ENNReal.ofReal k * D (x,y))
    (hE : ∀ x y : ℂ, E' (x,y) = ENNReal.ofReal k * E (x,y))
    (c u a b : ℂ) (R : ℝ) (hu : u ∈ closedBall c R) :
    Objects.Producer.goodSet D' c u R (lam * (E' (a,b)).toReal) hu =
      Objects.Producer.goodSet D c u R (lam * (E (a,b)).toReal) hu := by
  have hc0 : ENNReal.ofReal k ≠ 0 := (ENNReal.ofReal_pos.mpr hk).ne'
  have hcTop : ENNReal.ofReal k ≠ ∞ := ENNReal.ofReal_ne_top
  have hth : ENNReal.ofReal (lam * (E' (a,b)).toReal) =
      ENNReal.ofReal k * ENNReal.ofReal (lam * (E (a,b)).toReal) := by
    rw [hE a b, ENNReal.toReal_mul, ENNReal.toReal_ofReal hk.le]
    have hcomm : lam * (k * (E (a,b)).toReal) =
        k * (lam * (E (a,b)).toReal) := by ring
    rw [hcomm, ENNReal.ofReal_mul hk.le]
  ext x
  simp only [Objects.Producer.goodSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hxSphere, hxBall, hcost⟩
    refine ⟨hxSphere, hxBall, ?_⟩
    have hI := Positivity.Witnesses.internal_eq_mul_of_dist_scale D D' (ENNReal.ofReal k)
      hc0 hcTop hD (closedBall c R) (⟨x,hxBall⟩, ⟨u,hu⟩)
    rw [hI, hth] at hcost
    exact (ENNReal.mul_le_mul_iff_right hc0 hcTop).mp hcost
  · rintro ⟨hxSphere, hxBall, hcost⟩
    refine ⟨hxSphere, hxBall, ?_⟩
    have hI := Positivity.Witnesses.internal_eq_mul_of_dist_scale D D' (ENNReal.ofReal k)
      hc0 hcTop hD (closedBall c R) (⟨x,hxBall⟩, ⟨u,hu⟩)
    rw [hI, hth]
    exact (ENNReal.mul_le_mul_iff_right hc0 hcTop).mpr hcost

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockCoding
