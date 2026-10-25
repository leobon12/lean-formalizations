import SupercriticalLQGUniqueness.B2.DG20Lim.R32DyadicGoodSurrounds
import SupercriticalLQGUniqueness.B2.DG20Lim.RDataFromCoords

 



set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def dyadicGoodAtR32 (R : RData) (C : ℝ≥0∞) (K : ℕ) (v : ℤ × ℤ) : Prop :=
  ∃ i ∈ sparseDyadicIndices K,
    let A := centeredRatAnnulusR32 (dyadicLatticeCenter K v).1
      (dyadicLatticeCenter K v).2 (ratRad64 1 i)
      (ratRad64_pos (by norm_num) i)
    R.around A ≤ C * R.across A.inner A.outer

theorem dyadicGoodAt_of_not_coupledSiteBadR32
    {Ω : Type} (Ylim : Ω → (CoordJ → ℝ) × RatCoords)
    (ω : Ω) (R : RData) (C : ℝ≥0∞) (K : ℕ) (v : ℤ × ℤ)
    (hAcross : R.across = fun O P => (Ylim ω).2.1 (O, P))
    (hAround : R.around = (Ylim ω).2.2)
    (hnot : ω ∉ coupledSiteBadR32 Ylim C K v) :
    dyadicGoodAtR32 R C K v := by
  classical
  by_contra hnone
  apply hnot
  intro i hi
  let A := centeredRatAnnulusR32 (dyadicLatticeCenter K v).1
    (dyadicLatticeCenter K v).2 (ratRad64 1 i)
    (ratRad64_pos (by norm_num) i)
  have hnotgood : ¬ R.around A ≤ C * R.across A.inner A.outer := by
    intro hg
    exact hnone ⟨i, hi, hg⟩
  simpa only [hAcross, hAround, A] using (lt_of_not_ge hnotgood)

end SupercriticalLQGUniqueness.B2.DG20Lim
