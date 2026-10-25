import SupercriticalLQGUniqueness.Uniqueness.Objects.Network.EventRegularity
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.TwoSet.MeshCount




 




set_option autoImplicit false
noncomputable section
open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Network
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 
theorem nearestGrid_mem_grid (m : ℝ) (z : ℂ) :
    TwoScale.TwoSet.nearestGrid m z ∈ grid m := by
  refine ⟨⌊z.re / m + 1/2⌋, ⌊z.im / m + 1/2⌋, ?_⟩
  apply Complex.ext
  · simp only [TwoScale.TwoSet.nearestGrid,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · simp only [TwoScale.TwoSet.nearestGrid,
      Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im]
    ring


 

theorem nearestGrid_reg_site_of_radius_bound (C : Constants) (k : ℕ)
    (ε : ℝ) (z : ℂ)
    (hProtected : closedBall z (Real.sqrt ε * C.r) ⊆
      ann 0 C.r (4*C.r))
    (hRadius : lam k * C.r / 4 +
      2 * 4 ^ (regK k) * lam k * C.r ≤ Real.sqrt ε * C.r) :
    TwoScale.TwoSet.nearestGrid
      (lam k * C.r / 4) z ∈ regSites C k := by
  let m := lam k * C.r / 4
  have hm : 0 < m := by
    have hlam : 0 < lam k := by
      unfold lam
      positivity
    exact div_pos (mul_pos hlam C.rPos) (by norm_num)
  have hnear : dist (TwoScale.TwoSet.nearestGrid m z) z < m := by
    rw [dist_comm, dist_eq_norm]
    exact TwoScale.TwoSet.nearestGrid_norm_lt hm z
  apply reg_site_of_center_margin C k ε z
  · exact nearestGrid_mem_grid m z
  · exact hProtected
  · dsimp [m] at hnear
    linarith


end SupercriticalLQGUniqueness.Uniqueness.Objects.Network
