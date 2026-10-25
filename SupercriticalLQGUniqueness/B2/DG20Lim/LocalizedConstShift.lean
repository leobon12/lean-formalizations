import SupercriticalLQGUniqueness.B2.DG20Lim.GoodAnnulusCoupledLimit
import SupercriticalLQGUniqueness.B2.PfeAxioms.TranslationFiniteLFPP

 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def locTestMass (ε : ℝ) (hε : 0 < ε) : ℝ :=
  ∫ w : ℂ, locTest ε hε (0 : ℂ) w

theorem integral_locTest_eq_mass (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    (∫ w : ℂ, locTest ε hε z w) = locTestMass ε hε := by
  let F : ℂ → ℝ := fun w => locBump ε hε (-w) * heatKernel (ε ^ 2 / 2) 0 w
  have hv (w : ℂ) : locTest ε hε z w = F (w - z) := by
    have h1 : z - w = -(w - z) := by abel
    have h2 : (0 : ℂ) - (w - z) = z - w := by abel
    change locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w =
      locBump ε hε (-(w - z)) * heatKernel (ε ^ 2 / 2) 0 (w - z)
    rw [← h1]
    simp only [heatKernel, h2]
  have hv0 (w : ℂ) : locTest ε hε 0 w = F w := by
    simp [F, locTest, heatKernel]
  simp_rw [hv]
  rw [integral_sub_right_eq_self F z]
  simp only [locTestMass]
  congr 1
  funext w
  exact (hv0 w).symm

theorem locMollify_addConst (ε : ℝ) (hε : 0 < ε)
    (g : DistC) (c : ℝ) (z : ℂ) :
    locMollify ε hε (addConst g c) z =
      locMollify ε hε g z + c * locTestMass ε hε := by
  simp only [locMollify, addConst, addFun, add_apply,
    ofCont_apply, ContinuousMap.const_apply]
  rw [integral_mul_const, mul_comm, integral_locTest_eq_mass]

 

theorem lfppLocOn_addConst (ξ ε : ℝ) (hε : 0 < ε)
    (g : DistC) (c : ℝ) (S : Set ℂ) (z w : ℂ) :
    lfppLocOn ξ ε hε (addConst g c) S z w =
      ENNReal.ofReal (Real.exp (ξ * (c * locTestMass ε hε))) *
        lfppLocOn ξ ε hε g S z w := by
  unfold lfppLocOn
  have hφ : (fun u => locMollify ε hε (addConst g c) u) =
      fun u => locMollify ε hε g u + c * locTestMass ε hε :=
    funext fun u => locMollify_addConst ε hε g c u
  change lfppDOn ξ (fun u => locMollify ε hε (addConst g c) u) S z w = _
  rw [hφ]
  exact B2.PfeAxioms.lfppDOn_add_const ξ
    (locMollify ε hε g) S (c * locTestMass ε hε) z w

end SupercriticalLQGUniqueness.B2.DG20Lim
