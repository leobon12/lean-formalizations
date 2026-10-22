import HigherDimLQGMetric.Sphere.Tail
import HigherDimLQGMetric.Sphere.Var

/-!
# Gaussian point tails for sphere-average differences

Packet L2a. The single-point Gaussian estimate used in the dyadic block argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistRd d}

/-- A centered sphere-average difference has a Gaussian tail under any explicit variance bound. -/
theorem l2a_point_tail (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d) {V A : ℝ}
    (hV : Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] ≤ V)
    (hA : 0 ≤ A) :
    P.real {ω | A ≤ |sphereAvg (h ω) r z - sphereAvg (h ω) ρ w|} ≤
      2 * Real.exp (-A ^ 2 / (2 * (V + 1))) := by
  set X : Unit → Ω → ℝ := fun _ ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w
  let q : SphPair d := ⟨((r, z), (ρ, w)), hr, hρ⟩
  have hG : IsGaussianProcess X P :=
    (hh.isGaussianProcess_sphereAvg_sub hd).comp_right (fun _ : Unit => Sum.inl q)
  have h0 : ∀ t : Unit, ∫ ω, X t ω ∂P = 0 := fun _ =>
    (hh.hasGaussianLaw_sphereAvg_sub hd hr hρ z w).2
  have hint : ∀ s : ℝ, Integrable (fun ω => ⨆ _ : Unit, s * X () ω) P := by
    intro s
    simp only [ciSup_const]
    exact ((hG.hasGaussianLaw_eval ()).integrable).const_mul s
  have hv : 0 ≤ V + 1 := by
    have hv0 := variance_nonneg (fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) P
    linarith
  have hvar : ∀ t : Unit, Var[X t; P] ≤ Real.sqrt (V + 1) ^ 2 := by
    intro _
    rw [Real.sq_sqrt hv]
    exact le_trans hV (by linarith)
  have ht := LQGMetric.SupTail.tail_iSup_abs_le hG h0 (fun ω => continuous_const)
    (by simpa only [one_mul] using hint 1)
    (by simpa only [neg_one_mul] using hint (-1)) (M := 0)
    (by simp only [X, ciSup_const, (hh.hasGaussianLaw_sphereAvg_sub hd hr hρ z w).2,
      le_refl])
    (by simp only [X, ciSup_const, integral_neg,
      (hh.hasGaussianLaw_sphereAvg_sub hd hr hρ z w).2, neg_zero, le_refl]) hvar hA
  simpa only [X, ciSup_const, zero_add, Real.sq_sqrt hv] using ht

end HigherDimLQGMetric
