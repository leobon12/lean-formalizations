import HigherDimLQGMetric.Limits.CompareFamily
import HigherDimLQGMetric.Sec6.Defs
import HigherDimLQGMetric.Sec10.Perturb

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Topology Filter
namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The exact Weyl identity and boundedness of the perturbation yield the
uniform scale comparison in Remark 3.8(b). -/
theorem l6c_normalized_weyl_bdd_compare {d : ℕ}
    (hd : 1 ≤ d) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (h : DistRd d) (g : C(Rd d, ℝ)) (D Dg : ContMetric d)
    (hD : D.IsLength) (hW : IsWeylOf ξ g D Dg)
    (r c G : ℝ) (_hr : 0 < r) (hc : 0 < c)
    (hseq : Tendsto (sphereAvgSeq h r 0) atTop (𝓝 (sphereAvg h r 0)))
    (hG : ∀ x, |g x| ≤ G) (u v : Rd d) :
    Real.exp (-ξ * (2 * G)) *
      (normalizedAtScale ξ (fun _ => D) (fun _ => c) h r (u,v)) ≤
      normalizedAtScale ξ (fun _ => Dg) (fun _ => c) (addFun h g) r (u,v) ∧
    normalizedAtScale ξ (fun _ => Dg) (fun _ => c) (addFun h g) r (u,v) ≤
      Real.exp (ξ * (2 * G)) *
        (normalizedAtScale ξ (fun _ => D) (fun _ => c) h r (u,v)) := by
  have hmean : sphereAvg (addFun h g) r 0 =
      sphereAvg h r 0 + sphereAvg (ofCont g) r 0 := by
    rw [sphereAvg_addFun_of_tendsto hseq]
    exact congrArg (sphereAvg h r 0 + ·) (sphereAvg_ofCont g r 0).symm
  have hmeanbound : |sphereAvg (ofCont g) r 0| ≤ G :=
    s8a_abs_sphereAvg_ofCont_le hd g r G hG
  have hlow (x : Rd d) : -ξ * G ≤ ξ * g x := by
    have := (abs_le.mp (hG x)).1
    nlinarith
  have hupp (x : Rd d) : ξ * g x ≤ ξ * G := by
    have := (abs_le.mp (hG x)).2
    nlinarith
  have hraw := weylScale_mem_Icc_of_isLength (D := D) (z := r • u)
    (w := r • v) hD hlow hupp
  rw [← hW] at hraw
  have hrawlo : Real.exp (-ξ * G) * D.1 (r • u,r • v) ≤ Dg.1 (r • u,r • v) :=
    (ENNReal.ofReal_le_ofReal_iff (Dg.nonneg _ _)).mp hraw.1
  have hrawhi : Dg.1 (r • u,r • v) ≤ Real.exp (ξ * G) * D.1 (r • u,r • v) :=
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (Real.exp_pos _).le (D.nonneg _ _))).mp hraw.2
  have hmeanlo : -ξ * G ≤ -ξ * sphereAvg (ofCont g) r 0 := by
    have := (abs_le.mp hmeanbound).2
    nlinarith
  have hmeanhi : -ξ * sphereAvg (ofCont g) r 0 ≤ ξ * G := by
    have := (abs_le.mp hmeanbound).1
    nlinarith
  have hexplo : Real.exp (-ξ * G) ≤
      Real.exp (-ξ * sphereAvg (ofCont g) r 0) := Real.exp_le_exp.mpr hmeanlo
  have hexphi : Real.exp (-ξ * sphereAvg (ofCont g) r 0) ≤
      Real.exp (ξ * G) := Real.exp_le_exp.mpr hmeanhi
  let s : ℝ := c⁻¹ * Real.exp (-ξ * sphereAvg h r 0)
  have hs : 0 ≤ s := mul_nonneg (inv_nonneg.mpr hc.le) (Real.exp_pos _).le
  have hfactor : c⁻¹ * Real.exp (-ξ * (sphereAvg h r 0 + sphereAvg (ofCont g) r 0)) =
      s * Real.exp (-ξ * sphereAvg (ofCont g) r 0) := by
    dsimp [s]
    rw [mul_add, Real.exp_add]
    ring
  have hprodlo : Real.exp (-ξ * (2 * G)) * D.1 (r • u,r • v) ≤
      Real.exp (-ξ * sphereAvg (ofCont g) r 0) * Dg.1 (r • u,r • v) := by
    calc
      Real.exp (-ξ * (2 * G)) * D.1 (r • u,r • v) =
          Real.exp (-ξ * G) * (Real.exp (-ξ * G) * D.1 (r • u,r • v)) := by
            rw [show -ξ * (2 * G) = (-ξ * G) + (-ξ * G) by ring,
              Real.exp_add]
            ring
      _ ≤ Real.exp (-ξ * sphereAvg (ofCont g) r 0) * Dg.1 (r • u,r • v) := by
        exact mul_le_mul hexplo hrawlo
          (mul_nonneg (Real.exp_pos _).le (D.nonneg _ _)) (Real.exp_pos _).le
  have hprodhi : Real.exp (-ξ * sphereAvg (ofCont g) r 0) * Dg.1 (r • u,r • v) ≤
      Real.exp (ξ * (2 * G)) * D.1 (r • u,r • v) := by
    calc
      Real.exp (-ξ * sphereAvg (ofCont g) r 0) * Dg.1 (r • u,r • v) ≤
          Real.exp (ξ * G) * (Real.exp (ξ * G) * D.1 (r • u,r • v)) := by
            exact mul_le_mul hexphi hrawhi
              (Dg.nonneg _ _) (Real.exp_pos _).le
      _ = Real.exp (ξ * (2 * G)) * D.1 (r • u,r • v) := by
            rw [show ξ * (2 * G) = (ξ * G) + (ξ * G) by ring,
              Real.exp_add]
            ring
  simp only [normalizedAtScale, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, smul_eq_mul, hmean] at *
  rw [hfactor]
  constructor
  · calc
      Real.exp (-ξ * (2 * G)) * (s * D.1 (r • u,r • v)) =
          s * (Real.exp (-ξ * (2 * G)) * D.1 (r • u,r • v)) := by ring
      _ ≤ s * (Real.exp (-ξ * sphereAvg (ofCont g) r 0) * Dg.1 (r • u,r • v)) :=
        mul_le_mul_of_nonneg_left hprodlo hs
      _ = s * Real.exp (-ξ * sphereAvg (ofCont g) r 0) * Dg.1 (r • u,r • v) := by ring
  · calc
      s * Real.exp (-ξ * sphereAvg (ofCont g) r 0) * Dg.1 (r • u,r • v) =
          s * (Real.exp (-ξ * sphereAvg (ofCont g) r 0) * Dg.1 (r • u,r • v)) := by ring
      _ ≤ s * (Real.exp (ξ * (2 * G)) * D.1 (r • u,r • v)) :=
        mul_le_mul_of_nonneg_left hprodhi hs
      _ = Real.exp (ξ * (2 * G)) * (s * D.1 (r • u,r • v)) := by ring

end HigherDimLQGMetric
