import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.G1
import LQGMetric.Statement.Field




 













set_option autoImplicit false

noncomputable section

open Complex Set Metric Real MeasureTheory
open scoped Pointwise

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 
def mollifier (ε : Set.Ioi (0 : ℝ)) : ContDiffBump (0 : ℂ) where
  rIn := (ε : ℝ) / 2
  rOut := ε
  rIn_pos := by have := ε.2; simp only [mem_Ioi] at this; positivity
  rIn_lt_rOut := by have := ε.2; simp only [mem_Ioi] at this; linarith

 
def mollInd (S : Set ℂ) (ε : Set.Ioi (0 : ℝ)) : ℂ → ℝ :=
  convolution ((mollifier ε).normed volume) (S.indicator (fun _ => (1 : ℝ)))
    (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem mollInd_apply (S : Set ℂ) (ε : Set.Ioi (0 : ℝ)) (y : ℂ) :
    mollInd S ε y = ∫ t, (mollifier ε).normed volume t * S.indicator (fun _ => (1 : ℝ)) (y - t) := by
  unfold mollInd
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

theorem mollInd_eq_one {S : Set ℂ} {ε : Set.Ioi (0 : ℝ)} {y : ℂ} (h : ball y ε ⊆ S) :
    mollInd S ε y = 1 := by
  have hy : y ∈ S := h (mem_ball_self ε.2)
  unfold mollInd
  rw [ContDiffBump.normed_convolution_eq_right (φ := mollifier ε)]
  · simp [hy]
  · intro x hx
    have hxS : x ∈ S := h hx
    simp [hxS, hy]

theorem mollInd_eq_zero {S : Set ℂ} {ε : Set.Ioi (0 : ℝ)} {y : ℂ} (h : Disjoint (ball y ε) S) :
    mollInd S ε y = 0 := by
  have hy : y ∉ S := fun hy => h.ne_of_mem (mem_ball_self ε.2) hy rfl
  unfold mollInd
  rw [ContDiffBump.normed_convolution_eq_right (φ := mollifier ε)]
  · simp [hy]
  · intro x hx
    have hxS : x ∉ S := fun hxS => h.ne_of_mem hx hxS rfl
    simp [hxS, hy]

theorem mollInd_nonneg (S : Set ℂ) (ε : Set.Ioi (0 : ℝ)) (y : ℂ) : 0 ≤ mollInd S ε y := by
  rw [mollInd_apply]
  apply integral_nonneg
  intro t
  apply mul_nonneg ((mollifier ε).nonneg_normed (μ := volume) t)
  apply Set.indicator_nonneg; intro _ _; norm_num

theorem mollInd_le_one (S : Set ℂ) (ε : Set.Ioi (0 : ℝ)) (y : ℂ) : mollInd S ε y ≤ 1 := by
  rw [mollInd_apply]
  have h1 : ∫ t, (mollifier ε).normed volume t = 1 := (mollifier ε).integral_normed
  calc ∫ t, (mollifier ε).normed volume t * S.indicator (fun _ => (1 : ℝ)) (y - t)
      ≤ ∫ t, (mollifier ε).normed volume t := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun t => mul_nonneg
            ((mollifier ε).nonneg_normed (μ := volume) t)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        · exact (mollifier ε).integrable_normed
        · refine Filter.Eventually.of_forall fun t => ?_
          have h0 := (mollifier ε).nonneg_normed (μ := volume) t
          have h2 : S.indicator (fun _ => (1 : ℝ)) (y - t) ≤ 1 :=
            Set.indicator_le_self' (fun _ _ => zero_le_one) _
          calc (mollifier ε).normed volume t * S.indicator (fun _ => (1 : ℝ)) (y - t)
              ≤ (mollifier ε).normed volume t * 1 := mul_le_mul_of_nonneg_left h2 h0
            _ = (mollifier ε).normed volume t := mul_one _
    _ = 1 := h1

theorem contDiff_mollInd {S : Set ℂ} (hS : MeasurableSet S) (ε : Set.Ioi (0 : ℝ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mollInd S ε) := by
  unfold mollInd
  apply HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (mollifier ε).hasCompactSupport_normed (mollifier ε).contDiff_normed
  exact (locallyIntegrable_const (1 : ℝ)).indicator hS

namespace TubeParams

variable {P : TubeParams} {r : ℝ}

 
def half' (A : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(A : ℝ) / 2, by have := A.2; simp only [mem_Ioi] at this ⊢; positivity⟩

def quarter' (A : Set.Ioi (0 : ℝ)) : Set.Ioi (0 : ℝ) :=
  ⟨(A : ℝ) / 4, by have := A.2; simp only [mem_Ioi] at this ⊢; positivity⟩

 
def bump (P : TubeParams) (r Amax : ℝ) (A : Set.Ioi (0 : ℝ)) (x : ℂ) : ℝ :=
  Amax * mollInd (thickening ((A : ℝ) / 2) (r⁻¹ • P.tube r)) (quarter' A) (r⁻¹ • x)

 
theorem bump_smul (hr : r ≠ 0) (Amax : ℝ) (A : Set.Ioi (0 : ℝ)) (y : ℂ) :
    P.bump r Amax A (r • y) =
      Amax * mollInd (thickening ((A : ℝ) / 2) (r⁻¹ • P.tube r)) (quarter' A) y := by
  unfold bump; rw [smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem contDiff_bump (Amax : ℝ) (A : Set.Ioi (0 : ℝ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.bump r Amax A) := by
  unfold bump
  apply contDiff_const.mul
  exact (contDiff_mollInd isOpen_thickening.measurableSet _).comp (contDiff_id.const_smul _)

theorem bump_nonneg {Amax : ℝ} (hAmax : 0 ≤ Amax) (A : Set.Ioi (0 : ℝ)) (x : ℂ) :
    0 ≤ P.bump r Amax A x := mul_nonneg hAmax (mollInd_nonneg _ _ _)

theorem bump_le {Amax : ℝ} (hAmax : 0 ≤ Amax) (A : Set.Ioi (0 : ℝ)) (x : ℂ) :
    P.bump r Amax A x ≤ Amax := by
  unfold bump
  have := mollInd_le_one (thickening ((A : ℝ) / 2) (r⁻¹ • P.tube r)) (quarter' A) (r⁻¹ • x)
  nlinarith [mollInd_nonneg (thickening ((A : ℝ) / 2) (r⁻¹ • P.tube r)) (quarter' A) (r⁻¹ • x)]

 
theorem bump_eq_of_mem_closure (Amax : ℝ) (A : Set.Ioi (0 : ℝ)) {x : ℂ}
    (hx : x ∈ closure (P.tube r)) : P.bump r Amax A x = Amax := by
  have hA : 0 < (A : ℝ) := A.2
  unfold bump
  rw [mollInd_eq_one, mul_one]
  have hx' : r⁻¹ • x ∈ closure (r⁻¹ • P.tube r) :=
    image_closure_subset_closure_image (continuous_const_smul r⁻¹) ⟨x, hx, rfl⟩
  intro z hz
  obtain ⟨u, hu, hxu⟩ := Metric.mem_closure_iff.mp hx' ((A : ℝ) / 4) (by positivity)
  rw [mem_thickening_iff]
  refine ⟨u, hu, ?_⟩
  have hz' : dist z (r⁻¹ • x) < (A : ℝ) / 4 := hz
  calc dist z u ≤ dist z (r⁻¹ • x) + dist (r⁻¹ • x) u := dist_triangle _ _ _
    _ < (A : ℝ) / 4 + (A : ℝ) / 4 := add_lt_add hz' hxu
    _ ≤ (A : ℝ) / 2 := by linarith

 
theorem bump_eq_zero (hr : 0 < r) (Amax : ℝ) (A : Set.Ioi (0 : ℝ)) {x : ℂ}
    (hx : x ∉ P.nbhd r A) : P.bump r Amax A x = 0 := by
  have hA : 0 < (A : ℝ) := A.2
  unfold bump
  rw [mollInd_eq_zero, mul_zero]
  rw [Set.disjoint_left]
  intro z hz hzt
  apply hx
  obtain ⟨v, hv, hzv⟩ := mem_thickening_iff.mp hzt
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hv
  have hz' : dist z (r⁻¹ • x) < (A : ℝ) / 4 := hz
  have h1 : dist (r⁻¹ • x) (r⁻¹ • u) < (A : ℝ) := by
    calc dist (r⁻¹ • x) (r⁻¹ • u) ≤ dist (r⁻¹ • x) z + dist z (r⁻¹ • u) := dist_triangle _ _ _
      _ < (A : ℝ) / 4 + (A : ℝ) / 2 := by rw [dist_comm] at hz'; exact add_lt_add hz' hzv
      _ ≤ A := by linarith
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)] at h1
  rw [nbhd, mem_thickening_iff]
  refine ⟨u, hu, ?_⟩
  rw [inv_mul_lt_iff₀ hr] at h1
  linarith

 
theorem nbhd_subset_ball (hP : P.Good) (hr : 0 < r) {A : ℝ} (hA : 100 * A ≤ P.sp * P.ρ) :
    P.nbhd r A ⊆ closedBall 0 (3 * r) := by
  intro x hx
  have := closure_nbhd_subset hP hr hA (subset_closure hx)
  rw [mem_closedBall, dist_zero_right]
  linarith [this.2]

theorem hasCompactSupport_bump (hP : P.Good) (hr : 0 < r) (Amax : ℝ) (A : Set.Ioi (0 : ℝ))
    (hA : 100 * (A : ℝ) ≤ P.sp * P.ρ) : HasCompactSupport (P.bump r Amax A) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (3 * r)) fun _x hx =>
    bump_eq_zero hr Amax A (fun hV => hx (nbhd_subset_ball hP hr hA hV))

 
def bumpTest (P : TubeParams) (r Amax : ℝ) (A : Set.Ioi (0 : ℝ)) (hP : P.Good) (hr : 0 < r)
    (hA : 100 * (A : ℝ) ≤ P.sp * P.ρ) : LQGMetric.TestC :=
  ⟨P.bump r Amax A, contDiff_bump Amax A, hasCompactSupport_bump hP hr Amax A hA, subset_univ _⟩

theorem bumpTest_apply (hP : P.Good) (hr : 0 < r) (Amax : ℝ) (A : Set.Ioi (0 : ℝ))
    (hA : 100 * (A : ℝ) ≤ P.sp * P.ρ) (x : ℂ) :
    P.bumpTest r Amax A hP hr hA x = P.bump r Amax A x := rfl

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
