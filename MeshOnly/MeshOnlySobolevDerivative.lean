import MeshOnly.MeshOnlySobolevMollification

/-! A pointwise derivative bound for genuine cellwise mollification. -/

open scoped BigOperators Classical ENNReal MeasureTheory Convolution
open MeasureTheory ContinuousLinearMap

namespace BouRabeeGwynne.MeshOnlySobolev

lemma norm_linearFunctional_le_sum_coordinates {n : ℕ}
    (L : Euc (n + 1) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i : Fin (n + 1), ‖L (coordinateAxis i)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro z
  have hrepr : (∑ i : Fin (n + 1), z i • coordinateAxis i) = z :=
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr z
  calc
    ‖L z‖ = ‖∑ i : Fin (n + 1), z i • L (coordinateAxis i)‖ := by
      conv_lhs => rw [← hrepr]
      rw [map_sum]
      simp only [map_smul]
    _ ≤ ∑ i : Fin (n + 1), ‖z i • L (coordinateAxis i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin (n + 1), ‖z‖ * ‖L (coordinateAxis i)‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z i) (norm_nonneg _)
    _ = (∑ i : Fin (n + 1), ‖L (coordinateAxis i)‖) * ‖z‖ := by
      rw [← Finset.mul_sum, mul_comm]

end BouRabeeGwynne.MeshOnlySobolev

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

noncomputable def meshOnlyContactKernel (ρ : Euc (n + 1) → ℝ)
    (x : Euc (n + 1)) (v w : T.V) : ℝ :=
  if T.adj v w then ∫ y in T.facet v w, ρ (x - y) ∂μHE[n] else 0

lemma meshOnlyContactKernel_nonneg (ρ : Euc (n + 1) → ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (x : Euc (n + 1)) (v w : T.V) :
    0 ≤ T.meshOnlyContactKernel ρ x v w := by
  unfold meshOnlyContactKernel
  split_ifs
  · exact integral_nonneg fun _ => hρ _
  · exact le_rfl

lemma abs_meshOnlyCoordinateContactFlux_le_kernel (i : Fin (n + 1))
    (ρ : Euc (n + 1) → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (x : Euc (n + 1)) (v w : T.V) :
    |T.meshOnlyCoordinateContactFlux i (fun y => ρ (x - y)) v w| ≤
      T.meshOnlyContactKernel ρ x v w := by
  by_cases hvw : T.adj v w
  · have hcoeff : |(T.pos w - T.pos v) i / ‖T.pos w - T.pos v‖| ≤ 1 := by
      rw [abs_div, abs_of_nonneg (norm_nonneg _)]
      apply (div_le_one (T.edge_norm_pos hvw)).mpr
      exact PiLp.norm_apply_le (T.pos w - T.pos v) i
    have hK := T.meshOnlyContactKernel_nonneg ρ hρ x v w
    simp only [meshOnlyCoordinateContactFlux, meshOnlyContactKernel, if_pos hvw] at *
    rw [integral_const_mul, abs_mul, abs_of_nonneg hK]
    simpa using mul_le_mul_of_nonneg_right hcoeff hK
  · simp [meshOnlyCoordinateContactFlux, meshOnlyContactKernel, hvw]

/-- The derivative is controlled by the actual facet convolution kernels
and coefficient jumps. The dimension constant comes solely from comparing
the Euclidean operator norm with the sum of its coordinate values. -/
theorem meshOnlyCellFunction_convolution_fderiv_bound
    (R : Set T.V) [Fintype R] (c : R → ℝ)
    (hcell : ∀ v : R, c v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v : R, c v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R)
    (ρ : Euc (n + 1) → ℝ) (hρ : ContDiff ℝ 1 ρ) (hcompact : HasCompactSupport ρ)
    (hnonneg : ∀ x, 0 ≤ ρ x) (x : Euc (n + 1)) :
    ‖fderiv ℝ (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) x‖ ≤
      ((n + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        T.meshOnlyContactKernel ρ x v w * |c w - c v|) := by
  have hcoord (i : Fin (n + 1)) :
      ‖(fderiv ℝ (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) x)
        (coordinateAxis i)‖ ≤
        (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
          T.meshOnlyContactKernel ρ x v w * |c w - c v| := by
    rw [T.meshOnlyCellFunction_convolution_partial_eq_jumps i R c hcell hneighbors
      ρ hρ hcompact x, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ∑ v : R, |∑ w : R,
          T.meshOnlyCoordinateContactFlux i (fun y => ρ (x - y)) v w * (c w - c v)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v : R, ∑ w : R,
          |T.meshOnlyCoordinateContactFlux i (fun y => ρ (x - y)) v w * (c w - c v)| :=
        Finset.sum_le_sum fun _ _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro v _
        apply Finset.sum_le_sum
        intro w _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (T.abs_meshOnlyCoordinateContactFlux_le_kernel i ρ hnonneg x v w) (abs_nonneg _)
  calc
    _ ≤ ∑ i : Fin (n + 1),
        ‖(fderiv ℝ (T.meshOnlyCellFunction R c ⋆[lsmul ℝ ℝ, volume] ρ) x)
          (coordinateAxis i)‖ := MeshOnlySobolev.norm_linearFunctional_le_sum_coordinates _
    _ ≤ ∑ _i : Fin (n + 1), (1 / 2 : ℝ) * ∑ v : R, ∑ w : R,
        T.meshOnlyContactKernel ρ x v w * |c w - c v| :=
      Finset.sum_le_sum fun i _ => hcoord i
    _ = _ := by simp

end BouRabeeGwynne.OrthogonalTiling
