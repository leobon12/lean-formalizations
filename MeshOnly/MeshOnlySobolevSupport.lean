import MeshOnly.MeshOnlySobolevNash
import MeshOnly.MeshOnlySobolevSupportVolume

/-! The support-volume estimate following from the genuine geometric Nash
inequality, in a form directly compatible with Dirichlet energy bounds. -/

open scoped BigOperators Classical ENNReal MeasureTheory

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

theorem meshOnly_support_bound (hdim : 2 ≤ n + 1)
    (R : Set T.V) [Fintype R] (u : R → ℝ)
    (hmesh : T.mesh ≠ ∞)
    (hcell : ∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v : R, u v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R)
    (V : ℝ) (hV : 0 ≤ V)
    (hsupport : (∑ v : R, if u v ≠ 0 then (T.cell v).volume.toReal else 0) ≤ V) :
    (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) ≤
      (MeshOnlySobolev.nashConstant (n + 1) * V ^ (2 / ((n + 1 : ℕ) : ℝ)) +
        Real.sqrt (MeshOnlySobolev.nashConstant (n + 1)) *
          T.mesh.toReal * V ^ (1 / ((n + 1 : ℕ) : ℝ))) *
            (T.finiteNetwork R).energy u := by
  let d : ℝ := ((n + 1 : ℕ) : ℝ)
  let C := MeshOnlySobolev.nashConstant (n + 1)
  let X := ∑ v : R, (T.cell v).volume.toReal * u v ^ 2
  let A := ∑ v : R, (T.cell v).volume.toReal * |u v|
  let Q := (T.finiteNetwork R).energy u
  have hd : 0 < d := by dsimp [d]; positivity
  have hC : 0 ≤ C := (MeshOnlySobolev.nashConstant_pos hdim).le
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have hQ : 0 ≤ Q := (T.finiteNetwork R).energy_nonneg u
  have hε : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  have hAX : A ^ 2 ≤ V * X :=
    (MeshOnlySobolev.weighted_l1_sq_le_support_l2
      (fun v : R => (T.cell v).volume.toReal) u (fun _ => ENNReal.toReal_nonneg)).trans
      (mul_le_mul_of_nonneg_right hsupport hX)
  have hApow : A ^ (4 / d) ≤ V ^ (2 / d) * X ^ (2 / d) := by
    have h := Real.rpow_le_rpow (sq_nonneg A) hAX
      (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd.le)
    rw [← Real.rpow_two, ← Real.rpow_mul hA, Real.mul_rpow hV hX] at h
    have he : (2 : ℝ) * (2 / d) = 4 / d := by ring
    rwa [he] at h
  have hnash := T.meshOnly_defectiveNash hdim R u hmesh hcell hneighbors
  change X ^ (2 + 2 / d) ≤ C * A ^ (4 / d) * Q * (X + T.mesh.toReal ^ 2 * Q) at hnash
  have hquad : X ^ 2 ≤ C * V ^ (2 / d) * Q * (X + T.mesh.toReal ^ 2 * Q) := by
    by_cases hx0 : X = 0
    · norm_num only [hx0, zero_add] <;> positivity
    · have hx : 0 < X := hX.lt_of_ne' hx0
      apply le_of_mul_le_mul_left ?_ (Real.rpow_pos_of_pos hx (2 / d))
      have hmon := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hApow hC) hQ)
        (add_nonneg hX (mul_nonneg (sq_nonneg T.mesh.toReal) hQ))
      calc
        X ^ (2 / d) * X ^ 2 = X ^ (2 + 2 / d) := by
          rw [← Real.rpow_two, ← Real.rpow_add hx]
          congr 1
          ring
        _ ≤ C * A ^ (4 / d) * Q * (X + T.mesh.toReal ^ 2 * Q) := hnash
        _ ≤ C * (V ^ (2 / d) * X ^ (2 / d)) * Q * (X + T.mesh.toReal ^ 2 * Q) := hmon
        _ = _ := by ring
  let K := Real.sqrt C * V ^ (1 / d)
  have hK : 0 ≤ K := mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hV _)
  have hKsq : K ^ 2 = C * V ^ (2 / d) := by
    dsimp [K]
    rw [mul_pow, Real.sq_sqrt hC, ← Real.rpow_two, ← Real.rpow_mul hV]
    rw [show (1 / d) * 2 = 2 / d by ring]
  have hquad' : X ^ 2 ≤ K ^ 2 * Q * (X + T.mesh.toReal ^ 2 * Q) := by
    rwa [hKsq]
  have h := MeshOnlySobolev.support_bound_of_quadratic hX hQ hK hε hquad'
  rw [hKsq] at h
  dsimp [X, C, Q, K, d] at h ⊢
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end BouRabeeGwynne.OrthogonalTiling
