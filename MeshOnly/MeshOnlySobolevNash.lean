import MeshOnly.MeshOnlySobolevNorms
import MeshOnly.MeshOnlySobolevInterpolation

/-! The defective Nash inequality for actual orthogonal tilings, with one
constant chosen from the dimension before the tiling, mesh, or function. -/

open scoped BigOperators Classical ENNReal MeasureTheory
open MeasureTheory

namespace BouRabeeGwynne.MeshOnlySobolev

/-- A dimension-only constant, with slack to make positivity immediate. -/
noncomputable def nashConstant (d : ℕ) : ℝ :=
  (1 + (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc d))
    ((d : ℝ) / (d - 1)) : ℝ) ^ (2 / ((d : ℝ) / (d - 1)))) *
      (d : ℝ) ^ 2 * (6 * (d : ℝ) + 16)

lemma nashConstant_pos {d : ℕ} (hd : 2 ≤ d) : 0 < nashConstant d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold nashConstant
  positivity

end BouRabeeGwynne.MeshOnlySobolev

namespace BouRabeeGwynne.OrthogonalTiling

variable {n : ℕ} (T : OrthogonalTiling (n + 1))

/-- The actual geometric defective Nash estimate, including the L¹ factor.
All masses are primal-cell volumes and the energy is the same finite-network
energy as in the Dirichlet energy estimate and killed heat equation. -/
theorem meshOnly_defectiveNash (hdim : 2 ≤ n + 1)
    (R : Set T.V) [Fintype R] (u : R → ℝ)
    (hmesh : T.mesh ≠ ∞)
    (hcell : ∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v : R, u v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R) :
    (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) ^
        (2 + 2 / ((n + 1 : ℕ) : ℝ)) ≤
      MeshOnlySobolev.nashConstant (n + 1) *
        (∑ v : R, (T.cell v).volume.toReal * |u v|) ^ (4 / ((n + 1 : ℕ) : ℝ)) *
        (T.finiteNetwork R).energy u *
        ((∑ v : R, (T.cell v).volume.toReal * u v ^ 2) +
          T.mesh.toReal ^ 2 * (T.finiteNetwork R).energy u) := by
  let d : ℝ := ((n + 1 : ℕ) : ℝ)
  have hd : 1 < d := by dsimp [d]; exact_mod_cast (by omega : 1 < n + 1)
  have hd0 : 0 < d := by linarith
  have hd1 : 0 < d - 1 := by linarith
  let p : ℝ := d / (d - 1)
  have hp : Real.HolderConjugate d p :=
    (Real.holderConjugate_iff_eq_conjExponent hd).mpr rfl
  let C₀ : ℝ := lintegralPowLePowLIntegralFDerivConst
    (volume : Measure (Euc (n + 1))) p
  have hC₀ : 0 ≤ C₀ := NNReal.coe_nonneg _
  let X := ∑ v : R, (T.cell v).volume.toReal * u v ^ 2
  let A := ∑ v : R, (T.cell v).volume.toReal * |u v|
  let S := ∑ v : R, (T.cell v).volume.toReal * (u v ^ 2) ^ p
  let Q := (T.finiteNetwork R).energy u
  let J := T.meshOnlySquareJump R u
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
  have hQ : 0 ≤ Q := (T.finiteNetwork R).energy_nonneg u
  have hJ : 0 ≤ J := T.meshOnlySquareJump_nonneg R u
  have hs : S ≤ C₀ * (d * J) ^ p := T.meshOnly_sobolev_real_square hp R u hcell hneighbors
  have hpow := Real.rpow_le_rpow hS hs
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp.symm.nonneg)
  rw [Real.mul_rpow hC₀ (Real.rpow_nonneg (mul_nonneg hd0.le hJ) p),
    ← Real.rpow_mul (mul_nonneg hd0.le hJ)] at hpow
  have hep : p * (2 / p) = 2 := by field_simp [hp.symm.ne_zero]
  rw [hep, Real.rpow_two, mul_pow] at hpow
  have hj : J ^ 2 ≤ Q * (6 * d * X + 16 * T.mesh.toReal ^ 2 * Q) :=
    T.meshOnly_squareJump_sq_le (by omega) R u hmesh
  have hbase : S ^ (2 / p) ≤
      MeshOnlySobolev.nashConstant (n + 1) * Q * (X + T.mesh.toReal ^ 2 * Q) := by
    have hterm : 6 * d * X + 16 * T.mesh.toReal ^ 2 * Q ≤
        (6 * d + 16) * (X + T.mesh.toReal ^ 2 * Q) := by
      nlinarith only [hX, mul_nonneg hd0.le (mul_nonneg (sq_nonneg T.mesh.toReal) hQ)]
    have hcoeff : 0 ≤ C₀ ^ (2 / p) * d ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hC₀ _) (sq_nonneg _)
    have hstep := (mul_le_mul_of_nonneg_left hj hcoeff).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hterm hQ) hcoeff)
    have hslack : 0 ≤ d ^ 2 * (6 * d + 16) * Q * (X + T.mesh.toReal ^ 2 * Q) := by
      positivity
    dsimp [MeshOnlySobolev.nashConstant, d, p, C₀] at *
    nlinarith only [hpow, hstep, hslack]
  have heqS : (∑ v : R, (T.cell v).volume.toReal *
      |u v| ^ (2 * d / (d - 1))) = S := by
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    have he : 2 * d / (d - 1) = 2 * p := by dsimp [p]; ring
    rw [he, Real.rpow_mul (abs_nonneg (u v)), Real.rpow_two, sq_abs]
  have hinterp := MeshOnlySobolev.weighted_nash_interpolation
    (fun v : R => (T.cell v).volume.toReal) u
    (fun v => T.meshOnly_cellVolume_toReal_pos v) hd
  rw [heqS] at hinterp
  have he : 2 * (d - 1) / d = 2 / p := by
    dsimp [p]
    field_simp [hd0.ne', hd1.ne'] <;> ring
  rw [he] at hinterp
  have hfinal := hinterp.trans
    (mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hA _))
  dsimp [X, A, Q, d] at hfinal ⊢
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hfinal

/-- The same dimension-only Nash constant works for every upper bound on
the actual mesh, including a strictly positive regularization of a zero mesh. -/
theorem meshOnly_defectiveNash_of_mesh_le (hdim : 2 ≤ n + 1)
    (R : Set T.V) [Fintype R] (u : R → ℝ)
    (hmesh : T.mesh ≠ ∞)
    (hcell : ∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain)
    (hneighbors : ∀ v : R, u v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R)
    (ε : ℝ) (hbound : T.mesh.toReal ≤ ε) :
    (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) ^
        (2 + 2 / ((n + 1 : ℕ) : ℝ)) ≤
      MeshOnlySobolev.nashConstant (n + 1) *
        (∑ v : R, (T.cell v).volume.toReal * |u v|) ^ (4 / ((n + 1 : ℕ) : ℝ)) *
        (T.finiteNetwork R).energy u *
        ((∑ v : R, (T.cell v).volume.toReal * u v ^ 2) +
          ε ^ 2 * (T.finiteNetwork R).energy u) := by
  have hs : T.mesh.toReal ^ 2 ≤ ε ^ 2 := by
    nlinarith only [mul_self_le_mul_self ENNReal.toReal_nonneg hbound]
  apply (T.meshOnly_defectiveNash hdim R u hmesh hcell hneighbors).trans
  apply mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hs
      ((T.finiteNetwork R).energy_nonneg u)))
  exact mul_nonneg
    (mul_nonneg (MeshOnlySobolev.nashConstant_pos hdim).le
      (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ =>
        mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)) _))
    ((T.finiteNetwork R).energy_nonneg u)

end BouRabeeGwynne.OrthogonalTiling
