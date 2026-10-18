import MeshOnly.MeshOnlySobolevSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal NNReal

namespace BouRabeeGwynne.MeshRates

open Classical in
/-- MR Proposition 2.3: the defective Nash inequality (21) and the support inequality (23), with
`V_u = Σ_{u(v) ≠ 0} m_v` from (22); `C_d` depends only on `d`. Finitely supported `u` satisfying (11),
on a finite region `R` containing the support and its neighbours. -/
theorem prop23_defectiveNash_and_support {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : OrthogonalTiling d) (R : Set T.V) [Fintype R] (u : R → ℝ),
      T.mesh ≠ ∞ →
      (∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain) →
      (∀ v : R, u v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R) →
      (Real.sqrt (∑ v : R, (T.cell v).volume.toReal * u v ^ 2)) ^ (4 + 4 / (d : ℝ)) ≤
          C * (∑ v : R, (T.cell v).volume.toReal * |u v|) ^ (4 / (d : ℝ)) *
            (T.finiteNetwork R).energy u *
              ((∑ v : R, (T.cell v).volume.toReal * u v ^ 2) +
                T.mesh.toReal ^ 2 * (T.finiteNetwork R).energy u) ∧
      (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) ≤
          C * ((∑ v : R, if u v ≠ 0 then (T.cell v).volume.toReal else 0) ^ (2 / (d : ℝ)) +
            T.mesh.toReal *
              (∑ v : R, if u v ≠ 0 then (T.cell v).volume.toReal else 0) ^ (1 / (d : ℝ))) *
            (T.finiteNetwork R).energy u := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  set K := MeshOnlySobolev.nashConstant (n + 1)
  have hK : 0 ≤ K := (MeshOnlySobolev.nashConstant_pos hd).le
  refine ⟨K + Real.sqrt K, by positivity, ?_⟩
  intro T R _ u hmesh hcell hnb
  set X := ∑ v : R, (T.cell v).volume.toReal * u v ^ 2
  set A := ∑ v : R, (T.cell v).volume.toReal * |u v|
  set Q := (T.finiteNetwork R).energy u
  set V := ∑ v : R, if u v ≠ 0 then (T.cell v).volume.toReal else 0
  have hX : 0 ≤ X := Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ =>
    mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)
  have hQ : 0 ≤ Q := (T.finiteNetwork R).energy_nonneg u
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
  have hε : 0 ≤ T.mesh.toReal := ENNReal.toReal_nonneg
  have hs : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  constructor
  · have hN := T.meshOnly_defectiveNash_of_mesh_le hd R u hmesh hcell hnb _ le_rfl
    have hsq : Real.sqrt X ^ (4 + 4 / ((n + 1 : ℕ) : ℝ)) = X ^ (2 + 2 / ((n + 1 : ℕ) : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX]; congr 1; ring
    rw [hsq]
    refine hN.trans ?_
    have h1 : 0 ≤ A ^ (4 / ((n + 1 : ℕ) : ℝ)) * Q * (X + T.mesh.toReal ^ 2 * Q) := by
      have := Real.rpow_nonneg hA (4 / ((n + 1 : ℕ) : ℝ)); positivity
    nlinarith
  · have hS := T.meshOnly_support_bound hd R u hmesh hcell hnb V hV le_rfl
    refine hS.trans (mul_le_mul_of_nonneg_right ?_ hQ)
    have a := Real.rpow_nonneg hV (2 / ((n + 1 : ℕ) : ℝ))
    have b := Real.rpow_nonneg hV (1 / ((n + 1 : ℕ) : ℝ))
    have c : 0 ≤ T.mesh.toReal * V ^ (1 / ((n + 1 : ℕ) : ℝ)) := mul_nonneg hε b
    nlinarith [mul_nonneg hK c, mul_nonneg hs a]

end BouRabeeGwynne.MeshRates
