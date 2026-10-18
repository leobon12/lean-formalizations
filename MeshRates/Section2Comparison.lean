import MeshOnly.MeshOnlySobolevNorms
import MeshOnly.MeshOnlySobolevJump

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal
open MeasureTheory

namespace BouRabeeGwynne.MeshRates

/-- MR (14): the auxiliary vertex measure `ν_v = ½ Σ_{e∋v} a(e)‖e‖²`, the sum running over the
neighbours of `v` inside the finite region `R`; it equals MR's `ν_v` whenever every neighbour of `v`
lies in `R`. -/
noncomputable def nuMass {d : ℕ} (T : OrthogonalTiling d) (R : Set T.V) [Fintype R] (v : R) : ℝ :=
  (1 / 2 : ℝ) * ∑ w : R, T.conductanceReal v w * ‖T.pos w - T.pos v‖ ^ 2

/-- MR Lemma 2.1, (15). Stated for every finite region `R`; for `R` containing the support of `u`
and its neighbours, the left side is MR's `Σ_v ν_v u(v)²` and the energy is MR's `D(u)`. -/
theorem lemma21_nu_le_tileL2_add_energy {d : ℕ} (hd : 1 ≤ d) (T : OrthogonalTiling d)
    (R : Set T.V) [Fintype R] (u : R → ℝ) (hmesh : T.mesh ≠ ∞) :
    ∑ v : R, nuMass T R v * u v ^ 2 ≤
      (3 * (d : ℝ) / 2) * (∑ v : R, (T.cell v).volume.toReal * u v ^ 2) +
        4 * T.mesh.toReal ^ 2 * (T.finiteNetwork R).energy u := by
  have hid : ∑ v : R, nuMass T R v * u v ^ 2 = (1 / 2 : ℝ) * ((d : ℝ) * T.meshOnlyDualL2Sq R u) := by
    simp only [nuMass, OrthogonalTiling.meshOnlyDualL2Sq,
      T.conductance_mul_edge_sq_eq_pyramidMass hd, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  rw [hid]
  have h := T.meshOnly_dualL2_le_tileL2_add_energy hd R u hmesh
  linarith

/-- MR Lemma 2.2, (17), with `q = 2d/(d-1)` from (16): `‖u‖²_{q,m} ≤ C_d D(u)^{1/2}(‖u‖²_{2,m} + ε²D(u))^{1/2}`
for finitely supported `u` satisfying (11); `C_d` depends only on `d`. -/
theorem lemma22_bvSobolev {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : OrthogonalTiling d) (R : Set T.V) [Fintype R] (u : R → ℝ),
      T.mesh ≠ ∞ →
      (∀ v : R, u v ≠ 0 → (T.cell v).carrier ⊆ interior T.domain) →
      (∀ v : R, u v ≠ 0 → ∀ w : T.V, T.adj v w → w ∈ R) →
      ((∑ v : R, (T.cell v).volume.toReal * |u v| ^ (2 * (d : ℝ) / ((d : ℝ) - 1))) ^
          (((d : ℝ) - 1) / (2 * (d : ℝ)))) ^ 2 ≤
        C * Real.sqrt ((T.finiteNetwork R).energy u) *
          Real.sqrt ((∑ v : R, (T.cell v).volume.toReal * u v ^ 2) +
            T.mesh.toReal ^ 2 * (T.finiteNetwork R).energy u) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  set p : ℝ := ((n : ℝ) + 1) / n with hpdef
  have hnpos : (0 : ℝ) < n := by linarith
  have hp : Real.HolderConjugate ((n + 1 : ℕ) : ℝ) p := by
    rw [Real.holderConjugate_iff]
    push_cast
    refine ⟨by linarith, ?_⟩
    rw [hpdef]; field_simp; ring
  have hp0 : 0 < p := by rw [hpdef]; positivity
  set K : ℝ := (lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc (n + 1))) p : ℝ)
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  refine ⟨K ^ (1 / p) * ((n : ℝ) + 1) * Real.sqrt (16 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro T R _ u hmesh hcell hnb
  have hsob := T.meshOnly_sobolev_real_square hp R u hcell hnb
  have hJ := T.meshOnly_squareJump_sq_le (by omega) R u hmesh
  have hJ0 := T.meshOnlySquareJump_nonneg R u
  have hE := (T.finiteNetwork R).energy_nonneg u
  set J := T.meshOnlySquareJump R u
  set E := (T.finiteNetwork R).energy u
  set M := ∑ v : R, (T.cell v).volume.toReal * u v ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun v _ =>
    mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  have hq : 2 * ((n + 1 : ℕ) : ℝ) / (((n + 1 : ℕ) : ℝ) - 1) = 2 * p := by
    rw [hpdef]; push_cast; rw [add_sub_cancel_right]; ring
  have hsum : (∑ v : R, (T.cell v).volume.toReal * |u v| ^ (2 * ((n + 1 : ℕ) : ℝ) /
      (((n + 1 : ℕ) : ℝ) - 1))) = ∑ v : R, (T.cell v).volume.toReal * (u v ^ 2) ^ p := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hq, Real.rpow_mul (abs_nonneg _), Real.rpow_two, sq_abs]
  set S := ∑ v : R, (T.cell v).volume.toReal * (u v ^ 2) ^ p
  have hS : 0 ≤ S := Finset.sum_nonneg fun v _ =>
    mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
  have hexp : (((n + 1 : ℕ) : ℝ) - 1) / (2 * ((n + 1 : ℕ) : ℝ)) * 2 = 1 / p := by
    rw [hpdef]; push_cast; field_simp; ring
  rw [hsum, ← Real.rpow_natCast, ← Real.rpow_mul hS, Nat.cast_ofNat, hexp]
  -- S^{1/p} ≤ K^{1/p} (d J)
  have h1 : S ^ (1 / p) ≤ K ^ (1 / p) * (((n + 1 : ℕ) : ℝ) * J) := by
    calc S ^ (1 / p) ≤ (K * (((n + 1 : ℕ) : ℝ) * J) ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow hS hsob (by positivity)
      _ = K ^ (1 / p) * (((n + 1 : ℕ) : ℝ) * J) := by
          rw [Real.mul_rpow hK (by positivity), ← Real.rpow_mul (by positivity),
            mul_one_div_cancel hp0.ne', Real.rpow_one]
  -- J ≤ √(16 d) √E √(M + ε² E)
  have h2 : J ≤ Real.sqrt (16 * ((n : ℝ) + 1)) * Real.sqrt E *
      Real.sqrt (M + T.mesh.toReal ^ 2 * E) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    refine hJ.trans ?_
    push_cast
    have hm2 : 0 ≤ T.mesh.toReal ^ 2 * E := by positivity
    nlinarith [mul_nonneg hE hM, mul_nonneg hE hm2, mul_nonneg hnpos.le hE]
  push_cast at h1
  calc S ^ (1 / p) ≤ K ^ (1 / p) * (((n : ℝ) + 1) * J) := h1
    _ ≤ K ^ (1 / p) * (((n : ℝ) + 1) * (Real.sqrt (16 * ((n : ℝ) + 1)) * Real.sqrt E *
      Real.sqrt (M + T.mesh.toReal ^ 2 * E))) := by gcongr
    _ = _ := by ring

end BouRabeeGwynne.MeshRates
