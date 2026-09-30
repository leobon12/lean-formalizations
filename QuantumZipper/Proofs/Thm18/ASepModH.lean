import QuantumZipper.Proofs.Thm18.ASepModG
import QuantumZipper.Proofs.Thm18.ASepModB
import QuantumZipper.Proofs.Zipper.GenUCKolm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod H): the joint Hölder modulus of `muA0` and `GenFam`

`energy_muA0_joint`: `|E(muA0 p ρ − muA0 p' ρ')| ≤ K (dist p p' + |ρ − ρ'|)^c` on
`([0,T] × [a₀,a₁]) × [0,1]`, by the interpolation of XFLOW-E1 / D33 (`D = dist p p' + |ρ − ρ'|`,
`r₀ = D^{α/48}`): radii `≥ r₀` by the mixture modulus (`energy_muA0_large`, constants
`timeK, spaceK ≤ · / r₀²`), otherwise the triangle bound through radius `0`
(`energy_muA0_small`), and a uniform bound for `D ≥ 1/2`.

`genFam_muA0`: the family `muA0 W d r` satisfies `GenFam` on any parameter set inside the box.
Own bookkeeping (as `F1.flowE1Stmt_holds`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

open RegCont RegUnif B2 Thm18Asm.G4Core GenUC

theorem abs_coord_sub_le_dist (p p' : Fin 2 → ℝ) (i : Fin 2) : |p i - p' i| ≤ dist p p' := by
  have := dist_le_pi_dist p p' i
  rwa [Real.dist_eq] at this

/-- Arithmetic of the large-radius regime. -/
theorem large_arith {E tK sK Kt Ks r₀ D α c CΛ Λ τd : ℝ}
    (hE : E ≤ 2 * (tK * τd ^ (α / 12)) + 2 * (sK * Λ ^ (1 / 12 : ℝ)))
    (hTK : tK * r₀ ^ 2 ≤ Kt) (hSK : sK * r₀ ^ 2 ≤ Ks) (hr₀ : r₀ = D ^ (α / 48))
    (hDpos : 0 < D) (hD1 : D ≤ 1) (hα : 0 < α) (hτd : 0 ≤ τd) (hτD : τd ≤ D) (hΛ0 : 0 ≤ Λ)
    (hΛ : Λ ≤ CΛ * D ^ α) (hCΛ0 : 0 ≤ CΛ) (hc0 : 0 < c) (hc : c ≤ α / 24) :
    E ≤ (2 * |Kt| + 2 * |Ks| * CΛ ^ (1 / 12 : ℝ)) * D ^ c := by
  have hD0 := hDpos.le
  have hr₀p : 0 < r₀ := by rw [hr₀]; exact Real.rpow_pos_of_pos hDpos _
  have hr2 : 0 < r₀ ^ 2 := by positivity
  have hTK' : tK ≤ |Kt| / r₀ ^ 2 := by rw [le_div_iff₀ hr2]; exact hTK.trans (le_abs_self _)
  have hSK' : sK ≤ |Ks| / r₀ ^ 2 := by rw [le_div_iff₀ hr2]; exact hSK.trans (le_abs_self _)
  have hpow1 : Λ ^ (1 / 12 : ℝ) ≤ CΛ ^ (1 / 12 : ℝ) * D ^ (α / 12) := by
    refine (Real.rpow_le_rpow hΛ0 hΛ (by norm_num)).trans (le_of_eq ?_)
    rw [Real.mul_rpow hCΛ0 (Real.rpow_nonneg hD0 _), ← Real.rpow_mul hD0,
      show α * (1 / 12 : ℝ) = α / 12 by ring]
  have hpow2 : τd ^ (α / 12) ≤ D ^ (α / 12) := Real.rpow_le_rpow hτd hτD (by positivity)
  have hr₀sq : r₀ ^ 2 = D ^ (α / 24) := by
    rw [hr₀, ← Real.rpow_natCast, ← Real.rpow_mul hD0,
      show α / 48 * ((2 : ℕ) : ℝ) = α / 24 by push_cast; ring]
  have hquot : D ^ (α / 12) / r₀ ^ 2 = D ^ (α / 24) := by
    rw [hr₀sq, ← Real.rpow_sub hDpos, show α / 12 - α / 24 = α / 24 by ring]
  have hq24 : D ^ (α / 24) ≤ D ^ c :=
    Real.rpow_le_rpow_of_exponent_ge' hD0 hD1 hc0.le hc
  have g1 : tK * τd ^ (α / 12) ≤ |Kt| * D ^ (α / 24) := by
    calc tK * τd ^ (α / 12) ≤ |Kt| / r₀ ^ 2 * τd ^ (α / 12) :=
          mul_le_mul_of_nonneg_right hTK' (Real.rpow_nonneg hτd _)
      _ ≤ |Kt| / r₀ ^ 2 * D ^ (α / 12) := mul_le_mul_of_nonneg_left hpow2 (by positivity)
      _ = |Kt| * D ^ (α / 24) := by rw [← hquot]; ring
  have g2 : sK * Λ ^ (1 / 12 : ℝ) ≤ |Ks| * CΛ ^ (1 / 12 : ℝ) * D ^ (α / 24) := by
    calc sK * Λ ^ (1 / 12 : ℝ) ≤ |Ks| / r₀ ^ 2 * Λ ^ (1 / 12 : ℝ) :=
          mul_le_mul_of_nonneg_right hSK' (Real.rpow_nonneg hΛ0 _)
      _ ≤ |Ks| / r₀ ^ 2 * (CΛ ^ (1 / 12 : ℝ) * D ^ (α / 12)) :=
          mul_le_mul_of_nonneg_left hpow1 (by positivity)
      _ = |Ks| * CΛ ^ (1 / 12 : ℝ) * D ^ (α / 24) := by rw [← hquot]; ring
  have hK0 : 0 ≤ 2 * |Kt| + 2 * |Ks| * CΛ ^ (1 / 12 : ℝ) := by positivity
  have h3 := mul_le_mul_of_nonneg_left hq24 hK0
  have e : 2 * (|Kt| * D ^ (α / 24)) + 2 * (|Ks| * CΛ ^ (1 / 12 : ℝ) * D ^ (α / 24)) =
      (2 * |Kt| + 2 * |Ks| * CΛ ^ (1 / 12 : ℝ)) * D ^ (α / 24) := by ring
  linarith only [hE, g1, g2, h3, e]

/-- Arithmetic of the small-radius regime. -/
theorem small_arith {E M₀ C₀ b Dd ρ ρ' D r₀ α c ad : ℝ}
    (hE : E ≤ 2 * (M₀ * ρ ^ (1 / 4 : ℝ)) + 4 * (C₀ * (ad * Dd) ^ b) + 4 * (M₀ * ρ' ^ (1 / 4 : ℝ)))
    (hM₀ : 0 ≤ M₀) (hC₀ : 0 ≤ C₀) (hb : 0 < b) (hDd0 : 0 ≤ Dd) (hρ0 : 0 ≤ ρ) (hρ'0 : 0 ≤ ρ')
    (hρ2 : ρ ≤ 2 * r₀) (hρ'2 : ρ' ≤ 2 * r₀) (hr₀ : r₀ = D ^ (α / 48)) (hDpos : 0 < D)
    (hD1 : D ≤ 1) (had0 : 0 ≤ ad) (hadD : ad ≤ D) (hc0 : 0 < c) (hcα : c ≤ α / 192)
    (hcb : c ≤ b) :
    E ≤ (6 * M₀ * 2 ^ (1 / 4 : ℝ) + 4 * C₀ * Dd ^ b) * D ^ c := by
  have hD0 := hDpos.le
  have hr₀0 : 0 ≤ r₀ := by rw [hr₀]; exact Real.rpow_nonneg hD0 _
  have hr4 : (2 * r₀) ^ (1 / 4 : ℝ) = 2 ^ (1 / 4 : ℝ) * D ^ (α / 192) := by
    rw [Real.mul_rpow (by norm_num) hr₀0, hr₀, ← Real.rpow_mul hD0,
      show α / 48 * (1 / 4 : ℝ) = α / 192 by ring]
  have hρ4 : ∀ s : ℝ, 0 ≤ s → s ≤ 2 * r₀ → s ^ (1 / 4 : ℝ) ≤ 2 ^ (1 / 4 : ℝ) * D ^ c := by
    intro s hs hs2
    refine (Real.rpow_le_rpow hs hs2 (by norm_num)).trans ?_
    rw [hr4]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge' hD0 hD1 hc0.le hcα) (by positivity)
  have hbD : (ad * Dd) ^ b ≤ Dd ^ b * D ^ c := by
    calc (ad * Dd) ^ b ≤ (D * Dd) ^ b :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hadD hDd0) hb.le
      _ = D ^ b * Dd ^ b := Real.mul_rpow hD0 hDd0
      _ ≤ D ^ c * Dd ^ b := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_ge' hD0 hD1 hc0.le hcb) (by positivity)
      _ = Dd ^ b * D ^ c := by ring
  have e1 := mul_le_mul_of_nonneg_left (hρ4 ρ hρ0 hρ2) hM₀
  have e2 := mul_le_mul_of_nonneg_left (hρ4 ρ' hρ'0 hρ'2) hM₀
  have e3 := mul_le_mul_of_nonneg_left hbD hC₀
  have e : (6 * M₀ * 2 ^ (1 / 4 : ℝ) + 4 * C₀ * Dd ^ b) * D ^ c =
      6 * (M₀ * (2 ^ (1 / 4 : ℝ) * D ^ c)) + 4 * (C₀ * (Dd ^ b * D ^ c)) := by ring
  linarith only [hE, e1, e2, e3, e]

end ASep
end QuantumZipper
