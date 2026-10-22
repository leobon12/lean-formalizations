import HigherDimLQGMetric.Sec9.Interfaces
import HigherDimLQGMetric.Metric.ContMetric
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Claim (32), part 1: the choice of `ε` and the deterministic grid step (packet S8e)

Source: [S] §9, l. 1434–1475 (claim (32), (33), (34), the grid argument); MA4 Details (a) A17
and the global parameter order MA4 §1.7 (P5–P7); planning draft
`planning/drafts/S7b-S8-plan.md` §3 (S8e, steps 7–9).

* `s8e_tendsto_rpow`, `s8e_tendsto_const_mul_rpow`, `s8e_tendsto_const_mul_rpow_rpow`: real powers
  `C ε^a`, `C (ε^ν)^a` tend to `0` as `ε → 0⁺` (`a, ν > 0`).
* `s8e_exists_eps` (step P6): **one** `ε > 0` below the thresholds `ε₇` (Lemma 7.2) and `ε₁`
  (Proposition 8.6), below `1/3` (Lemma 8.1), with the grid separation `ε^ν ≤ 2β`, the modulus
  absorption `4 C_* (ε^ν)^α L ≤ (3/4) ε^{B+1}` (from `να > B + 1`), `t = C_* − βε^{B+1}/(4L) > 0`,
  and the four failure terms each `< p_*/5`.
* `s8e_rpow_grid`: `ε^{2νd+2} = ((ε^ν)^d)^2 ε^2`, the cancellation of the grid count against the
  Proposition 8.6 rate at `N = 2νd + 2` (MA4 E-P89-5).
* `s8e_norm_lt_three`, `s8e_norm_sub_le`, `s8e_sep`: rounding a point of `B̄_{2R}` to a grid point
  within `ε^ν R/8` keeps it in `B_{3R}`, within `ε^ν R` of the original, and keeps the separation
  `≥ βR/2` of two points at distance `≥ βR` when `ε^ν ≤ 2β`.
* `s8e_c1_of_near` (the triangle-inequality step of (32), [S] l. 1466–1472): if `D(x, y) ≤ β⁻¹ s`,
  `t D(x, y) < D̃(x, y)` with `C_* − t = βq/(4L)`, `s ≤ L S`, `D̃ ≤ C_* D`, and the rounding errors
  are `≤ δ s` with `4 C_* δ L ≤ (3/4) q`, then `C_* D(x′, y′) − q S ≤ D̃(x′, y′)`, i.e. (27) at the
  grid pair (`q = ε^{B+1}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-! ### Real powers near `0` -/

/-- `ε ^ a → 0` as `ε → 0⁺`, for a real exponent `a > 0`. -/
theorem s8e_tendsto_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => ε ^ a) (𝓝 0) (𝓝 ((0 : ℝ) ^ a)) :=
    (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- `C ε ^ a → 0` as `ε → 0⁺`, for a real exponent `a > 0`. -/
theorem s8e_tendsto_const_mul_rpow (C : ℝ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => C * ε ^ a) (𝓝[>] 0) (𝓝 0) := by
  simpa using (s8e_tendsto_rpow ha).const_mul C

/-- `C (ε ^ ν) ^ a → 0` as `ε → 0⁺`, for real exponents `ν, a > 0`. -/
theorem s8e_tendsto_const_mul_rpow_rpow (C : ℝ) {ν a : ℝ} (hν : 0 < ν) (ha : 0 < a) :
    Tendsto (fun ε : ℝ => C * (ε ^ ν) ^ a) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun u : ℝ => u ^ a) (𝓝 0) (𝓝 ((0 : ℝ) ^ a)) :=
    (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  have h2 : Tendsto (fun ε : ℝ => (ε ^ ν) ^ a) (𝓝[>] 0) (𝓝 0) :=
    h.comp (s8e_tendsto_rpow hν)
  simpa using h2.const_mul C

/-! ### The choice of `ε` (MA4 §1.7, P6) -/

/-- **Step P6**: one `ε` satisfying all the smallness conditions of the proof of (32) at once. The
constants are fixed before `ε`: `ε₇` (Lemma 7.2), `ε₁` (Proposition 8.6), `C_* = Cs`, `β`, `L`
((33)), `B` (Lemma 8.1), `ν`, `α` (with `να > B + 1`), the rates `a₈`, `a₂` and the prefactors
`C₇, C₈, C₂, K` of the four failure terms. -/
theorem s8e_exists_eps {ε₇ ε₁ Cs β L B ν α a₈ a₂ C₇ C₈ C₂ K pstar : ℝ}
    (hε₇ : 0 < ε₇) (hε₁ : 0 < ε₁) (hCs : 0 < Cs) (hβ : 0 < β) (hB : 0 < B)
    (hν : 0 < ν) (hνα : B + 1 < ν * α) (ha₈ : 0 < a₈) (ha₂ : 0 < a₂) (hpstar : 0 < pstar) :
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₇ ∧ ε < ε₁ ∧ ε < 1 / 3 ∧ ε ^ ν ≤ 2 * β ∧
      4 * Cs * (ε ^ ν) ^ α * L ≤ 3 / 4 * ε ^ (B + 1) ∧
      β * ε ^ (B + 1) / (4 * L) < Cs ∧
      C₇ * ε < pstar / 5 ∧ C₈ * ε ^ a₈ < pstar / 5 ∧ C₂ * (ε ^ ν) ^ a₂ < pstar / 5 ∧
      K * ε ^ (2 : ℝ) < pstar / 5 := by
  have e0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  have elt : ∀ {c : ℝ}, 0 < c → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < c := fun hc =>
    nhdsWithin_le_nhds (Iio_mem_nhds hc)
  have hp5 : 0 < pstar / 5 := by positivity
  have e5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ ν < 2 * β :=
    (tendsto_order.1 (s8e_tendsto_rpow hν)).2 _ (by positivity)
  have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 4 * Cs * L * ε ^ (ν * α - (B + 1)) < 3 / 4 :=
    (tendsto_order.1 (s8e_tendsto_const_mul_rpow (4 * Cs * L) (by linarith))).2 _
      (by norm_num)
  have e7 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), β / (4 * L) * ε ^ (B + 1) < Cs :=
    (tendsto_order.1 (s8e_tendsto_const_mul_rpow (β / (4 * L)) (by linarith))).2 _ hCs
  have e8 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C₇ * ε ^ (1 : ℝ) < pstar / 5 :=
    (tendsto_order.1 (s8e_tendsto_const_mul_rpow C₇ one_pos)).2 _ hp5
  have e9 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C₈ * ε ^ a₈ < pstar / 5 :=
    (tendsto_order.1 (s8e_tendsto_const_mul_rpow C₈ ha₈)).2 _ hp5
  have e10 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C₂ * (ε ^ ν) ^ a₂ < pstar / 5 :=
    (tendsto_order.1 (s8e_tendsto_const_mul_rpow_rpow C₂ hν ha₂)).2 _ hp5
  have e11 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), K * ε ^ (2 : ℝ) < pstar / 5 :=
    (tendsto_order.1 (s8e_tendsto_const_mul_rpow K two_pos)).2 _ hp5
  obtain ⟨ε, h0, h7, h1, h3, h5, h6, ht, h8, h9, h10, h11⟩ :=
    (e0.and ((elt hε₇).and ((elt hε₁).and ((elt (by norm_num : (0 : ℝ) < 1 / 3)).and
      (e5.and (e6.and (e7.and (e8.and (e9.and (e10.and e11)))))))))).exists
  refine ⟨ε, h0, h7, h1, h3, h5.le, ?_, ?_, ?_, h9, h10, h11⟩
  · have hsplit : (ε ^ ν) ^ α = ε ^ (B + 1) * ε ^ (ν * α - (B + 1)) := by
      rw [← Real.rpow_mul h0.le, ← Real.rpow_add h0]
      congr 1
      ring
    have hpos : 0 < ε ^ (B + 1) := Real.rpow_pos_of_pos h0 _
    rw [hsplit]
    calc 4 * Cs * (ε ^ (B + 1) * ε ^ (ν * α - (B + 1))) * L
        = (4 * Cs * L * ε ^ (ν * α - (B + 1))) * ε ^ (B + 1) := by ring
      _ ≤ 3 / 4 * ε ^ (B + 1) := mul_le_mul_of_nonneg_right h6.le hpos.le
  · have heq : β * ε ^ (B + 1) / (4 * L) = β / (4 * L) * ε ^ (B + 1) := by ring
    rw [heq]
    exact ht
  · simpa [Real.rpow_one] using h8

/-- The grid count cancels against the Proposition 8.6 rate at `N = 2νd + 2`:
`ε ^ (2νd + 2) = ((ε ^ ν) ^ d) ^ 2 · ε ^ 2` (MA4 E-P89-5). -/
theorem s8e_rpow_grid {ε : ℝ} (hε : 0 < ε) (ν : ℝ) (d : ℕ) :
    ε ^ (2 * ν * d + 2) = ((ε ^ ν) ^ d) ^ 2 * ε ^ (2 : ℝ) := by
  have h1 : (ε ^ ν) ^ d = ε ^ (ν * d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
  rw [h1, sq, ← Real.rpow_add hε, ← Real.rpow_add hε]
  congr 1
  ring

/-! ### Grid rounding -/

/-- A grid point within `eR/8` of a point of `B̄_{2R}` lies in `B_{3R}` (`e ≤ 1`). -/
theorem s8e_norm_lt_three {R e : ℝ} {x x' : Rd d} (hR : 0 < R) (he1 : e ≤ 1)
    (hx : ‖x‖ ≤ 2 * R) (hxx' : ‖x - x'‖ ≤ e * R / 8) : ‖x'‖ < 3 * R := by
  have h1 : ‖x'‖ ≤ ‖x‖ + ‖x - x'‖ := by
    have h := norm_sub_le x (x - x')
    rwa [sub_sub_cancel] at h
  have h2 : e * R ≤ R := by nlinarith
  linarith

/-- A grid point within `eR/8` is within `eR` (`R > 0`, `e > 0`). -/
theorem s8e_norm_sub_le {R e : ℝ} {x x' : Rd d} (hR : 0 < R) (he : 0 < e)
    (hxx' : ‖x - x'‖ ≤ e * R / 8) : ‖x - x'‖ ≤ e * R := by
  have : 0 < e * R := mul_pos he hR
  linarith

/-- Rounding both endpoints by at most `eR/8`, with `e ≤ 2β`, keeps the separation `≥ (β/2)R`. -/
theorem s8e_sep {R e β : ℝ} {x y x' y' : Rd d} (hR : 0 < R) (he : e ≤ 2 * β)
    (hxy : β * R ≤ ‖x - y‖) (hxx' : ‖x - x'‖ ≤ e * R / 8) (hyy' : ‖y - y'‖ ≤ e * R / 8) :
    β / 2 * R ≤ ‖x' - y'‖ := by
  have h : ‖x - y‖ ≤ ‖x - x'‖ + ‖x' - y'‖ + ‖y' - y‖ := by
    have heq : x - y = (x - x') + (x' - y') + (y' - y) := by abel
    rw [heq]
    exact norm_add₃_le
  rw [norm_sub_rev y' y] at h
  have h2 : e * R ≤ 2 * β * R := mul_le_mul_of_nonneg_right he hR.le
  nlinarith

/-! ### The deterministic step of (32) -/

/-- **The triangle-inequality step of (32)** ([S] l. 1466–1472, MA4 A17). Let `D, D̃` be continuous
metrics with `D̃ ≤ C_* D`. If the witness pair `(x, y)` satisfies `D(x, y) ≤ β⁻¹ s` and
`t D(x, y) < D̃(x, y)` with `C_* − t = βq/(4L)`, the macro-normalizer bound `s ≤ L S` holds, and the
rounded endpoints satisfy `D(x, x′), D(y, y′) ≤ δ s` with `4 C_* δ L ≤ (3/4) q`, then the grid pair
satisfies (27): `C_* D(x′, y′) − q S ≤ D̃(x′, y′)`. -/
theorem s8e_c1_of_near {D Dt : ContMetric d} {Cs t β L S s q δ : ℝ} {x y x' y' : Rd d}
    (hCs : 0 ≤ Cs) (hβ : 0 < β) (hL : 0 < L) (hS : 0 ≤ S) (hq : 0 ≤ q) (hδ0 : 0 ≤ δ)
    (hcomp : ∀ u v : Rd d, Dt.1 (u, v) ≤ Cs * D.1 (u, v))
    (ht : Cs - t = β * q / (4 * L))
    (hDxy : D.1 (x, y) ≤ β⁻¹ * s) (hrat : t * D.1 (x, y) < Dt.1 (x, y))
    (hsL : s ≤ L * S)
    (hxx' : D.1 (x, x') ≤ δ * s) (hyy' : D.1 (y, y') ≤ δ * s)
    (hδ : 4 * Cs * δ * L ≤ 3 / 4 * q) :
    Cs * D.1 (x', y') - q * S ≤ Dt.1 (x', y') := by
  -- triangle inequalities
  have hT1 : Dt.1 (x, y) ≤ Dt.1 (x, x') + Dt.1 (x', y') + Dt.1 (y', y) := by
    have h1 := Dt.apply_triangle x x' y
    have h2 := Dt.apply_triangle x' y' y
    linarith
  have hT2 : D.1 (x', y') ≤ D.1 (x, x') + D.1 (x, y) + D.1 (y, y') := by
    have h1 := D.apply_triangle x' x y'
    have h2 := D.apply_triangle x y y'
    rw [D.apply_comm x' x] at h1
    linarith
  have hc1 := hcomp x x'
  have hc2 := hcomp y' y
  rw [D.apply_comm y' y] at hc2
  -- the additive gap at the witness pair: `< q S / 4`
  have hgap : Cs * D.1 (x, y) - Dt.1 (x, y) ≤ q * S / 4 := by
    have h1 : Cs * D.1 (x, y) - Dt.1 (x, y) ≤ (Cs - t) * D.1 (x, y) := by
      have := hrat.le
      linarith
    have h2 : (Cs - t) * D.1 (x, y) ≤ β * q / (4 * L) * (β⁻¹ * s) := by
      rw [ht]
      exact mul_le_mul_of_nonneg_left hDxy (by positivity)
    have h3 : β * q / (4 * L) * (β⁻¹ * s) = q * s / (4 * L) := by
      field_simp
    have h4 : q * s / (4 * L) ≤ q * S / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hsL hq
      nlinarith
    linarith
  -- the rounding errors: `≤ (3/4) q S`
  have hmod : 2 * Cs * (D.1 (x, x') + D.1 (y, y')) ≤ 3 / 4 * q * S := by
    have h1 : D.1 (x, x') + D.1 (y, y') ≤ 2 * δ * (L * S) := by
      have : δ * s ≤ δ * (L * S) := mul_le_mul_of_nonneg_left hsL hδ0
      linarith
    calc 2 * Cs * (D.1 (x, x') + D.1 (y, y')) ≤ 2 * Cs * (2 * δ * (L * S)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (4 * Cs * δ * L) * S := by ring
      _ ≤ (3 / 4 * q) * S := mul_le_mul_of_nonneg_right hδ hS
      _ = 3 / 4 * q * S := by ring
  have hT2' : Cs * D.1 (x', y') ≤ Cs * (D.1 (x, x') + D.1 (x, y) + D.1 (y, y')) :=
    mul_le_mul_of_nonneg_left hT2 hCs
  nlinarith

end HigherDimLQGMetric
