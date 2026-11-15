/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Stochastic.Bessel.Comparison
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Bessel paths: the solution concept and pathwise uniqueness

Packet PROVE-BESSEL. Specification p. 19, (2.1)–(2.2): for `δ > 1` the Bessel process is the
nonnegative, instantaneously reflecting solution of

  `X_t = x + B_t + ∫₀ᵗ (δ - 1) / (2 X_s) ds`

(the zero set has Lebesgue measure zero and the integral is finite). With `c = (δ - 1)/2 > 0`,
`IsBesselPath c x b X` says that the path `X : ℝ≥0 → ℝ` is continuous, nonnegative, its zero set is
Lebesgue-null, `X⁻¹` is integrable on every `[0, t]`, and `X t = x + b t + ∫₀ᵗ c / X s ds` for all `t`
(time integrals are interval integrals over `ℝ` of `s ↦ f s.toNNReal`, as in `IsIntegratedSLEPath`).

* `IsBesselPath.le` — **comparison**: if `c ≤ c'` and `x ≤ x'`, a Bessel path with `(c, x)` lies below
  the one with `(c', x')` driven by the same `b`.
* `IsBesselPath.eq` — **pathwise uniqueness**: two Bessel paths with the same `(c, x, b)` coincide.

Both are deterministic: `X - Y = (x - x') + ∫ (c / X - c' / Y)` and where `X > Y > 0` the integrand is
negative, so the comparison principle `le_of_sub_eq_integral` applies (the drift `c / x` is decreasing).
This is the uniqueness half of "standard facts about Bessel processes" in the proof of Theorem 2.2
(p. 21) for one force point.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

noncomputable section

namespace InteractingSLE

namespace Bessel

/-- `X` is a **Bessel path** with drift coefficient `c` (dimension `δ = 1 + 2c`), initial value `x`
and driving path `b` (Specification (2.2), p. 19): continuous, nonnegative, instantaneously reflecting
(Lebesgue-null zero set), with locally integrable reciprocal, and
`X t = x + b t + ∫₀ᵗ c / X s ds` for every `t`. -/
def IsBesselPath (c x : ℝ) (b X : ℝ≥0 → ℝ) : Prop :=
  Continuous X ∧ (∀ t, 0 ≤ X t) ∧ volume {s : ℝ | 0 ≤ s ∧ X s.toNNReal = 0} = 0 ∧
    (∀ t : ℝ≥0, IntervalIntegrable (fun s : ℝ => (X s.toNNReal)⁻¹) volume 0 t) ∧
    ∀ t : ℝ≥0, X t = x + b t + ∫ s in (0 : ℝ)..t, c / X s.toNNReal

variable {c c' x x' : ℝ} {b X Y : ℝ≥0 → ℝ}

theorem IsBesselPath.continuous_real (h : IsBesselPath c x b X) :
    Continuous fun s : ℝ => X s.toNNReal :=
  h.1.comp continuous_real_toNNReal

theorem IsBesselPath.intervalIntegrable_div (h : IsBesselPath c x b X) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => c / X s.toNNReal) volume 0 t := by
  have := (h.2.2.2.1 t).const_mul c
  simpa [div_eq_mul_inv] using this

theorem IsBesselPath.ae_pos (h : IsBesselPath c x b X) :
    ∀ᵐ s : ℝ ∂volume, 0 ≤ s → 0 < X s.toNNReal := by
  have h0 : ∀ᵐ s : ℝ ∂volume, s ∉ {s : ℝ | 0 ≤ s ∧ X s.toNNReal = 0} :=
    measure_eq_zero_iff_ae_notMem.1 h.2.2.1
  filter_upwards [h0] with s hs hs0
  rcases (h.2.1 s.toNNReal).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd ⟨hs0, heq.symm⟩ hs

/-- **Comparison of Bessel paths** driven by the same path. -/
theorem IsBesselPath.le (hc : 0 < c) (hcc : c ≤ c') (hxx : x ≤ x') (hX : IsBesselPath c x b X)
    (hY : IsBesselPath c' x' b Y) (t : ℝ≥0) : X t ≤ Y t := by
  have key := le_of_sub_eq_integral (T := t) (X := fun s : ℝ => X s.toNNReal)
    (Y := fun s : ℝ => Y s.toNNReal) (f := fun s => c / X s.toNNReal)
    (h := fun s => c' / Y s.toNNReal) hX.continuous_real.continuousOn
    hY.continuous_real.continuousOn (hX.intervalIntegrable_div t) (hY.intervalIntegrable_div t)
    ?_ ?_ ?_ t ⟨t.coe_nonneg, le_rfl⟩
  · simpa using key
  · simp only [Real.toNNReal_zero]
    rw [hX.2.2.2.2 0, hY.2.2.2.2 0]
    simp [hxx]
  · intro s hs
    have hs0 : s.toNNReal = ⟨s, hs.1⟩ := Real.toNNReal_of_nonneg hs.1
    have hint := hX.intervalIntegrable_div (c := c) (Real.toNNReal s)
    have hint' := hY.intervalIntegrable_div (c := c') (Real.toNNReal s)
    rw [Real.coe_toNNReal s hs.1] at hint hint'
    simp only [Real.toNNReal_zero]
    rw [hX.2.2.2.2 s.toNNReal, hY.2.2.2.2 s.toNNReal, hX.2.2.2.2 0, hY.2.2.2.2 0,
      Real.coe_toNNReal s hs.1, intervalIntegral.integral_sub hint hint']
    simp only [NNReal.coe_zero, intervalIntegral.integral_same, add_zero]
    ring
  · filter_upwards [IsBesselPath.ae_pos hY] with s hYpos hs hlt
    have hYs := hYpos hs.1
    have hXs : 0 < X s.toNNReal := hYs.trans hlt
    calc c / X s.toNNReal ≤ c' / X s.toNNReal := div_le_div_of_nonneg_right hcc hXs.le
      _ ≤ c' / Y s.toNNReal := div_le_div_of_nonneg_left (hc.le.trans hcc) hYs hlt.le

/-- **Pathwise uniqueness of Bessel paths.** -/
theorem IsBesselPath.eq (hc : 0 < c) (hX : IsBesselPath c x b X) (hY : IsBesselPath c x b Y) :
    X = Y :=
  funext fun t => le_antisymm (hX.le hc le_rfl le_rfl hY t) (hY.le hc le_rfl le_rfl hX t)

/-- **Scaling of Bessel paths**: if `X` is a Bessel path with `(c, x, b)` and `σ > 0`, then `σ X` is a
Bessel path with `(σ² c, σ x, σ b)`. (With `b = -B`, `σ = √κ`, `c = (ρ + 2)/κ` this is the gap
`V^R - W = √κ X` of the single-force-point `SLE_κ(ρ)` in (2.3), p. 19.) -/
theorem IsBesselPath.const_mul {σ : ℝ} (hσ : 0 < σ) (h : IsBesselPath c x b X) :
    IsBesselPath (σ ^ 2 * c) (σ * x) (fun t => σ * b t) (fun t => σ * X t) := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  refine ⟨continuous_const.mul h.1, fun t => mul_nonneg hσ.le (h.2.1 t), ?_, fun t => ?_,
    fun t => ?_⟩
  · have : {s : ℝ | 0 ≤ s ∧ σ * X s.toNNReal = 0} = {s : ℝ | 0 ≤ s ∧ X s.toNNReal = 0} := by
      ext s; simp [hσ0]
    rw [this]; exact h.2.2.1
  · refine ((h.2.2.2.1 t).const_mul σ⁻¹).congr fun s _ => ?_
    simp only [mul_inv]
  · have hI : ∫ s in (0 : ℝ)..t, σ ^ 2 * c / (σ * X s.toNNReal)
        = σ * ∫ s in (0 : ℝ)..t, c / X s.toNNReal := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun s _ => ?_
      show σ ^ 2 * c / (σ * X s.toNNReal) = σ * (c / X s.toNNReal)
      rw [sq, mul_assoc, mul_div_mul_left _ _ hσ0, mul_div_assoc]
    simp only
    rw [hI, h.2.2.2.2 t]
    ring

end Bessel

end InteractingSLE
