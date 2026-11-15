/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTilde

/-!
# Zhan's A.1.6, the stochastic part I: the generator identity of the seeded density

Packet PROVE-ZHAN-GT4-A19. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L500, R38): "Do not substitute the seed into the unnormalized factors of `M̃`. Instead use
their normalized factors in `M` … In the remaining formulas the symbol `g_j(p_m)` means `V_j^m` when `p_m` is a seed of
curve `j` … At positive own time, differentiating (D13)–(D15) by Itô and the force ODE is the same cancelled
calculation leading to (D8)."

## The seeded density with the other curve frozen

Curve `j` (driver `W`) grows under its own force-point law: `dW = √κ dB + b dt`, its marks follow the force ODE
`dV^m = 2/(V^m − W) dt` (a seed starts at `V^m(0) = W(0)`), and the other source (index `0`) is the mark `V⁰` with
charge `−κ/2`. The other curve is frozen; `h = h_j` is the map removing its image (A4's `ownExt`). In the normalized form
(D6a) the density of the coupling with respect to the product of the two force-point laws, along the time of curve `j`,
is `exp(ℓ_y − ℓ_0)`, where `ℓ_y` is A7's `log M̃` evaluated with the **own-chart marks** `V^m` (every factor `g_j(p_m)`
replaced by `V^m`, every own derivative `g_j'(p_m)` dropped):

* `A_{j,0} = h(W)`, `A_{j,k} = h^{(k)}(W)`, `A_{k,0} = h(V⁰)`, `A_{k,1} = h'(V⁰)`, `B_{m,0} = h(V^m)`,
  `B_{m,1} = h'(V^m)`;

and `ℓ_0` is the same expression with `h = id` (`A_{j,0} = W`, `A_{j,1} = 1`, `A_{j,2} = A_{j,3} = 0`, `A_{k,0} = V⁰`,
`A_{k,1} = 1`, `B_{m,0} = V^m`, `B_{m,1} = 1`, `F = 1`). The singular parts of the two (`log(h(W) − h(V^m))` against
`log(W − V^m)`, …) cancel in the difference, which is `log` of the normalized factors (D13)–(D15).

At a positive time the derivatives of the own-chart data are those of A7 except that the **derivative factors carry the
extra own-chart rates**: `∂_t log h'(V^m) = −2A₁²/(h(V^m) − h(W))² + 2/(V^m − W)²` (the second term from the force ODE
of `V^m`; A7's `∂_t log B_{m,1}` has only the first), and likewise for `h'(V⁰)`; `∂_t h(V^m) = 2A₁²/(h(V^m) − h(W))`
is unchanged. The extra rates are the same at both heights.

## Main results

* `seedTimeT`, `seedGen`: the time derivative of the time part with the extra rates, and the generator
  `∂_t ℓ + (κ/2)(∂²_x ℓ + (∂_x ℓ)²)` of one height at the driver;
* `dualLogTimeT_add_rates`: the extra rates add `(3κ − 8)/16 · c + Σ_m γ_m c_m` (linearity);
* **`seedGen_eq`**: `seedGen = (3κ − 8)/16 · 2/(V⁰ − W)² + Σ_m γ_m · 2/(V^m − W)²` for every height (A7's
  `dualGen_eq_zero` plus the extra rates);
* `seedGen_id_eq`: the height-`0` (`h = id`) instance;
* `kappa_mul_dualLogSpaceX_id`: `κ ∂_x ℓ_0 = −(κ/2)/(W − V⁰) + Σ_m κ r_m/(W − V^m)`, the force-point drift `b`;
* **`seedGenDiff_eq_zero`**: the generator of `exp(ℓ_y − ℓ_0)` along the drifted driver vanishes,
  `∂_t(ℓ_y − ℓ_0) + b ∂_x(ℓ_y − ℓ_0) + (κ/2)(∂²_x(ℓ_y − ℓ_0) + (∂_x(ℓ_y − ℓ_0))²) = 0` with `b = κ ∂_x ℓ_0`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace InteractingSLE.ZhanGT4

variable {κ : ℝ} {n : ℕ}

/-! ### Extra rates in the time part -/

/-- **Linearity of the time derivative in the derivative-factor rates**: adding `c · A_{k,1}` to `∂_t A_{k,1}` and
`c_m · B_{m,1}` to `∂_t B_{m,1}` adds `(3κ − 8)/16 · c + Σ_m γ_m c_m`. -/
theorem dualLogTimeT_add_rates (r : Fin n → ℝ) {A21 A20 dA21 dL dA20 : ℝ} {B0 B1 dB0 dB1 : Fin n → ℝ}
    (h21 : A21 ≠ 0) (hB1 : ∀ m, B1 m ≠ 0) (c : ℝ) (cm : Fin n → ℝ) :
    dualLogTimeT κ r A21 A20 B0 B1 (dA21 + c * A21) dL dA20 dB0 (fun m => dB1 m + cm m * B1 m)
      = dualLogTimeT κ r A21 A20 B0 B1 dA21 dL dA20 dB0 dB1 + ((3 * κ - 8) / 16 * c
        + ∑ m, dualGamma κ (r m) * cm m) := by
  unfold dualLogTimeT
  have h1 : (dA21 + c * A21) / A21 = dA21 / A21 + c := by field_simp
  have h2 : ∀ m, (dB1 m + cm m * B1 m) / B1 m = dB1 m / B1 m + cm m := fun m => by
    have := hB1 m
    field_simp
  simp_rw [h1, h2, mul_add, add_assoc, Finset.sum_add_distrib]
  ring

/-! ### The generator of one height -/

/-- **The time derivative of the time part with the own-chart marks**, at a positive time: A7's `dualLogTimeT` with
the (D3) derivatives of `A_{k,0}, B_{m,0}` and the derivative factors' rates `−2A₁²/E² + 2/(V − W)²`
(`W` the own driver, `V⁰`, `V^m` the own-chart marks), and `∂_t log F = dL`. -/
def seedTimeT (κ : ℝ) (r : Fin n → ℝ) (A10 A1 A20 A21 : ℝ) (B0 B1 : Fin n → ℝ) (dL W V0 : ℝ) (V : Fin n → ℝ) :
    ℝ :=
  dualLogTimeT κ r A21 A20 B0 B1 (-2 * A1 ^ 2 * A21 / (A10 - A20) ^ 2 + 2 / (V0 - W) ^ 2 * A21) dL
    (2 * A1 ^ 2 / (A20 - A10)) (fun m => 2 * A1 ^ 2 / (B0 m - A10))
    (fun m => -2 * A1 ^ 2 * B1 m / (A10 - B0 m) ^ 2 + 2 / (V m - W) ^ 2 * B1 m)

/-- **The generator of `exp ℓ` at the driver for one height** (driftless part): `∂_t ℓ + (κ/2)(∂²_x ℓ + (∂_x ℓ)²)` at
`x = W`, with the own-time derivatives (D2) `∂_t f = −3A₂`, `∂_t f' = A₂²/(2A₁) − (4/3)A₃` and (D5)
`∂_t log F = ¼(A₂/A₁)² − ⅙A₃/A₁`. -/
def seedGen (κ : ℝ) (r : Fin n → ℝ) (A10 A1 A2 A3 A20 A21 : ℝ) (B0 B1 : Fin n → ℝ) (W V0 : ℝ) (V : Fin n → ℝ) :
    ℝ :=
  seedTimeT κ r A10 A1 A20 A21 B0 B1 (1 / 4 * (A2 / A1) ^ 2 - 1 / 6 * (A3 / A1)) W V0 V
    + dualLogSpaceT κ r A10 A1 A20 B0 (-3 * A2) (A2 ^ 2 / (2 * A1) - 4 / 3 * A3) (2 * A1 ^ 2 / (A20 - A10))
        (fun m => 2 * A1 ^ 2 / (B0 m - A10))
    + κ / 2 * (dualLogSpaceXX κ r A10 A1 A2 A3 A20 B0 + dualLogSpaceX κ r A10 A1 A2 A20 B0 ^ 2)

/-- The extra term of the generator: `(3κ − 8)/16 · 2/(V⁰ − W)² + Σ_m γ_m · 2/(V^m − W)²`. It depends on the own-chart
data only, so it is the same at every height. -/
def seedExtra (κ : ℝ) (r : Fin n → ℝ) (W V0 : ℝ) (V : Fin n → ℝ) : ℝ :=
  (3 * κ - 8) / 16 * (2 / (V0 - W) ^ 2) + ∑ m, dualGamma κ (r m) * (2 / (V m - W) ^ 2)

/-- **The generator of one height is the extra term** (A7's `dualGen_eq_zero` and `dualLogTimeT_add_rates`): the
driftless generator of `M̃` with own-chart marks is not zero, but its defect `seedExtra` does not depend on the map
`h`. -/
theorem seedGen_eq (r : Fin n → ℝ) {A10 A1 A2 A3 A20 A21 W V0 : ℝ} {B0 B1 : Fin n → ℝ} {V : Fin n → ℝ}
    (hκ : κ ≠ 0) (hA1 : A1 ≠ 0) (h21 : A21 ≠ 0) (hB1 : ∀ m, B1 m ≠ 0) (hE0 : A10 - A20 ≠ 0)
    (hE : ∀ m, A10 - B0 m ≠ 0) (h2m : ∀ m, A20 - B0 m ≠ 0) (hmn : ∀ m n, m ≠ n → B0 m - B0 n ≠ 0) :
    seedGen κ r A10 A1 A2 A3 A20 A21 B0 B1 W V0 V = seedExtra κ r W V0 V := by
  have h0 := dualGen_eq_zero (κ := κ) r (A10 := A10) (A1 := A1) (A2 := A2) (A3 := A3) (A20 := A20) (A21 := A21)
    (B0 := B0) (B1 := B1) hκ hA1 h21 hB1 hE0 hE h2m hmn
  have hadd := dualLogTimeT_add_rates (κ := κ) r (A20 := A20) (B0 := B0) (dL := 1 / 4 * (A2 / A1) ^ 2 - 1 / 6 *
    (A3 / A1)) (dA20 := 2 * A1 ^ 2 / (A20 - A10)) (dB0 := fun m => 2 * A1 ^ 2 / (B0 m - A10))
    (dA21 := -2 * A1 ^ 2 * A21 / (A10 - A20) ^ 2) (dB1 := fun m => -2 * A1 ^ 2 * B1 m / (A10 - B0 m) ^ 2)
    h21 hB1 (2 / (V0 - W) ^ 2) (fun m => 2 / (V m - W) ^ 2)
  beta_reduce at hadd
  unfold seedGen seedTimeT seedExtra
  linear_combination hadd + h0

/-- **The height-`0` instance** (`h = id`): `A_{j,0} = W`, `A_{j,1} = 1`, `A_{j,2} = A_{j,3} = 0`, `A_{k,0} = V⁰`,
`A_{k,1} = 1`, `B_{m,0} = V^m`, `B_{m,1} = 1`. -/
theorem seedGen_id_eq (r : Fin n → ℝ) {W V0 : ℝ} {V : Fin n → ℝ} (hκ : κ ≠ 0) (hE0 : W - V0 ≠ 0)
    (hE : ∀ m, W - V m ≠ 0) (h2m : ∀ m, V0 - V m ≠ 0) (hmn : ∀ m n, m ≠ n → V m - V n ≠ 0) :
    seedGen κ r W 1 0 0 V0 1 V (fun _ => 1) W V0 V = seedExtra κ r W V0 V :=
  seedGen_eq r hκ one_ne_zero one_ne_zero (fun _ => one_ne_zero) hE0 hE h2m hmn

/-! ### The force-point drift -/

/-- **`κ ∂_x ℓ_0` is the force-point drift**: at height `0`, `κ · dualLogSpaceX = −(κ/2)/(x − V⁰) + Σ_m κ r_m/(x − V^m)`
(charge `−κ/2` at the other source, `ρ_m = κ r_m` at the marks). -/
theorem kappa_mul_dualLogSpaceX_id (r : Fin n → ℝ) (x V0 : ℝ) (V : Fin n → ℝ) :
    κ * dualLogSpaceX κ r x 1 0 V0 V = -(κ / 2) / (x - V0) + ∑ m, κ * r m / (x - V m) := by
  unfold dualLogSpaceX
  rw [mul_add, mul_sub, Finset.mul_sum]
  simp only [zero_div, mul_zero, zero_sub]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun m _ => ?_
    ring

/-- The height-`0` space part: `ℓ_0 = −½ log(x − V⁰) + Σ_m r_m log(x − V^m)`. -/
theorem dualLogSpace_id (r : Fin n → ℝ) (x V0 : ℝ) (V : Fin n → ℝ) :
    dualLogSpace κ r x 1 V0 V = -(1 / 2) * Real.log (x - V0) + ∑ m, r m * Real.log (x - V m) := by
  unfold dualLogSpace
  rw [Real.log_one, mul_zero, zero_sub, neg_mul]

/-! ### The seeded generator -/

/-- **The generator of the seeded density vanishes** (§A.1.6, "the same cancelled calculation leading to (D8)"): with
`G_y`, `G_0` the driftless generators of the two heights (`seedGen`) and `X_y`, `X_0`, `XX_y`, `XX_0` their first and
second space derivatives at the driver, the generator of `exp(ℓ_y − ℓ_0)` along `dW = √κ dB + b dt`,
`b = κ X_0`, is `G_y − G_0 = seedExtra − seedExtra = 0`. Here `T_y`, `T_0` are the time derivatives (time part plus
space part at the fixed point `x = W`). -/
theorem seedGenDiff_eq_zero {Ty T0 Xy X0 XXy XX0 Gy G0 : ℝ}
    (hGy : Gy = Ty + κ / 2 * (XXy + Xy ^ 2)) (hG0 : G0 = T0 + κ / 2 * (XX0 + X0 ^ 2)) (hG : Gy = G0) :
    (Ty - T0) + κ * X0 * (Xy - X0) + κ / 2 * ((XXy - XX0) + (Xy - X0) ^ 2) = 0 := by
  linear_combination hG - hGy + hG0

/-- **The seeded generator in closed form**: the generator of `exp(ℓ_y − ℓ_0)` along the drifted driver, written with
the two heights' data, vanishes whenever both heights are nondegenerate. -/
theorem seedGen_diff_eq_zero (r : Fin n → ℝ) {A10 A1 A2 A3 A20 A21 W V0 : ℝ} {B0 B1 V : Fin n → ℝ}
    (hκ : κ ≠ 0) (hA1 : A1 ≠ 0) (h21 : A21 ≠ 0) (hB1 : ∀ m, B1 m ≠ 0) (hE0 : A10 - A20 ≠ 0)
    (hE : ∀ m, A10 - B0 m ≠ 0) (h2m : ∀ m, A20 - B0 m ≠ 0) (hmn : ∀ m n, m ≠ n → B0 m - B0 n ≠ 0)
    (hE0' : W - V0 ≠ 0) (hE' : ∀ m, W - V m ≠ 0) (h2m' : ∀ m, V0 - V m ≠ 0)
    (hmn' : ∀ m n, m ≠ n → V m - V n ≠ 0) :
    ((seedTimeT κ r A10 A1 A20 A21 B0 B1 (1 / 4 * (A2 / A1) ^ 2 - 1 / 6 * (A3 / A1)) W V0 V
        + dualLogSpaceT κ r A10 A1 A20 B0 (-3 * A2) (A2 ^ 2 / (2 * A1) - 4 / 3 * A3) (2 * A1 ^ 2 / (A20 - A10))
            (fun m => 2 * A1 ^ 2 / (B0 m - A10)))
      - (seedTimeT κ r W 1 V0 1 V (fun _ => 1) (1 / 4 * (0 / 1) ^ 2 - 1 / 6 * (0 / 1)) W V0 V
        + dualLogSpaceT κ r W 1 V0 V (-3 * 0) (0 ^ 2 / (2 * 1) - 4 / 3 * 0) (2 * 1 ^ 2 / (V0 - W))
            (fun m => 2 * 1 ^ 2 / (V m - W))))
      + κ * dualLogSpaceX κ r W 1 0 V0 V
          * (dualLogSpaceX κ r A10 A1 A2 A20 B0 - dualLogSpaceX κ r W 1 0 V0 V)
      + κ / 2 * ((dualLogSpaceXX κ r A10 A1 A2 A3 A20 B0 - dualLogSpaceXX κ r W 1 0 0 V0 V)
          + (dualLogSpaceX κ r A10 A1 A2 A20 B0 - dualLogSpaceX κ r W 1 0 V0 V) ^ 2) = 0 := by
  have hy := seedGen_eq r (A2 := A2) (A3 := A3) (B1 := B1) (V := V) hκ hA1 h21 hB1 hE0 hE h2m hmn
    (W := W) (V0 := V0)
  have h0 := seedGen_id_eq (κ := κ) r hκ hE0' hE' h2m' hmn'
  unfold seedGen at hy h0
  exact seedGenDiff_eq_zero rfl rfl (hy.trans h0.symm)

end InteractingSLE.ZhanGT4
