/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFieldMark
import InteractingSLE.Spec.ZhanGT4.DualSeedGen
import InteractingSLE.Spec.ZhanGT4.ItoFieldFrozen

/-!
# Zhan's A.1.6, the seeded field III: the concrete seeded log-density and its generator

Packet PROVE-ZHAN-GT4-A20. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L500, R38), (D6a) and (D13)–(D15): "Do not substitute the seed into the unnormalized
factors of `M̃`. Instead use their normalized factors in `M` … In the remaining formulas the symbol `g_j(p_m)` means
`V_j^m` when `p_m` is a seed of curve `j` … At positive own time, differentiating (D13)–(D15) by Itô and the force
ODE is the same cancelled calculation leading to (D8)."

Curve `j` (driver `W`) grows; the other curve is frozen (hull `A`, map `φ`, image chain `W', a` of `OwnData`, frozen tip
`ζ₀` in the `φ`-chart). The marks enter through their **own-chart force coordinates** `V^m` (`V' = 2/(V − W)`: seeds
and ordinary marks alike), the other source through its own-chart coordinate `V⁰` and `G⁰ = g_t'(x_k)`
(`∂_t G⁰ = −2G⁰/(V⁰ − W)²`). `SeedData` packages these; with `F_t = ownExt … t` (the reflected `h_j`):

* height `y` (A7's `log M̃` with the own-chart marks): `A_{k,0} = Re g̃_{a(t)}(ζ₀)`, `A_{k,1} = Re g̃'_{a(t)}(ζ₀)/G⁰`,
  `B_{m,0} = F_t(V^m)`, `B_{m,1} = F_t'(V^m)`, `log F` (A7's `frzLogF`); the space part at the driver position `x`
  uses `F_t(x)`, `F_t'(x)`;
* height `0` (`h = id`): `A_{k,0} = V⁰`, `A_{k,1} = 1`, `B_{m,0} = V^m`, `B_{m,1} = 1`, `log F = 0`, `f(x) = x`;
* **the seeded log-density** `SeedData.ell t x = ℓ_y(t, x) − ℓ_0(t, x)`, its space derivatives `ellX`, `ellXX`,
  `ellXXX`, its time derivative `ellT` ((D1) through `dHat`, (D3) for the marks: `DualSeedFieldMark`, (D5), the force
  ODE) and the force-point drift `drift t = κ ∂_xℓ_0(t, W_t)`.

## Main results

* **`SeedData.gen_eq_zero`**: the generator of `exp ℓ` along `dW = √κ dB + drift dt` vanishes at the driver,
  `∂_tℓ + drift · ∂_xℓ + (κ/2)(∂²_xℓ + (∂_xℓ)²) = 0` (A19's `seedGen_diff_eq_zero` with (D2) at the driver).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-- **The data of the seeded field** with the other curve frozen: the growing driver `W`, the image chain `W', a` and
the frozen map `φ` (A4's `OwnData`), `κ`, the reduced charges `r_m = ρ_m/κ`, the frozen tip `ζ₀` of the other curve
(`φ`-chart), the own-chart coordinate `V⁰` of the other source with `G⁰ = g_t'(x_k)`, and the own-chart force
coordinates `V^m` of the marks. -/
structure SeedData (n : ℕ) where
  W : ℝ → ℝ
  W' : ℝ → ℝ
  a : ℝ → ℝ
  φ : ℂ → ℂ
  κ : ℝ
  r : Fin n → ℝ
  ζ₀ : ℝ
  V₀ : ℝ → ℝ
  G₀ : ℝ → ℝ
  V : Fin n → ℝ → ℝ

namespace SeedData

variable {n : ℕ} (d : SeedData n)

/-- `Re F_t^{(k)}(x)`, `F_t = ownExt … t`. -/
def F (k : ℕ) (t x : ℝ) : ℝ := (deriv^[k] (ownExt d.W d.W' d.a d.φ t) x).re

/-- `A_{j,k}(t) = Re F_t^{(k)}(W_t)`. -/
def A (k : ℕ) (t : ℝ) : ℝ := frzA d.W d.W' d.a d.φ k t

/-- `A_{k,0}(t)`: the frozen tip through the image chain. -/
def A20 (t : ℝ) : ℝ := frzImg d.W' d.a d.ζ₀ t

/-- `A_{k,1}(t)/g_t'(x_k)`: the normalized derivative factor of the other source. -/
def A21 (t : ℝ) : ℝ := frzImgD d.W' d.a d.ζ₀ t / d.G₀ t

/-- `B_{m,0}(t) = F_t(V^m_t)`. -/
def B0 (t : ℝ) : Fin n → ℝ := fun m => d.F 0 t (d.V m t)

/-- `B_{m,1}(t) = F_t'(V^m_t)` (the normalized derivative factor (D13)). -/
def B1 (t : ℝ) : Fin n → ℝ := fun m => d.F 1 t (d.V m t)

/-- The own-chart marks at time `t`. -/
def Vv (t : ℝ) : Fin n → ℝ := fun m => d.V m t

/-- `log F(t, t_k)`. -/
def L (t : ℝ) : ℝ := frzLogF d.W d.W' d.a d.φ t

/-- The time part at height `y`. -/
def LT (t : ℝ) : ℝ := dualLogTime d.κ d.r (d.A21 t) (d.L t) (d.A20 t) (d.B0 t) (d.B1 t)

/-- The time part at height `0`. -/
def LT0 (t : ℝ) : ℝ := dualLogTime d.κ d.r 1 0 (d.V₀ t) (d.Vv t) (fun _ => 1)

/-- The space part at height `y`, at the driver position `x`. -/
def LS (t x : ℝ) : ℝ := dualLogSpace d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.A20 t) (d.B0 t)

/-- The space part at height `0`. -/
def LS0 (t x : ℝ) : ℝ := dualLogSpace d.κ d.r x 1 (d.V₀ t) (d.Vv t)

/-- **The seeded log-density** `ℓ_y − ℓ_0` with the other curve frozen. -/
def ell (t x : ℝ) : ℝ := (d.LT t + d.LS t x) - (d.LT0 t + d.LS0 t x)

/-- `∂_x ℓ`. -/
def ellX (t x : ℝ) : ℝ :=
  dualLogSpaceX d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.F 2 t x) (d.A20 t) (d.B0 t)
    - dualLogSpaceX d.κ d.r x 1 0 (d.V₀ t) (d.Vv t)

/-- `∂²_x ℓ`. -/
def ellXX (t x : ℝ) : ℝ :=
  dualLogSpaceXX d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.F 2 t x) (d.F 3 t x) (d.A20 t) (d.B0 t)
    - dualLogSpaceXX d.κ d.r x 1 0 0 (d.V₀ t) (d.Vv t)

/-- `∂³_x ℓ`. -/
def ellXXX (t x : ℝ) : ℝ :=
  dualLogSpaceXXX d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.F 2 t x) (d.F 3 t x) (d.F 4 t x) (d.A20 t) (d.B0 t)
    - dualLogSpaceXXX d.κ d.r x 1 0 0 0 (d.V₀ t) (d.Vv t)

/-- The time derivative of the time part at height `y` (A19's `seedTimeT`). -/
def LTT (t : ℝ) : ℝ :=
  seedTimeT d.κ d.r (d.A 0 t) (d.A 1 t) (d.A20 t) (d.A21 t) (d.B0 t) (d.B1 t) (frzRate d.W d.W' d.a d.φ t) (d.W t)
    (d.V₀ t) (d.Vv t)

/-- The time derivative of the time part at height `0`. -/
def LT0T (t : ℝ) : ℝ :=
  seedTimeT d.κ d.r (d.W t) 1 (d.V₀ t) 1 (d.Vv t) (fun _ => 1) 0 (d.W t) (d.V₀ t) (d.Vv t)

/-- The time derivative of the space part at height `y` at a fixed `x` ((D1) in the removable form, (D3)). -/
def LST (t x : ℝ) : ℝ :=
  dualLogSpaceT d.κ d.r (d.F 0 t x) (d.F 1 t x) (d.A20 t) (d.B0 t)
    ((dHat (ownExt d.W d.W' d.a d.φ t) (d.W t) x).re) ((deriv (dHat (ownExt d.W d.W' d.a d.φ t) (d.W t)) x).re)
    (2 * d.A 1 t ^ 2 / (d.A20 t - d.A 0 t)) (fun m => 2 * d.A 1 t ^ 2 / (d.B0 t m - d.A 0 t))

/-- The time derivative of the space part at height `0` at a fixed `x` (the force ODE). -/
def LS0T (t x : ℝ) : ℝ :=
  dualLogSpaceT d.κ d.r x 1 (d.V₀ t) (d.Vv t) 0 0 (2 / (d.V₀ t - d.W t)) (fun m => 2 / (d.V m t - d.W t))

/-- `∂_t ℓ` at a fixed `x`. -/
def ellT (t x : ℝ) : ℝ := (d.LTT t + d.LST t x) - (d.LT0T t + d.LS0T t x)

/-- **The force-point drift** `b_t = κ ∂_xℓ_0(t, W_t) = −(κ/2)/(W − V⁰) + Σ_m κ r_m/(W − V^m)`. -/
def drift (t : ℝ) : ℝ := d.κ * dualLogSpaceX d.κ d.r (d.W t) 1 0 (d.V₀ t) (d.Vv t)

theorem F_driver (k : ℕ) (t : ℝ) : d.F k t (d.W t) = d.A k t := rfl

end SeedData

/-! ### The generator at the driver -/

/-- A19's `seedGen_diff_eq_zero` with the height-`0` data in normal form. -/
theorem seedGen_diff_eq_zero' {κ : ℝ} {n : ℕ} (r : Fin n → ℝ) {A10 A1 A2 A3 A20 A21 W V0 : ℝ}
    {B0 B1 V : Fin n → ℝ} (hκ : κ ≠ 0) (hA1 : A1 ≠ 0) (h21 : A21 ≠ 0) (hB1 : ∀ m, B1 m ≠ 0)
    (hE0 : A10 - A20 ≠ 0) (hE : ∀ m, A10 - B0 m ≠ 0) (h2m : ∀ m, A20 - B0 m ≠ 0)
    (hmn : ∀ m n, m ≠ n → B0 m - B0 n ≠ 0) (hE0' : W - V0 ≠ 0) (hE' : ∀ m, W - V m ≠ 0)
    (h2m' : ∀ m, V0 - V m ≠ 0) (hmn' : ∀ m n, m ≠ n → V m - V n ≠ 0) :
    ((seedTimeT κ r A10 A1 A20 A21 B0 B1 (1 / 4 * (A2 / A1) ^ 2 - 1 / 6 * (A3 / A1)) W V0 V
        + dualLogSpaceT κ r A10 A1 A20 B0 (-3 * A2) (A2 ^ 2 / (2 * A1) - 4 / 3 * A3) (2 * A1 ^ 2 / (A20 - A10))
            (fun m => 2 * A1 ^ 2 / (B0 m - A10)))
      - (seedTimeT κ r W 1 V0 1 V (fun _ => 1) 0 W V0 V
        + dualLogSpaceT κ r W 1 V0 V 0 0 (2 / (V0 - W)) (fun m => 2 / (V m - W))))
      + κ * dualLogSpaceX κ r W 1 0 V0 V
          * (dualLogSpaceX κ r A10 A1 A2 A20 B0 - dualLogSpaceX κ r W 1 0 V0 V)
      + κ / 2 * ((dualLogSpaceXX κ r A10 A1 A2 A3 A20 B0 - dualLogSpaceXX κ r W 1 0 0 V0 V)
          + (dualLogSpaceX κ r A10 A1 A2 A20 B0 - dualLogSpaceX κ r W 1 0 V0 V) ^ 2) = 0 := by
  have key := seedGen_diff_eq_zero r (A2 := A2) (A3 := A3) hκ hA1 h21 hB1 hE0 hE h2m hmn hE0' hE' h2m' hmn'
  have e1 : (1 / 4 * ((0 : ℝ) / 1) ^ 2 - 1 / 6 * ((0 : ℝ) / 1)) = 0 := by norm_num
  have e2 : (-3 * (0 : ℝ)) = 0 := by norm_num
  have e3 : ((0 : ℝ) ^ 2 / (2 * 1) - 4 / 3 * 0) = 0 := by norm_num
  have e4 : ∀ u : ℝ, 2 * (1 : ℝ) ^ 2 / u = 2 / u := fun u => by norm_num
  rw [e1, e2, e3, e4] at key
  simp only [e4] at key
  exact key

namespace SeedData

variable {n : ℕ} (d : SeedData n)

/-- **The generator of the seeded density vanishes at the driver** (§A.1.6): given the (D2) values at the driver and
the nondegeneracy of both heights, `∂_tℓ + b ∂_xℓ + (κ/2)(∂²_xℓ + (∂_xℓ)²) = 0` at `x = W_t` with `b = drift`. -/
theorem gen_eq_zero_of_D2 {t : ℝ} (hκ : d.κ ≠ 0)
    (hD2 : (dHat (ownExt d.W d.W' d.a d.φ t) (d.W t) (d.W t)).re = -3 * d.A 2 t ∧
      (deriv (dHat (ownExt d.W d.W' d.a d.φ t) (d.W t)) (d.W t)).re =
        d.A 2 t ^ 2 / (2 * d.A 1 t) - 4 / 3 * d.A 3 t)
    (hA1 : d.A 1 t ≠ 0) (h21 : d.A21 t ≠ 0) (hB1 : ∀ m, d.B1 t m ≠ 0) (hE0 : d.A 0 t - d.A20 t ≠ 0)
    (hE : ∀ m, d.A 0 t - d.B0 t m ≠ 0) (h2m : ∀ m, d.A20 t - d.B0 t m ≠ 0)
    (hmn : ∀ m k, m ≠ k → d.B0 t m - d.B0 t k ≠ 0) (hE0' : d.W t - d.V₀ t ≠ 0) (hE' : ∀ m, d.W t - d.V m t ≠ 0)
    (h2m' : ∀ m, d.V₀ t - d.V m t ≠ 0) (hmn' : ∀ m k, m ≠ k → d.V m t - d.V k t ≠ 0) :
    d.ellT t (d.W t) + d.drift t * d.ellX t (d.W t)
      + d.κ / 2 * (d.ellXX t (d.W t) + d.ellX t (d.W t) ^ 2) = 0 := by
  have key := seedGen_diff_eq_zero' (κ := d.κ) d.r (A10 := d.A 0 t) (A1 := d.A 1 t) (A2 := d.A 2 t)
    (A3 := d.A 3 t) (A20 := d.A20 t) (A21 := d.A21 t) (B0 := d.B0 t) (B1 := d.B1 t) (W := d.W t) (V0 := d.V₀ t)
    (V := d.Vv t) hκ hA1 h21 hB1 hE0 hE h2m hmn hE0' hE' h2m' hmn'
  have hrate : frzRate d.W d.W' d.a d.φ t = 1 / 4 * (d.A 2 t / d.A 1 t) ^ 2 - 1 / 6 * (d.A 3 t / d.A 1 t) := rfl
  simp only [ellT, LTT, LT0T, LST, LS0T, drift, ellX, ellXX, F_driver, hrate, hD2.1, hD2.2]
  exact key

end SeedData

end InteractingSLE.ZhanGT4
