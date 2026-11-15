/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.Dual
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The two-parameter density `M̃` of (D6) as a field: logarithm, derivatives and the generator identity

Packet PROVE-ZHAN-GT4-A7. Source: Astra, *Follow-up proofs and dependency audit*, §A.1.1–A.1.3
(`source/external/AstraIG1/ig1_followup_proofs.txt` L190–L300, ruling R38; A.6 item 3), and the additional note §2.1
(`ig1_additional_proofs.txt` L620–L790, ruling R39: "All differential identities below can be read as generator
identities").

Along the time `t_j` of curve `j` (the other curve frozen), the density
`M̃ = A^{α_j}_{j,1} A^{α_k}_{k,1} E^{−1/2} F^{−Λ} ∏_m (B^{γ_m}_{m,1} |E_{j,m}|^{r_{j,m}} |E_{k,m}|^{r_{k,m}}) ∏_{m<n} |C_{mn}|^{δ_{mn}}`
depends on the position `x` of the driver `W_j` only through `f = h_j(x)` and `f' = h_j'(x)`
(`E_{j,0} = f − A_{k,0}`, `E_{j,m} = f − B_{m,0}`); every other factor is a function of time alone
(`E_{k,m} = A_{k,0} − B_{m,0}`, `C_{mn} = B_{m,0} − B_{n,0}`). We write `M̃ = exp(ℓ_time + ℓ_space)` with **real
logarithms** (`Real.log y = log |y|`, so the absolute values of (D6) are built in):

* `dualLogSpace κ r f f' A₀ B₀ = α log f' − ½ log (f − A₀) + Σ_m r_m log (f − B₀ m)`;
* `dualLogTime κ r A₂₁ L A₂₀ B₀ B₁ = α' log A₂₁ − Λ L + Σ_m (γ_m log B₁ m + r'_m log (A₂₀ − B₀ m))
  + Σ_{m<n} δ_{mn} log (B₀ m − B₀ n)`, with `α' = (3κ − 8)/16 = α_k` and `r'_m = −(κ/4) r_m = r_{k,m}` (`Dual.lean`),
  `L = log F`.

## Main results

* `hasDerivAt_dualLogSpace`, `hasDerivAt_dualLogSpaceX`: the first and second space derivatives
  (`dualLogSpaceX`, `dualLogSpaceXX`) of `x ↦ ℓ_space(f(x), f'(x), …)`;
* `hasDerivWithinAt_dualLogSpace_time`, `hasDerivWithinAt_dualLogTime`: the time derivatives (`dualLogSpaceT`,
  `dualLogTimeT`) at a fixed space point;
* **`dualGen_eq_dualDrift`, `dualGen_eq_zero`**: at the driver, after substituting (D2)–(D3) and (D5)
  (`∂_t f = −3A₂`, `∂_t f' = A₂²/(2A₁) − (4/3)A₃`, `∂_t A_{k,0} = 2A₁²/(A_{k,0} − A_{j,0})`, …), the generator
  `∂_t ℓ + (κ/2)(∂_x² ℓ + (∂_x ℓ)²)` of `M̃ = exp ℓ` is `dualDrift`, hence `0` (`dualDrift_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open Finset Set

namespace InteractingSLE.ZhanGT4

/-! ### The logarithm of `M̃` and its formal derivatives -/

/-- **The space part of `log M̃`**: `α log f' − ½ log (f − A₀) + Σ_m r_m log (f − B₀ m)` (real logarithms). -/
def dualLogSpace (κ : ℝ) {n : ℕ} (r : Fin n → ℝ) (f f1 A0 : ℝ) (B0 : Fin n → ℝ) : ℝ :=
  dualAlpha κ * Real.log f1 - 1 / 2 * Real.log (f - A0) + ∑ m, r m * Real.log (f - B0 m)

/-- The first space derivative of `dualLogSpace` (`f2 = f''`): the noise coefficient `q` of (D7). -/
def dualLogSpaceX (κ : ℝ) {n : ℕ} (r : Fin n → ℝ) (f f1 f2 A0 : ℝ) (B0 : Fin n → ℝ) : ℝ :=
  dualAlpha κ * (f2 / f1) - 1 / 2 * (f1 / (f - A0)) + ∑ m, r m * (f1 / (f - B0 m))

/-- The second space derivative of `dualLogSpace` (`f3 = f'''`). -/
def dualLogSpaceXX (κ : ℝ) {n : ℕ} (r : Fin n → ℝ) (f f1 f2 f3 A0 : ℝ) (B0 : Fin n → ℝ) : ℝ :=
  dualAlpha κ * (f3 / f1 - (f2 / f1) ^ 2) - 1 / 2 * (f2 / (f - A0) - (f1 / (f - A0)) ^ 2)
    + ∑ m, r m * (f2 / (f - B0 m) - (f1 / (f - B0 m)) ^ 2)

/-- The time derivative of `dualLogSpace` at a fixed space point, given the time derivatives `df, df1, dA0, dB0`. -/
def dualLogSpaceT (κ : ℝ) {n : ℕ} (r : Fin n → ℝ) (f f1 A0 : ℝ) (B0 : Fin n → ℝ) (df df1 dA0 : ℝ)
    (dB0 : Fin n → ℝ) : ℝ :=
  dualAlpha κ * (df1 / f1) - 1 / 2 * ((df - dA0) / (f - A0)) + ∑ m, r m * ((df - dB0 m) / (f - B0 m))

/-- **The time part of `log M̃`**: `α' log A₂₁ − Λ L + Σ_m (γ_m log B₁ m + r'_m log (A₂₀ − B₀ m))
+ Σ_{m<n} δ_{mn} log (B₀ m − B₀ n)`, `α' = (3κ − 8)/16`, `r'_m = −(κ/4) r_m`, `L = log F`. -/
def dualLogTime (κ : ℝ) {n : ℕ} (r : Fin n → ℝ) (A21 L A20 : ℝ) (B0 B1 : Fin n → ℝ) : ℝ :=
  (3 * κ - 8) / 16 * Real.log A21 - dualLambda κ * L
    + ∑ m, (dualGamma κ (r m) * Real.log (B1 m) + -(κ / 4) * r m * Real.log (A20 - B0 m))
    + pairSum (fun m n => dualDelta κ (r m) (r n) * Real.log (B0 m - B0 n))

/-- The time derivative of `dualLogTime`, given the time derivatives of its arguments. -/
def dualLogTimeT (κ : ℝ) {n : ℕ} (r : Fin n → ℝ) (A21 A20 : ℝ) (B0 B1 : Fin n → ℝ) (dA21 dL dA20 : ℝ)
    (dB0 dB1 : Fin n → ℝ) : ℝ :=
  (3 * κ - 8) / 16 * (dA21 / A21) - dualLambda κ * dL
    + ∑ m, (dualGamma κ (r m) * (dB1 m / B1 m) + -(κ / 4) * r m * ((dA20 - dB0 m) / (A20 - B0 m)))
    + pairSum (fun m n => dualDelta κ (r m) (r n) * ((dB0 m - dB0 n) / (B0 m - B0 n)))

/-! ### Derivatives -/

section Deriv

variable {κ : ℝ} {n : ℕ} {r : Fin n → ℝ}

/-- The space derivative of `ℓ_space(f(x), f'(x), A₀, B₀)`. -/
theorem hasDerivAt_dualLogSpace {f f1 : ℝ → ℝ} {x f2 A0 : ℝ} {B0 : Fin n → ℝ}
    (hf : HasDerivAt f (f1 x) x) (hf1 : HasDerivAt f1 f2 x) (h1 : f1 x ≠ 0) (h0 : f x - A0 ≠ 0)
    (hm : ∀ m, f x - B0 m ≠ 0) :
    HasDerivAt (fun y => dualLogSpace κ r (f y) (f1 y) A0 B0) (dualLogSpaceX κ r (f x) (f1 x) f2 A0 B0) x := by
  have e1 := (hf1.log h1).const_mul (dualAlpha κ)
  have e2 := ((hf.sub_const A0).log h0).const_mul (1 / 2 : ℝ)
  have e3 : HasDerivAt (fun y => ∑ m, r m * Real.log (f y - B0 m))
      (∑ m, r m * (f1 x / (f x - B0 m))) x :=
    HasDerivAt.fun_sum fun m _ => ((hf.sub_const (B0 m)).log (hm m)).const_mul (r m)
  exact (e1.sub e2).add e3

/-- The space derivative of `dualLogSpaceX(f(x), f'(x), f''(x), A₀, B₀)`. -/
theorem hasDerivAt_dualLogSpaceX {f f1 f2 : ℝ → ℝ} {x f3 A0 : ℝ} {B0 : Fin n → ℝ}
    (hf : HasDerivAt f (f1 x) x) (hf1 : HasDerivAt f1 (f2 x) x) (hf2 : HasDerivAt f2 f3 x) (h1 : f1 x ≠ 0)
    (h0 : f x - A0 ≠ 0) (hm : ∀ m, f x - B0 m ≠ 0) :
    HasDerivAt (fun y => dualLogSpaceX κ r (f y) (f1 y) (f2 y) A0 B0)
      (dualLogSpaceXX κ r (f x) (f1 x) (f2 x) f3 A0 B0) x := by
  have q1 : HasDerivAt (fun y => f2 y / f1 y) (f3 / f1 x - (f2 x / f1 x) ^ 2) x := by
    refine (hf2.div hf1 h1).congr_deriv ?_
    field_simp
  have qd : ∀ c : ℝ, f x - c ≠ 0 → HasDerivAt (fun y => f1 y / (f y - c))
      (f2 x / (f x - c) - (f1 x / (f x - c)) ^ 2) x := fun c hc => by
    refine (hf1.div (hf.sub_const c) hc).congr_deriv ?_
    field_simp
  have e1 := q1.const_mul (dualAlpha κ)
  have e2 := (qd A0 h0).const_mul (1 / 2 : ℝ)
  have e3 : HasDerivAt (fun y => ∑ m, r m * (f1 y / (f y - B0 m)))
      (∑ m, r m * (f2 x / (f x - B0 m) - (f1 x / (f x - B0 m)) ^ 2)) x :=
    HasDerivAt.fun_sum fun m _ => (qd (B0 m) (hm m)).const_mul (r m)
  exact (e1.sub e2).add e3

/-- The time derivative of `ℓ_space` at a fixed space point. -/
theorem hasDerivWithinAt_dualLogSpace_time {J : Set ℝ} {s : ℝ} {f f1 A0 : ℝ → ℝ} {B0 : ℝ → Fin n → ℝ}
    {df df1 dA0 : ℝ} {dB0 : Fin n → ℝ} (hf : HasDerivWithinAt f df J s) (hf1 : HasDerivWithinAt f1 df1 J s)
    (hA0 : HasDerivWithinAt A0 dA0 J s) (hB0 : ∀ m, HasDerivWithinAt (fun u => B0 u m) (dB0 m) J s)
    (h1 : f1 s ≠ 0) (h0 : f s - A0 s ≠ 0) (hm : ∀ m, f s - B0 s m ≠ 0) :
    HasDerivWithinAt (fun u => dualLogSpace κ r (f u) (f1 u) (A0 u) (B0 u))
      (dualLogSpaceT κ r (f s) (f1 s) (A0 s) (B0 s) df df1 dA0 dB0) J s := by
  have e1 := (hf1.log h1).const_mul (dualAlpha κ)
  have e2 := ((hf.sub hA0).log h0).const_mul (1 / 2 : ℝ)
  have e3 : HasDerivWithinAt (fun u => ∑ m, r m * Real.log (f u - B0 u m))
      (∑ m, r m * ((df - dB0 m) / (f s - B0 s m))) J s :=
    HasDerivWithinAt.fun_sum fun m _ => ((hf.sub (hB0 m)).log (hm m)).const_mul (r m)
  exact (e1.sub e2).add e3

/-- The time derivative of `ℓ_time`. -/
theorem hasDerivWithinAt_dualLogTime {J : Set ℝ} {s : ℝ} {A21 L A20 : ℝ → ℝ} {B0 B1 : ℝ → Fin n → ℝ}
    {dA21 dL dA20 : ℝ} {dB0 dB1 : Fin n → ℝ} (hA21 : HasDerivWithinAt A21 dA21 J s)
    (hL : HasDerivWithinAt L dL J s) (hA20 : HasDerivWithinAt A20 dA20 J s)
    (hB0 : ∀ m, HasDerivWithinAt (fun u => B0 u m) (dB0 m) J s)
    (hB1 : ∀ m, HasDerivWithinAt (fun u => B1 u m) (dB1 m) J s) (h21 : A21 s ≠ 0) (hB1z : ∀ m, B1 s m ≠ 0)
    (h2m : ∀ m, A20 s - B0 s m ≠ 0) (hmn : ∀ m n, m ≠ n → B0 s m - B0 s n ≠ 0) :
    HasDerivWithinAt (fun u => dualLogTime κ r (A21 u) (L u) (A20 u) (B0 u) (B1 u))
      (dualLogTimeT κ r (A21 s) (A20 s) (B0 s) (B1 s) dA21 dL dA20 dB0 dB1) J s := by
  have e1 := (hA21.log h21).const_mul ((3 * κ - 8) / 16)
  have e2 := hL.const_mul (dualLambda κ)
  have e3 : HasDerivWithinAt (fun u => ∑ m, (dualGamma κ (r m) * Real.log (B1 u m)
      + -(κ / 4) * r m * Real.log (A20 u - B0 u m)))
      (∑ m, (dualGamma κ (r m) * (dB1 m / B1 s m) + -(κ / 4) * r m * ((dA20 - dB0 m) / (A20 s - B0 s m))))
      J s :=
    HasDerivWithinAt.fun_sum fun m _ =>
      (((hB1 m).log (hB1z m)).const_mul _).add (((hA20.sub (hB0 m)).log (h2m m)).const_mul _)
  have e4 : HasDerivWithinAt (fun u => pairSum (fun m n => dualDelta κ (r m) (r n) * Real.log (B0 u m - B0 u n)))
      (pairSum (fun m n => dualDelta κ (r m) (r n) * ((dB0 m - dB0 n) / (B0 s m - B0 s n)))) J s := by
    unfold pairSum
    refine HasDerivWithinAt.fun_sum fun p hp => ?_
    have hp' : p.1 ≠ p.2 := (Finset.mem_filter.1 hp).2.ne
    exact (((hB0 p.1).sub (hB0 p.2)).log (hmn _ _ hp')).const_mul _
  exact ((e1.sub e2).add e3).add e4

end Deriv

/-! ### The generator identity at the driver -/

/-- **The generator of `M̃ = exp ℓ` at the driver is `dualDrift`** (§A.1.2, L270–L281; the additional note's coefficient
certificate, L700–L745). Substitute the space derivatives `f = A₁₀, f' = A₁, f'' = A₂, f''' = A₃`, the own-time
derivatives (D2) `∂_t f = −3A₂`, `∂_t f' = A₂²/(2A₁) − (4/3)A₃`, the other-time derivatives (D3)
`∂_t A₂₀ = 2A₁²/(A₂₀ − A₁₀)`, `∂_t B₀ m = 2A₁²/(B₀ m − A₁₀)`, `∂_t A₂₁ = −2A₁²A₂₁/E₀²`, `∂_t B₁ m = −2A₁²B₁ m/E_m²`,
and (D5) `∂_t log F = ¼(A₂/A₁)² − ⅙A₃/A₁`; then `∂_t ℓ + (κ/2)(∂²_x ℓ + (∂_x ℓ)²)` is `dualDrift` with
`E₀ = A₁₀ − A₂₀`, `E_m = A₁₀ − B₀ m`. -/
theorem dualGen_eq_dualDrift {κ : ℝ} {n : ℕ} (r : Fin n → ℝ) {A10 A1 A2 A3 A20 A21 : ℝ} {B0 B1 : Fin n → ℝ}
    (hA1 : A1 ≠ 0) (h21 : A21 ≠ 0) (hB1 : ∀ m, B1 m ≠ 0) (hE0 : A10 - A20 ≠ 0) (hE : ∀ m, A10 - B0 m ≠ 0)
    (h2m : ∀ m, A20 - B0 m ≠ 0) (hmn : ∀ m n, m ≠ n → B0 m - B0 n ≠ 0) :
    dualLogTimeT κ r A21 A20 B0 B1 (-2 * A1 ^ 2 * A21 / (A10 - A20) ^ 2) (1 / 4 * (A2 / A1) ^ 2 - 1 / 6 * (A3 / A1))
        (2 * A1 ^ 2 / (A20 - A10)) (fun m => 2 * A1 ^ 2 / (B0 m - A10))
        (fun m => -2 * A1 ^ 2 * B1 m / (A10 - B0 m) ^ 2)
      + dualLogSpaceT κ r A10 A1 A20 B0 (-3 * A2) (A2 ^ 2 / (2 * A1) - 4 / 3 * A3) (2 * A1 ^ 2 / (A20 - A10))
          (fun m => 2 * A1 ^ 2 / (B0 m - A10))
      + κ / 2 * (dualLogSpaceXX κ r A10 A1 A2 A3 A20 B0 + dualLogSpaceX κ r A10 A1 A2 A20 B0 ^ 2)
    = dualDrift κ A1 A2 A3 (A10 - A20) r (fun m => A10 - B0 m) := by
  have e5 : A20 - A10 ≠ 0 := fun h => hE0 (by linarith)
  have hq : dualLogSpaceX κ r A10 A1 A2 A20 B0 = dualQ κ A1 A2 (A10 - A20) r (fun m => A10 - B0 m) := by
    unfold dualLogSpaceX dualQ
    congr 1
    field_simp
  -- one mark
  have hm : ∀ m, (dualGamma κ (r m) * (-2 * A1 ^ 2 * B1 m / (A10 - B0 m) ^ 2 / B1 m)
        + -(κ / 4) * r m * ((2 * A1 ^ 2 / (A20 - A10) - 2 * A1 ^ 2 / (B0 m - A10)) / (A20 - B0 m)))
      + r m * ((-3 * A2 - 2 * A1 ^ 2 / (B0 m - A10)) / (A10 - B0 m))
      + κ / 2 * (r m * (A2 / (A10 - B0 m) - (A1 / (A10 - B0 m)) ^ 2))
      = dualGamma κ (r m) * (-2 * A1 ^ 2 / (A10 - B0 m) ^ 2)
        + r m * ((κ / 2 - 3) * (A2 / (A10 - B0 m)) + 2 * A1 ^ 2 / (A10 - B0 m) ^ 2
          - κ * A1 ^ 2 / (2 * (A10 - B0 m) ^ 2))
        + -(κ / 4) * r m * (-2 * A1 ^ 2 / ((A10 - A20) * (A10 - B0 m))) := by
    intro m
    have e1 := hE m
    have e2 := h2m m
    have e3 := hB1 m
    have e4 : B0 m - A10 ≠ 0 := fun h => e1 (by linarith)
    field_simp
    ring
  -- one pair
  have hp : ∀ m n, m ≠ n → dualDelta κ (r m) (r n) * ((2 * A1 ^ 2 / (B0 m - A10) - 2 * A1 ^ 2 / (B0 n - A10))
      / (B0 m - B0 n)) = dualDelta κ (r m) (r n) * (-2 * A1 ^ 2 / ((A10 - B0 m) * (A10 - B0 n))) := by
    intro m n hne
    have e1 := hE m
    have e2 := hE n
    have e3 := hmn m n hne
    have e4 : B0 m - A10 ≠ 0 := fun h => e1 (by linarith)
    have e6 : B0 n - A10 ≠ 0 := fun h => e2 (by linarith)
    field_simp
    ring
  -- the scalar terms
  have hs : (3 * κ - 8) / 16 * (-2 * A1 ^ 2 * A21 / (A10 - A20) ^ 2 / A21)
      - dualLambda κ * (1 / 4 * (A2 / A1) ^ 2 - 1 / 6 * (A3 / A1))
      + (dualAlpha κ * ((A2 ^ 2 / (2 * A1) - 4 / 3 * A3) / A1)
        - 1 / 2 * ((-3 * A2 - 2 * A1 ^ 2 / (A20 - A10)) / (A10 - A20)))
      + κ / 2 * (dualAlpha κ * (A3 / A1 - (A2 / A1) ^ 2) - 1 / 2 * (A2 / (A10 - A20) - (A1 / (A10 - A20)) ^ 2))
      = dualAlpha κ * ((1 - κ) / 2 * (A2 ^ 2 / A1 ^ 2) + (κ / 2 - 4 / 3) * (A3 / A1))
        + (3 * κ - 8) / 16 * (-2 * A1 ^ 2 / (A10 - A20) ^ 2)
        - 1 / 2 * ((κ / 2 - 3) * (A2 / (A10 - A20)) + 2 * A1 ^ 2 / (A10 - A20) ^ 2
          - κ * A1 ^ 2 / (2 * (A10 - A20) ^ 2))
        - dualLambda κ * (1 / 4 * (A2 ^ 2 / A1 ^ 2) - 1 / 6 * (A3 / A1)) := by
    field_simp
    ring
  -- the sums over marks
  have hsum : (∑ m, (dualGamma κ (r m) * (-2 * A1 ^ 2 * B1 m / (A10 - B0 m) ^ 2 / B1 m)
        + -(κ / 4) * r m * ((2 * A1 ^ 2 / (A20 - A10) - 2 * A1 ^ 2 / (B0 m - A10)) / (A20 - B0 m))))
      + (∑ m, r m * ((-3 * A2 - 2 * A1 ^ 2 / (B0 m - A10)) / (A10 - B0 m)))
      + κ / 2 * (∑ m, r m * (A2 / (A10 - B0 m) - (A1 / (A10 - B0 m)) ^ 2))
      = (∑ m, dualGamma κ (r m) * (-2 * A1 ^ 2 / (A10 - B0 m) ^ 2))
        + (∑ m, r m * ((κ / 2 - 3) * (A2 / (A10 - B0 m)) + 2 * A1 ^ 2 / (A10 - B0 m) ^ 2
          - κ * A1 ^ 2 / (2 * (A10 - B0 m) ^ 2)))
        + (∑ m, -(κ / 4) * r m * (-2 * A1 ^ 2 / ((A10 - A20) * (A10 - B0 m)))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun m _ => hm m,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hpair : pairSum (fun m n => dualDelta κ (r m) (r n) * ((2 * A1 ^ 2 / (B0 m - A10) - 2 * A1 ^ 2 / (B0 n - A10))
      / (B0 m - B0 n))) =
      pairSum (fun m n => dualDelta κ (r m) (r n) * (-2 * A1 ^ 2 / ((A10 - B0 m) * (A10 - B0 n)))) := by
    unfold pairSum
    exact Finset.sum_congr rfl fun p hp' => hp p.1 p.2 (Finset.mem_filter.1 hp').2.ne
  rw [hq]
  unfold dualLogTimeT dualLogSpaceT dualLogSpaceXX dualDrift
  linear_combination hs + hsum + hpair

/-- **The drift of `M̃` vanishes at the driver** (`dualGen_eq_dualDrift` and `dualDrift_eq_zero`). -/
theorem dualGen_eq_zero {κ : ℝ} {n : ℕ} (r : Fin n → ℝ) {A10 A1 A2 A3 A20 A21 : ℝ} {B0 B1 : Fin n → ℝ}
    (hκ : κ ≠ 0) (hA1 : A1 ≠ 0) (h21 : A21 ≠ 0) (hB1 : ∀ m, B1 m ≠ 0) (hE0 : A10 - A20 ≠ 0)
    (hE : ∀ m, A10 - B0 m ≠ 0) (h2m : ∀ m, A20 - B0 m ≠ 0) (hmn : ∀ m n, m ≠ n → B0 m - B0 n ≠ 0) :
    dualLogTimeT κ r A21 A20 B0 B1 (-2 * A1 ^ 2 * A21 / (A10 - A20) ^ 2) (1 / 4 * (A2 / A1) ^ 2 - 1 / 6 * (A3 / A1))
        (2 * A1 ^ 2 / (A20 - A10)) (fun m => 2 * A1 ^ 2 / (B0 m - A10))
        (fun m => -2 * A1 ^ 2 * B1 m / (A10 - B0 m) ^ 2)
      + dualLogSpaceT κ r A10 A1 A20 B0 (-3 * A2) (A2 ^ 2 / (2 * A1) - 4 / 3 * A3) (2 * A1 ^ 2 / (A20 - A10))
          (fun m => 2 * A1 ^ 2 / (B0 m - A10))
      + κ / 2 * (dualLogSpaceXX κ r A10 A1 A2 A3 A20 B0 + dualLogSpaceX κ r A10 A1 A2 A20 B0 ^ 2) = 0 := by
  rw [dualGen_eq_dualDrift r hA1 h21 hB1 hE0 hE h2m hmn]
  exact dualDrift_eq_zero r (fun m => A10 - B0 m) hκ hA1 hE0 hE

/-! ### The third space derivative and the cut-off exponential -/

/-- The third space derivative of `dualLogSpace` (`f4 = f''''`). -/
def dualLogSpaceXXX (κ : ℝ) {n : ℕ} (r : Fin n → ℝ) (f f1 f2 f3 f4 A0 : ℝ) (B0 : Fin n → ℝ) : ℝ :=
  dualAlpha κ * (f4 / f1 - 3 * (f3 / f1) * (f2 / f1) + 2 * (f2 / f1) ^ 3)
    - 1 / 2 * (f3 / (f - A0) - 3 * (f2 / (f - A0)) * (f1 / (f - A0)) + 2 * (f1 / (f - A0)) ^ 3)
    + ∑ m, r m * (f3 / (f - B0 m) - 3 * (f2 / (f - B0 m)) * (f1 / (f - B0 m)) + 2 * (f1 / (f - B0 m)) ^ 3)

section Deriv3

variable {κ : ℝ} {n : ℕ} {r : Fin n → ℝ}

/-- The derivative of `u ↦ (u'' u − u'²)`-type ratios: `(g₂/g₀ − (g₁/g₀)²)' = g₃/g₀ − 3(g₂/g₀)(g₁/g₀) + 2(g₁/g₀)³`. -/
theorem hasDerivAt_ratio2 {g0 g1 g2 : ℝ → ℝ} {x g3 : ℝ} (h0 : HasDerivAt g0 (g1 x) x)
    (h1 : HasDerivAt g1 (g2 x) x) (h2 : HasDerivAt g2 g3 x) (hne : g0 x ≠ 0) :
    HasDerivAt (fun y => g2 y / g0 y - (g1 y / g0 y) ^ 2)
      (g3 / g0 x - 3 * (g2 x / g0 x) * (g1 x / g0 x) + 2 * (g1 x / g0 x) ^ 3) x := by
  have q1 : HasDerivAt (fun y => g1 y / g0 y) (g2 x / g0 x - (g1 x / g0 x) ^ 2) x := by
    refine (h1.div h0 hne).congr_deriv ?_
    field_simp
  have q2 : HasDerivAt (fun y => g2 y / g0 y) (g3 / g0 x - g2 x / g0 x * (g1 x / g0 x)) x := by
    refine (h2.div h0 hne).congr_deriv ?_
    field_simp
  refine (q2.sub (q1.pow 2)).congr_deriv ?_
  push_cast
  ring

/-- The space derivative of `dualLogSpaceXX(f(x), f'(x), f''(x), f'''(x), A₀, B₀)`. -/
theorem hasDerivAt_dualLogSpaceXX {f f1 f2 f3 : ℝ → ℝ} {x f4 A0 : ℝ} {B0 : Fin n → ℝ}
    (hf : HasDerivAt f (f1 x) x) (hf1 : HasDerivAt f1 (f2 x) x) (hf2 : HasDerivAt f2 (f3 x) x)
    (hf3 : HasDerivAt f3 f4 x) (h1 : f1 x ≠ 0) (h0 : f x - A0 ≠ 0) (hm : ∀ m, f x - B0 m ≠ 0) :
    HasDerivAt (fun y => dualLogSpaceXX κ r (f y) (f1 y) (f2 y) (f3 y) A0 B0)
      (dualLogSpaceXXX κ r (f x) (f1 x) (f2 x) (f3 x) f4 A0 B0) x := by
  have e1 := (hasDerivAt_ratio2 hf1 hf2 hf3 h1).const_mul (dualAlpha κ)
  have hd : ∀ c : ℝ, f x - c ≠ 0 → HasDerivAt (fun y => f2 y / (f y - c) - (f1 y / (f y - c)) ^ 2)
      (f3 x / (f x - c) - 3 * (f2 x / (f x - c)) * (f1 x / (f x - c)) + 2 * (f1 x / (f x - c)) ^ 3) x :=
    fun c hc => hasDerivAt_ratio2 (g0 := fun y => f y - c) (hf.sub_const c) hf1 hf2 hc
  have e2 := (hd A0 h0).const_mul (1 / 2 : ℝ)
  have e3 : HasDerivAt (fun y => ∑ m, r m * (f2 y / (f y - B0 m) - (f1 y / (f y - B0 m)) ^ 2))
      (∑ m, r m * (f3 x / (f x - B0 m) - 3 * (f2 x / (f x - B0 m)) * (f1 x / (f x - B0 m))
        + 2 * (f1 x / (f x - B0 m)) ^ 3)) x :=
    HasDerivAt.fun_sum fun m _ => (hd (B0 m) (hm m)).const_mul (r m)
  exact (e1.sub e2).add e3

end Deriv3

/-- `χ e^ℓ`. -/
def cutExp0 (c0 l0 : ℝ) : ℝ := c0 * Real.exp l0

/-- The first derivative of `χ e^ℓ`: `(χ' + χℓ') e^ℓ`. -/
def cutExp1 (c0 c1 l0 l1 : ℝ) : ℝ := (c1 + c0 * l1) * Real.exp l0

/-- The second derivative of `χ e^ℓ`: `(χ'' + 2χ'ℓ' + χ(ℓ'' + ℓ'²)) e^ℓ`. -/
def cutExp2 (c0 c1 c2 l0 l1 l2 : ℝ) : ℝ := (c2 + 2 * c1 * l1 + c0 * (l2 + l1 ^ 2)) * Real.exp l0

/-- The third derivative of `χ e^ℓ`. -/
def cutExp3 (c0 c1 c2 c3 l0 l1 l2 l3 : ℝ) : ℝ :=
  (c3 + 3 * c2 * l1 + 3 * c1 * (l2 + l1 ^ 2) + c0 * (l3 + 3 * l1 * l2 + l1 ^ 3)) * Real.exp l0

section CutExp

variable {χ0 χ1 χ2 ℓ0 ℓ1 ℓ2 : ℝ → ℝ} {x : ℝ}

theorem hasDerivAt_cutExp0 (hc0 : HasDerivAt χ0 (χ1 x) x) (hl0 : HasDerivAt ℓ0 (ℓ1 x) x) :
    HasDerivAt (fun y => cutExp0 (χ0 y) (ℓ0 y)) (cutExp1 (χ0 x) (χ1 x) (ℓ0 x) (ℓ1 x)) x := by
  refine (hc0.mul hl0.exp).congr_deriv ?_
  simp only [cutExp1]
  ring

theorem hasDerivAt_cutExp1 (hc0 : HasDerivAt χ0 (χ1 x) x) (hc1 : HasDerivAt χ1 (χ2 x) x)
    (hl0 : HasDerivAt ℓ0 (ℓ1 x) x) (hl1 : HasDerivAt ℓ1 (ℓ2 x) x) :
    HasDerivAt (fun y => cutExp1 (χ0 y) (χ1 y) (ℓ0 y) (ℓ1 y))
      (cutExp2 (χ0 x) (χ1 x) (χ2 x) (ℓ0 x) (ℓ1 x) (ℓ2 x)) x := by
  have H := (hc1.add (hc0.mul hl1)).mul hl0.exp
  refine (H.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [cutExp1, Pi.add_apply, Pi.mul_apply]
  · simp only [cutExp2, Pi.add_apply, Pi.mul_apply]
    ring

theorem hasDerivAt_cutExp2 {χ3 : ℝ → ℝ} {ℓ3 : ℝ → ℝ} (hc0 : HasDerivAt χ0 (χ1 x) x) (hc1 : HasDerivAt χ1 (χ2 x) x)
    (hc2 : HasDerivAt χ2 (χ3 x) x) (hl0 : HasDerivAt ℓ0 (ℓ1 x) x) (hl1 : HasDerivAt ℓ1 (ℓ2 x) x)
    (hl2 : HasDerivAt ℓ2 (ℓ3 x) x) :
    HasDerivAt (fun y => cutExp2 (χ0 y) (χ1 y) (χ2 y) (ℓ0 y) (ℓ1 y) (ℓ2 y))
      (cutExp3 (χ0 x) (χ1 x) (χ2 x) (χ3 x) (ℓ0 x) (ℓ1 x) (ℓ2 x) (ℓ3 x)) x := by
  have H := (((hc2.add ((hc1.mul hl1).const_mul (2 : ℝ))).add (hc0.mul (hl2.add (hl1.pow 2))))).mul hl0.exp
  refine (H.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [cutExp2, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [cutExp3, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    push_cast
    ring

end CutExp

end InteractingSLE.ZhanGT4
