/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The stopped dual coupling: the algebra of the two-parameter martingale (Part A.1.2)

Packet PROVE-ZHAN-GT4-A. Source: Astra, *Follow-up proofs and dependency audit*, §A.1.1–A.1.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L190–L296, ruling R38; with A.6 item 3, the corrected integrand
`2A²_{1,1}A²_{2,1}/E⁴` of (D4)):

> Here is the algebraic martingale verification in a form suitable for a symbolic Lean calculation. First suppose
> `W_j` has zero drift. Using (D3)–(D5), the coefficient of `dW_j` in `d_j M̃/M̃` is
> `q_j = α_j A_{j,2}/A_{j,1} − A_{j,1}/(2E_{j,0}) + Σ_m r_{j,m} A_{j,1}/E_{j,m}` (D7). … The quadratic covariations
> between the factors with stochastic parts are exactly the negatives of these four summands. Hence the drift is
> zero.

This file carries out that calculation exactly. Along the time `t_j` of curve `j` (the other time frozen), with
`dW_j = √κ dB` (`κ = κ_j`), the logarithmic differentials of the factors of
`M̃ = A^{α₁}_{1,1} A^{α₂}_{2,1} E^{−1/2} F^{−Λ} ∏_m (B^{γ_m}_{m,1} |E_{1,m}|^{r_{1,m}} |E_{2,m}|^{r_{2,m}}) ∏_{m<n} |C_{mn}|^{δ_{mn}}`
are read off (D3)–(D5) (Itô: `d log X = dX/X − ½ d⟨X⟩/X²`):

| factor | drift of `d log` | `dB` coefficient |
|---|---|---|
| `A^{α}_{j,1}` | `α((1 − κ)/2 · A₂²/A₁² + (κ/2 − 4/3) A₃/A₁)` | `α √κ A₂/A₁` |
| `A^{α'}_{k,1}` | `α' (−2A₁²/E₀²)` | — |
| `E^{−1/2}` | `−½((κ/2 − 3) A₂/E₀ + 2A₁²/E₀² − κA₁²/(2E₀²))` | `−½ √κ A₁/E₀` |
| `F^{−Λ}` | `−Λ(¼ A₂²/A₁² − ⅙ A₃/A₁)` ((D5)) | — |
| `B^{γ_m}_{m,1}` | `γ_m (−2A₁²/E_m²)` | — |
| `|E_{j,m}|^{r_m}` | `r_m((κ/2 − 3) A₂/E_m + 2A₁²/E_m² − κA₁²/(2E_m²))` | `r_m √κ A₁/E_m` |
| `|E_{k,m}|^{r'_m}` | `r'_m (−2A₁²/(E₀E_m))` | — |
| `|C_{mn}|^{δ_{mn}}` | `δ_{mn} (−2A₁²/(E_mE_n))` | — |

Here `A_ℓ = A_{j,ℓ}`, `E₀ = E_{j,0} = A_{j,0} − A_{k,0}`, `E_m = E_{j,m} = A_{j,0} − B_{m,0}`, `r_m = r_{j,m}`, and the other
curve's exponents are `α' = α_k`, `r'_m = r_{k,m}`. (`E_{k,m} = E_m − E₀` and `C_{mn} = E_n − E_m`, so their drifts
reduce to the displayed ones.) The drift of `M̃/M̃` is the sum of the drifts plus `½ κ q²`, `q` the total `dB`
coefficient divided by `√κ` (D7).

## Main results

* `dualLambda_dual`, `dualGamma_dual`, `dualDelta_dual`, `dualAlpha_dual`: with `κ₁κ₂ = 16` and
  `ρ_{2,m} = −(κ₂/4) ρ_{1,m}` (i.e. `r_{2,m} = −(κ₁/4) r_{1,m}`), the constants `Λ, γ_m, δ_{mn}` are the same for both
  curves, and `α_k = (3κ_j − 8)/16` (L247–L249).
* `dualCharge_dual`: the charges `ρ_{j,m} = C_m(κ_j − 4)` satisfy `ρ_{2,m} = −(κ₂/4) ρ_{1,m}`.
* `dualDrift_eq_zero`: **the drift of `M̃` vanishes** for zero-drift `W_j` (L270–L281).
* `dualQuotient_drift_eq_zero`: (D8)'s quotient-rule identity `(q − q₀)b + κq₀² − κqq₀ = 0`, `q₀ = b/κ`.
-/

set_option autoImplicit false

open Finset

namespace InteractingSLE.ZhanGT4

/-! ### The constants of (D6) -/

/-- `α_j = (6 − κ_j)/(2κ_j)`. -/
noncomputable def dualAlpha (κ : ℝ) : ℝ := (6 - κ) / (2 * κ)

/-- `Λ = (8 − 3κ_j)(6 − κ_j)/(2κ_j)`. -/
noncomputable def dualLambda (κ : ℝ) : ℝ := (8 - 3 * κ) * (6 - κ) / (2 * κ)

/-- `γ_m = (κ_j/4) r_{j,m}(r_{j,m} − 1) + r_{j,m}`. -/
noncomputable def dualGamma (κ r : ℝ) : ℝ := κ / 4 * r * (r - 1) + r

/-- `δ_{mn} = (κ_j/2) r_{j,m} r_{j,n}`. -/
noncomputable def dualDelta (κ r r' : ℝ) : ℝ := κ / 2 * r * r'

/-- The dual parameter and the dual exponents: with `κ₂ = 16/κ₁` and `r_{2,m} = −(κ₁/4) r_{1,m}`, `Λ` is the same. -/
theorem dualLambda_dual {κ : ℝ} (hκ : κ ≠ 0) : dualLambda (16 / κ) = dualLambda κ := by
  unfold dualLambda
  field_simp
  ring

theorem dualGamma_dual {κ : ℝ} (hκ : κ ≠ 0) (r : ℝ) :
    dualGamma (16 / κ) (-(κ / 4) * r) = dualGamma κ r := by
  unfold dualGamma
  field_simp
  ring

theorem dualDelta_dual {κ : ℝ} (hκ : κ ≠ 0) (r r' : ℝ) :
    dualDelta (16 / κ) (-(κ / 4) * r) (-(κ / 4) * r') = dualDelta κ r r' := by
  unfold dualDelta
  field_simp
  ring

/-- `α_k = (3κ_j − 8)/16` for the dual parameter `κ_k = 16/κ_j`. -/
theorem dualAlpha_dual {κ : ℝ} (hκ : κ ≠ 0) : dualAlpha (16 / κ) = (3 * κ - 8) / 16 := by
  unfold dualAlpha
  field_simp
  ring

/-- The charges `ρ_{j,m} = C_m(κ_j − 4)` of §A.1 satisfy `ρ_{2,m} = −(κ₂/4) ρ_{1,m}` when `κ₁κ₂ = 16`; equivalently
`r_{2,m} = −(κ₁/4) r_{1,m}` for `r_{j,m} = ρ_{j,m}/κ_j`. -/
theorem dualCharge_dual {κ₁ κ₂ : ℝ} (h : κ₁ * κ₂ = 16) (C : ℝ) :
    C * (κ₂ - 4) = -(κ₂ / 4) * (C * (κ₁ - 4)) ∧
      (κ₁ ≠ 0 → κ₂ ≠ 0 → C * (κ₂ - 4) / κ₂ = -(κ₁ / 4) * (C * (κ₁ - 4) / κ₁)) := by
  refine ⟨by linear_combination (C / 4) * h, fun h1 h2 => ?_⟩
  field_simp
  linear_combination C * h

/-! ### The drift of `M̃` -/

/-- The sum over ordered pairs `m < n`. -/
def pairSum {n : ℕ} (f : Fin n → Fin n → ℝ) : ℝ :=
  ∑ p ∈ (univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), f p.1 p.2

/-- `(Σ x)² = Σ x² + 2 Σ_{m<n} x_m x_n`. -/
theorem sq_sum_eq_sum_sq_add_pairSum {n : ℕ} (x : Fin n → ℝ) :
    (∑ m, x m) ^ 2 = ∑ m, x m ^ 2 + 2 * pairSum (fun m n => x m * x n) := by
  set f : Fin n × Fin n → ℝ := fun p => x p.1 * x p.2 with hf
  have hfull : (∑ m, x m) ^ 2 = ∑ p : Fin n × Fin n, f p := by
    rw [sq, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin n × Fin n))
    (fun p => p.1 < p.2) f
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)) (fun p => p.1 = p.2) f
  have hdiag : ∑ p ∈ ((univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => p.1 = p.2), f p = ∑ m, x m ^ 2 := by
    refine Finset.sum_nbij' Prod.fst (fun m => (m, m)) (fun _ _ => mem_univ _) (fun m _ => ?_)
      (fun p hp => ?_) (fun _ _ => rfl) (fun p hp => ?_)
    · simp
    · simp only [mem_filter, mem_univ, true_and] at hp
      exact Prod.ext rfl hp.2
    · simp only [mem_filter, mem_univ, true_and] at hp
      simp only [hf, sq]
      rw [hp.2]
  have hlow : ∑ p ∈ ((univ : Finset (Fin n × Fin n)).filter (fun p => ¬ p.1 < p.2)).filter
      (fun p => ¬ p.1 = p.2), f p = pairSum (fun m n => x m * x n) := by
    unfold pairSum
    refine Finset.sum_nbij' Prod.swap Prod.swap (fun p hp => ?_) (fun p hp => ?_)
      (fun p _ => Prod.swap_swap p) (fun p _ => Prod.swap_swap p) (fun p _ => ?_)
    · simp only [mem_filter, mem_univ, true_and, not_lt] at hp ⊢
      exact lt_of_le_of_ne hp.1 (Ne.symm hp.2)
    · simp only [mem_filter, mem_univ, true_and, not_lt] at hp ⊢
      exact ⟨hp.le, hp.ne'⟩
    · simp only [hf, Prod.fst_swap, Prod.snd_swap]
      ring
  have hupper : ∑ p ∈ (univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2), f p =
      pairSum (fun m n => x m * x n) := rfl
  rw [hfull, ← hsplit, ← hsplit2, hdiag, hlow, hupper]
  ring

/-- **(D7)**: the coefficient of `dW_j` in `d_j M̃/M̃`. -/
noncomputable def dualQ (κ A1 A2 E0 : ℝ) {n : ℕ} (r E : Fin n → ℝ) : ℝ :=
  dualAlpha κ * (A2 / A1) - A1 / (2 * E0) + ∑ m, r m * (A1 / E m)

/-- **The drift of `d_j M̃/M̃`** for zero-drift `W_j` (`dW_j = √κ dB`): the sum of the drifts of the logarithmic
differentials of the factors (the table in the module docstring), plus `½ κ q²`. -/
noncomputable def dualDrift (κ A1 A2 A3 E0 : ℝ) {n : ℕ} (r E : Fin n → ℝ) : ℝ :=
  dualAlpha κ * ((1 - κ) / 2 * (A2 ^ 2 / A1 ^ 2) + (κ / 2 - 4 / 3) * (A3 / A1))
    + (3 * κ - 8) / 16 * (-2 * A1 ^ 2 / E0 ^ 2)
    - 1 / 2 * ((κ / 2 - 3) * (A2 / E0) + 2 * A1 ^ 2 / E0 ^ 2 - κ * A1 ^ 2 / (2 * E0 ^ 2))
    - dualLambda κ * (1 / 4 * (A2 ^ 2 / A1 ^ 2) - 1 / 6 * (A3 / A1))
    + (∑ m, dualGamma κ (r m) * (-2 * A1 ^ 2 / E m ^ 2))
    + (∑ m, r m * ((κ / 2 - 3) * (A2 / E m) + 2 * A1 ^ 2 / E m ^ 2 - κ * A1 ^ 2 / (2 * E m ^ 2)))
    + (∑ m, -(κ / 4) * r m * (-2 * A1 ^ 2 / (E0 * E m)))
    + pairSum (fun m n => dualDelta κ (r m) (r n) * (-2 * A1 ^ 2 / (E m * E n)))
    + κ / 2 * dualQ κ A1 A2 E0 r E ^ 2

/-- **The drift of `M̃` vanishes** (§A.1.2, L270–L281): for `κ ≠ 0` and nonzero `A_{j,1}`, `E_{j,0}`, `E_{j,m}`,
`dualDrift = 0`. The `A₃/A₁` terms cancel between `α_j` and `Λ` (the Schwarzian terms), the `A₂²/A₁²` terms between
`α_j`, `Λ` and `½κα_j²`, and each remaining group against its covariation. -/
theorem dualDrift_eq_zero {κ A1 A2 A3 E0 : ℝ} {n : ℕ} (r E : Fin n → ℝ) (hκ : κ ≠ 0)
    (hA1 : A1 ≠ 0) (hE0 : E0 ≠ 0) (hE : ∀ m, E m ≠ 0) :
    dualDrift κ A1 A2 A3 E0 r E = 0 := by
  set a := dualAlpha κ * (A2 / A1) - A1 / (2 * E0) with ha
  set x : Fin n → ℝ := fun m => r m * (A1 / E m) with hx
  have hq : dualQ κ A1 A2 E0 r E = a + ∑ m, x m := rfl
  have hsq := sq_sum_eq_sum_sq_add_pairSum x
  -- the summands over one mark cancel
  have hper : ∀ m, dualGamma κ (r m) * (-2 * A1 ^ 2 / E m ^ 2)
      + r m * ((κ / 2 - 3) * (A2 / E m) + 2 * A1 ^ 2 / E m ^ 2 - κ * A1 ^ 2 / (2 * E m ^ 2))
      + -(κ / 4) * r m * (-2 * A1 ^ 2 / (E0 * E m))
      + κ / 2 * x m ^ 2 + κ * a * x m = 0 := by
    intro m
    have hEm := hE m
    simp only [hx, ha, dualGamma, dualAlpha]
    field_simp
    ring
  -- the summands over one pair cancel
  have hpair : ∀ m n, dualDelta κ (r m) (r n) * (-2 * A1 ^ 2 / (E m * E n))
      + κ * (x m * x n) = 0 := by
    intro m n
    have hEm := hE m
    have hEn := hE n
    simp only [hx, dualDelta]
    field_simp
    ring
  -- the scalar terms cancel (the Schwarzian and `A₂²/A₁²` terms, and the `E₀` terms)
  have hscal : dualAlpha κ * ((1 - κ) / 2 * (A2 ^ 2 / A1 ^ 2) + (κ / 2 - 4 / 3) * (A3 / A1))
      + (3 * κ - 8) / 16 * (-2 * A1 ^ 2 / E0 ^ 2)
      - 1 / 2 * ((κ / 2 - 3) * (A2 / E0) + 2 * A1 ^ 2 / E0 ^ 2 - κ * A1 ^ 2 / (2 * E0 ^ 2))
      - dualLambda κ * (1 / 4 * (A2 ^ 2 / A1 ^ 2) - 1 / 6 * (A3 / A1))
      + κ / 2 * a ^ 2 = 0 := by
    simp only [ha, dualAlpha, dualLambda]
    field_simp
    ring
  have h1 : ∑ m, (dualGamma κ (r m) * (-2 * A1 ^ 2 / E m ^ 2)
      + r m * ((κ / 2 - 3) * (A2 / E m) + 2 * A1 ^ 2 / E m ^ 2 - κ * A1 ^ 2 / (2 * E m ^ 2))
      + -(κ / 4) * r m * (-2 * A1 ^ 2 / (E0 * E m))
      + κ / 2 * x m ^ 2 + κ * a * x m) = 0 :=
    Finset.sum_eq_zero fun m _ => hper m
  have e1 : ∑ m, (dualGamma κ (r m) * (-2 * A1 ^ 2 / E m ^ 2)
      + r m * ((κ / 2 - 3) * (A2 / E m) + 2 * A1 ^ 2 / E m ^ 2 - κ * A1 ^ 2 / (2 * E m ^ 2))
      + -(κ / 4) * r m * (-2 * A1 ^ 2 / (E0 * E m))
      + κ / 2 * x m ^ 2 + κ * a * x m) =
      (∑ m, dualGamma κ (r m) * (-2 * A1 ^ 2 / E m ^ 2))
      + (∑ m, r m * ((κ / 2 - 3) * (A2 / E m) + 2 * A1 ^ 2 / E m ^ 2
          - κ * A1 ^ 2 / (2 * E m ^ 2)))
      + (∑ m, -(κ / 4) * r m * (-2 * A1 ^ 2 / (E0 * E m)))
      + κ / 2 * ∑ m, x m ^ 2 + κ * a * ∑ m, x m := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have h2 : pairSum (fun m n => dualDelta κ (r m) (r n) * (-2 * A1 ^ 2 / (E m * E n))
      + κ * (x m * x n)) = 0 := by
    unfold pairSum
    exact Finset.sum_eq_zero fun p _ => hpair p.1 p.2
  have e2 : pairSum (fun m n => dualDelta κ (r m) (r n) * (-2 * A1 ^ 2 / (E m * E n))
      + κ * (x m * x n)) =
      pairSum (fun m n => dualDelta κ (r m) (r n) * (-2 * A1 ^ 2 / (E m * E n)))
      + κ * pairSum (fun m n => x m * x n) := by
    unfold pairSum
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  unfold dualDrift
  rw [hq, add_sq, hsq]
  linear_combination h1 - e1 + h2 - e2 + hscal

/-- **(D8)'s quotient-rule identity**: with `q₀ = b/κ` the drift `(q − q₀) b + κ q₀² − κ q q₀` vanishes, so
`d_j M/M = √κ (q − b/κ) dB` under the marginal law `dW_j = √κ dB + b dt`. -/
theorem dualQuotient_drift_eq_zero {κ : ℝ} (hκ : κ ≠ 0) (q b : ℝ) :
    (q - b / κ) * b + κ * (b / κ) ^ 2 - κ * q * (b / κ) = 0 := by
  field_simp
  ring

end InteractingSLE.ZhanGT4
