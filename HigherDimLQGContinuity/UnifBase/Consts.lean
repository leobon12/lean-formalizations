import HigherDimLQGContinuity.UnifBase.Hyp
import HigherDimLQGMetric.DGZ.NiceBoxDefs

/-!
# The constant package (A.7) of the uniform port (packet U0)

Blueprint Part D, `d:lem-consts` (NA3 R3, §2.5, §2.15 rows 1, 3, 9, 11; errata ED8, ED9). For `b > 0` and `μ > 0`,
defined in this order (functions of `(d, b, μ)`; `η` depends on `μ` only):

* `uEta μ = μ/2`, `uQ0 d b μ = √(2d) + μ/(2b)`, `uQstar d b μ = √(2d) + μ/b` (in `UnifBase/Hyp.lean`);
* `uAlpha = (Q_*²/2 - d)/4`, `uBeta = d + 2α`, `uLambda = α/(4(α + d))`;
* `uQbar = (√(2β) + Q_*)/2`, `uNu = b(Q_* - Q̄)`, `uTheta = νλ/(8(3 + λ))`.

`uConsts_spec` collects every inequality of `d:lem-consts`: `α > 0`, `d + α < β < Q_*²/2`, `β - d > α`,
`(2d + α)λ < α`, `λ < α/(2(α + d)) < 1/2`, `√(2β) < Q̄ < Q_*`, `ν > 0` (and `λ, θ > 0`), and, for every
`ξ ∈ S(b, μ)`: (i) `0 < η < ξ(Q(ξ) - √(2d))`; (ii) `Q(ξ) - η/ξ ≥ Q₀`; (iii) `ϕ(ξ) - ξQ̄ ≥ ν`; (iv) `Q(ξ) ≥ Q_*`;
(v) `μ ≤ ϕ(ξ) ≤ 1 + √(2d) b` (ruling N8: `L_ϕ = √(2d)`, PAR's `phiXi_le_one_add_sqrt_mul`). Each inequality is also
a separate named lemma, and the `ξ`-clauses have `UHyp` forms (`UHyp.uEta_lt` …).

The fixed-`ξ` lemmas `DGZ.dgzLambda_lt_half` and `DGZ.dgzLambda_lt_alpha_div` are restated for `λ = α/(4(α + d))` with
`α > 0` free (`u0_lambda_lt_half`, `u0_lambda_lt_alpha_div`); the fixed-`ξ` `dgzAlpha d Q = Q²/4 - d/2` is
`2 · uAlpha` at `Q = Q_*` (`dgzAlpha_uQstar`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd IsLFPPKernel)

variable {d : ℕ}

/-! ### The constants -/

/-- `η = μ/2`, the margin of the coarse event (ED8). -/
def uEta (μ : ℝ) : ℝ := μ / 2

/-- `Q₀ = √(2d) + μ/(2b)`, the slope of the coarse event `𝒢_n ⊇ {sup h_n ≤ n Q₀ log 2}` (ED8; in general
`Q₀(η) = √(2d) + (μ - η)/b`). -/
def uQ0 (d : ℕ) (b μ : ℝ) : ℝ := Real.sqrt (2 * d) + μ / (2 * b)

/-- `α = (Q_*²/2 - d)/4` ((A.7)). -/
def uAlpha (d : ℕ) (b μ : ℝ) : ℝ := (uQstar d b μ ^ 2 / 2 - d) / 4

/-- `β = d + 2α` ((A.7)). -/
def uBeta (d : ℕ) (b μ : ℝ) : ℝ := d + 2 * uAlpha d b μ

/-- `λ = α/(4(α + d))` ((A.7); DGZ (5.3) with `α` from `Q_*`). -/
def uLambda (d : ℕ) (b μ : ℝ) : ℝ := uAlpha d b μ / (4 * (uAlpha d b μ + d))

/-- `Q̄ = (√(2β) + Q_*)/2`, the midpoint of `(√(2β), Q_*)` ((A.7), ED9). -/
def uQbar (d : ℕ) (b μ : ℝ) : ℝ := (Real.sqrt (2 * uBeta d b μ) + uQstar d b μ) / 2

/-- `ν = b(Q_* - Q̄)`, the uniform lower bound of `ϕ - ξQ̄` on `S(b, μ)` ((A.7), gap form, ED9). -/
def uNu (d : ℕ) (b μ : ℝ) : ℝ := b * (uQstar d b μ - uQbar d b μ)

/-- `θ = νλ/(8(3 + λ))` ((A.8), ED10). -/
def uTheta (d : ℕ) (b μ : ℝ) : ℝ := uNu d b μ * uLambda d b μ / (8 * (3 + uLambda d b μ))

/-! ### `λ = α/(4(α + d))` with `α > 0` free (restating `DGZ.dgzLambda_lt_half`, `DGZ.dgzLambda_lt_alpha_div`) -/

theorem u0_lambda_pos {α : ℝ} (hα : 0 < α) : 0 < α / (4 * (α + d)) := by
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  positivity

/-- `λ < α/(2(α + d))` (DGZ Lemma 5.9; `DGZ.dgzLambda_lt_half` with `α` free). -/
theorem u0_lambda_lt_half {α : ℝ} (hα : 0 < α) : α / (4 * (α + d)) < α / (2 * (α + d)) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  apply div_lt_div_of_pos_left hα (by positivity)
  linarith

/-- `λ < α/(2d + α)` (DGZ Lemma 5.8; `DGZ.dgzLambda_lt_alpha_div` with `α` free). -/
theorem u0_lambda_lt_alpha_div {α : ℝ} (hα : 0 < α) : α / (4 * (α + d)) < α / (2 * d + α) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  apply div_lt_div_of_pos_left hα (by positivity)
  linarith

/-- `(2d + α)λ < α`, the form of `u0_lambda_lt_alpha_div` used in (A.7). -/
theorem u0_two_mul_add_mul_lambda_lt {α : ℝ} (hα : 0 < α) :
    (2 * d + α) * (α / (4 * (α + d))) < α := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h := u0_lambda_lt_alpha_div (d := d) hα
  rwa [lt_div_iff₀ (by positivity), mul_comm] at h

/-- `α/(2(α + d)) < 1/2` for `d ≥ 1`. -/
theorem u0_alpha_div_lt_half (hd : 0 < d) {α : ℝ} (hα : 0 < α) : α / (2 * (α + d)) < 1 / 2 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [div_lt_iff₀ (by positivity)]
  linarith

/-! ### The constant inequalities -/

section Consts

variable {b μ : ℝ}

theorem uQstar_eq : uQstar d b μ = Real.sqrt (2 * d) + μ / b := rfl

theorem sqrt_lt_uQstar (hb : 0 < b) (hμ : 0 < μ) : Real.sqrt (2 * d) < uQstar d b μ := by
  unfold uQstar
  have : 0 < μ / b := div_pos hμ hb
  linarith

theorem uQstar_pos (hb : 0 < b) (hμ : 0 < μ) : 0 < uQstar d b μ :=
  (Real.sqrt_nonneg _).trans_lt (sqrt_lt_uQstar hb hμ)

/-- `2d < Q_*²`. -/
theorem two_mul_lt_uQstar_sq (hb : 0 < b) (hμ : 0 < μ) : 2 * (d : ℝ) < uQstar d b μ ^ 2 := by
  have h := sqrt_lt_uQstar (d := d) hb hμ
  have h2 : Real.sqrt (2 * d) ^ 2 = 2 * d := Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg (2 * (d : ℝ))]

/-- `b Q_* = b √(2d) + μ`, i.e. `μ = b(Q_* - √(2d))`. -/
theorem mul_uQstar (hb : 0 < b) : b * uQstar d b μ = b * Real.sqrt (2 * d) + μ := by
  unfold uQstar
  field_simp

/-- The fixed-`ξ` constant `DGZ.dgzAlpha d Q = Q²/4 - d/2` at `Q = Q_*` is `2α`. -/
theorem dgzAlpha_uQstar : DGZ.dgzAlpha d (uQstar d b μ) = 2 * uAlpha d b μ := by
  unfold DGZ.dgzAlpha uAlpha
  ring

theorem uAlpha_pos (hb : 0 < b) (hμ : 0 < μ) : 0 < uAlpha d b μ := by
  unfold uAlpha
  have := two_mul_lt_uQstar_sq (d := d) hb hμ
  linarith

theorem uBeta_eq : uBeta d b μ = d + 2 * uAlpha d b μ := rfl

theorem add_uAlpha_lt_uBeta (hb : 0 < b) (hμ : 0 < μ) : (d : ℝ) + uAlpha d b μ < uBeta d b μ := by
  unfold uBeta
  linarith [uAlpha_pos (d := d) hb hμ]

theorem uBeta_lt_uQstar_sq (hb : 0 < b) (hμ : 0 < μ) : uBeta d b μ < uQstar d b μ ^ 2 / 2 := by
  have hα := uAlpha_pos (d := d) hb hμ
  unfold uBeta
  unfold uAlpha at hα ⊢
  linarith

theorem uAlpha_lt_uBeta_sub (hb : 0 < b) (hμ : 0 < μ) : uAlpha d b μ < uBeta d b μ - d := by
  unfold uBeta
  linarith [uAlpha_pos (d := d) hb hμ]

theorem uBeta_pos (hb : 0 < b) (hμ : 0 < μ) : 0 < uBeta d b μ := by
  unfold uBeta
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith [uAlpha_pos (d := d) hb hμ]

theorem uLambda_pos (hb : 0 < b) (hμ : 0 < μ) : 0 < uLambda d b μ :=
  u0_lambda_pos (uAlpha_pos hb hμ)

theorem uLambda_lt_half (hb : 0 < b) (hμ : 0 < μ) :
    uLambda d b μ < uAlpha d b μ / (2 * (uAlpha d b μ + d)) :=
  u0_lambda_lt_half (uAlpha_pos hb hμ)

theorem uLambda_lt_alpha_div (hb : 0 < b) (hμ : 0 < μ) :
    uLambda d b μ < uAlpha d b μ / (2 * d + uAlpha d b μ) :=
  u0_lambda_lt_alpha_div (uAlpha_pos hb hμ)

theorem two_mul_add_uAlpha_mul_uLambda_lt (hb : 0 < b) (hμ : 0 < μ) :
    (2 * d + uAlpha d b μ) * uLambda d b μ < uAlpha d b μ :=
  u0_two_mul_add_mul_lambda_lt (uAlpha_pos hb hμ)

theorem uAlpha_div_lt_half (hd : 0 < d) (hb : 0 < b) (hμ : 0 < μ) :
    uAlpha d b μ / (2 * (uAlpha d b μ + d)) < 1 / 2 :=
  u0_alpha_div_lt_half hd (uAlpha_pos hb hμ)

theorem uLambda_lt_one_half (hd : 0 < d) (hb : 0 < b) (hμ : 0 < μ) : uLambda d b μ < 1 / 2 :=
  (uLambda_lt_half hb hμ).trans (uAlpha_div_lt_half hd hb hμ)

/-- `√(2β) < Q_*` (from `2β < Q_*²`). -/
theorem sqrt_two_uBeta_lt_uQstar (hb : 0 < b) (hμ : 0 < μ) :
    Real.sqrt (2 * uBeta d b μ) < uQstar d b μ := by
  rw [Real.sqrt_lt' (uQstar_pos hb hμ)]
  linarith [uBeta_lt_uQstar_sq (d := d) hb hμ]

theorem sqrt_two_uBeta_lt_uQbar (hb : 0 < b) (hμ : 0 < μ) :
    Real.sqrt (2 * uBeta d b μ) < uQbar d b μ := by
  unfold uQbar
  linarith [sqrt_two_uBeta_lt_uQstar (d := d) hb hμ]

theorem uQbar_lt_uQstar (hb : 0 < b) (hμ : 0 < μ) : uQbar d b μ < uQstar d b μ := by
  unfold uQbar
  linarith [sqrt_two_uBeta_lt_uQstar (d := d) hb hμ]

/-- `√(2d) < Q̄` (as `β > d`). -/
theorem sqrt_lt_uQbar (hb : 0 < b) (hμ : 0 < μ) : Real.sqrt (2 * d) < uQbar d b μ := by
  have h1 : Real.sqrt (2 * d) < Real.sqrt (2 * uBeta d b μ) := by
    refine Real.sqrt_lt_sqrt (by positivity) ?_
    have := add_uAlpha_lt_uBeta (d := d) hb hμ
    linarith [uAlpha_pos (d := d) hb hμ]
  exact h1.trans (sqrt_two_uBeta_lt_uQbar hb hμ)

theorem uNu_pos (hb : 0 < b) (hμ : 0 < μ) : 0 < uNu d b μ := by
  unfold uNu
  exact mul_pos hb (by linarith [uQbar_lt_uQstar (d := d) hb hμ])

/-- `ν = μ - b(Q̄ - √(2d))`. -/
theorem uNu_eq_sub (hb : 0 < b) : uNu d b μ = μ - b * (uQbar d b μ - Real.sqrt (2 * d)) := by
  unfold uNu
  have := mul_uQstar (d := d) (μ := μ) hb
  linarith

theorem uTheta_pos (hb : 0 < b) (hμ : 0 < μ) : 0 < uTheta d b μ := by
  unfold uTheta
  have := uNu_pos (d := d) hb hμ
  have := uLambda_pos (d := d) hb hμ
  positivity

theorem uEta_pos (hμ : 0 < μ) : 0 < uEta μ := by
  unfold uEta
  linarith

theorem uEta_lt (hμ : 0 < μ) : uEta μ < μ := by
  unfold uEta
  linarith

end Consts

/-! ### The `ξ`-clauses (i)–(v) on `S(b, μ)` -/

section Xi

variable {b μ ξ : ℝ}

/-- (i) `0 < η < ξ(Q(ξ) - √(2d))` on `S(b, μ)`. -/
theorem uEta_lt_of_mem_uSbm (hμ : 0 < μ) (h : ξ ∈ uSbm d b μ) :
    0 < uEta μ ∧ uEta μ < ξ * (distExp d ξ - Real.sqrt (2 * d)) :=
  ⟨uEta_pos hμ, (uEta_lt hμ).trans_le h.2.2⟩

/-- (ii) `Q(ξ) - η/ξ ≥ Q₀ = √(2d) + μ/(2b)` on `S(b, μ)`. -/
theorem uQ0_le_of_mem_uSbm (hμ : 0 < μ) (h : ξ ∈ uSbm d b μ) :
    uQ0 d b μ ≤ distExp d ξ - uEta μ / ξ := by
  obtain ⟨hξ, hξb, hg⟩ := h
  have hb : 0 < b := hξ.trans_le hξb
  -- `Q - η/ξ - √(2d) = (gap - η)/ξ ≥ (μ/2)/ξ ≥ (μ/2)/b`
  have h1 : μ / 2 ≤ ξ * (distExp d ξ - Real.sqrt (2 * d)) - uEta μ := by
    unfold uEta
    linarith
  have h2 : (μ / 2) / b ≤ (μ / 2) / ξ := div_le_div_of_nonneg_left (by linarith) hξ hξb
  have h3 : (μ / 2) / ξ ≤ distExp d ξ - Real.sqrt (2 * d) - uEta μ / ξ := by
    rw [div_le_iff₀ hξ, sub_mul, div_mul_cancel₀ _ hξ.ne']
    linarith
  have e : μ / (2 * b) = (μ / 2) / b := by rw [div_div]
  unfold uQ0
  rw [e]
  linarith

/-- (iii) `ϕ(ξ) - ξQ̄ ≥ ν` on `S(b, μ)` (gap form: `ϕ - ξQ̄ = gap - ξ(Q̄ - √(2d)) ≥ μ - b(Q̄ - √(2d)) = ν`). -/
theorem uNu_le_of_mem_uSbm (hμ : 0 < μ) (h : ξ ∈ uSbm d b μ) :
    uNu d b μ ≤ ξ * distExp d ξ - ξ * uQbar d b μ := by
  obtain ⟨hξ, hξb, hg⟩ := h
  have hb : 0 < b := hξ.trans_le hξb
  have hQ := sqrt_lt_uQbar (d := d) hb hμ
  have h1 : ξ * (uQbar d b μ - Real.sqrt (2 * d)) ≤ b * (uQbar d b μ - Real.sqrt (2 * d)) :=
    mul_le_mul_of_nonneg_right hξb (by linarith)
  rw [uNu_eq_sub hb]
  have e : ξ * distExp d ξ - ξ * uQbar d b μ =
      ξ * (distExp d ξ - Real.sqrt (2 * d)) - ξ * (uQbar d b μ - Real.sqrt (2 * d)) := by ring
  rw [e]
  linarith

/-- (iv) `Q(ξ) ≥ Q_*` on `S(b, μ)` (`μ > 0`). -/
theorem uQstar_le_of_mem_uSbm (hμ : 0 < μ) (h : ξ ∈ uSbm d b μ) : uQstar d b μ ≤ distExp d ξ := by
  obtain ⟨hξ, hξb, hg⟩ := h
  have h1 : μ / b ≤ μ / ξ := div_le_div_of_nonneg_left hμ.le hξ hξb
  have h2 : μ / ξ ≤ distExp d ξ - Real.sqrt (2 * d) := by
    rw [div_le_iff₀ hξ]
    linarith
  unfold uQstar
  linarith

/-- (v) `μ ≤ ϕ(ξ) ≤ 1 + √(2d) b` on `S(b, μ)` (`d ≥ 2`; ruling N8: `L_ϕ = √(2d)`). -/
theorem phi_mem_of_mem_uSbm (hd : 2 ≤ d) (h : ξ ∈ uSbm d b μ) :
    μ ≤ ξ * distExp d ξ ∧ ξ * distExp d ξ ≤ 1 + Real.sqrt (2 * d) * b := by
  obtain ⟨hξ, hξb, hg⟩ := h
  constructor
  · have h0 : 0 ≤ ξ * Real.sqrt (2 * d) := mul_nonneg hξ.le (Real.sqrt_nonneg _)
    have e : ξ * distExp d ξ = ξ * (distExp d ξ - Real.sqrt (2 * d)) + ξ * Real.sqrt (2 * d) := by
      ring
    rw [e]
    linarith
  · have h1 := phiXi_le_one_add_sqrt_mul hd hξ.le
    rw [phiXi_of_pos hξ] at h1
    have h2 : Real.sqrt (2 * d) * ξ ≤ Real.sqrt (2 * d) * b :=
      mul_le_mul_of_nonneg_left hξb (Real.sqrt_nonneg _)
    linarith

/-! #### The same clauses under `UHyp` (for consumers of the uniform port) -/

theorem UHyp.uEta_lt {κ : Rd d → ℝ} (h : UHyp d κ b μ ξ) (hμ : 0 < μ) :
    0 < uEta μ ∧ uEta μ < ξ * (distExp d ξ - Real.sqrt (2 * d)) :=
  uEta_lt_of_mem_uSbm hμ h.mem_uSbm

theorem UHyp.uQ0_le {κ : Rd d → ℝ} (h : UHyp d κ b μ ξ) (hμ : 0 < μ) :
    uQ0 d b μ ≤ distExp d ξ - uEta μ / ξ :=
  uQ0_le_of_mem_uSbm hμ h.mem_uSbm

theorem UHyp.uNu_le {κ : Rd d → ℝ} (h : UHyp d κ b μ ξ) (hμ : 0 < μ) :
    uNu d b μ ≤ ξ * distExp d ξ - ξ * uQbar d b μ :=
  uNu_le_of_mem_uSbm hμ h.mem_uSbm

end Xi

/-! ### The package -/

/-- **`d:lem-consts`** (the constant package (A.7)). Let `d ≥ 2`, `b > 0` and `μ > 0`. Then `α > 0`,
`d + α < β < Q_*²/2`, `β - d > α`, `(2d + α)λ < α`, `0 < λ < α/(2(α + d)) < 1/2`, `√(2β) < Q̄ < Q_*`, `ν > 0` and
`θ > 0`; and for every `ξ ∈ S(b, μ)`: (i) `0 < η < ξ(Q(ξ) - √(2d))`; (ii) `Q(ξ) - η/ξ ≥ Q₀`; (iii) `ϕ(ξ) - ξQ̄ ≥ ν`;
(iv) `Q(ξ) ≥ Q_*`; (v) `μ ≤ ϕ(ξ) ≤ 1 + √(2d) b` (`ϕ(ξ) = ξ Q(ξ)`). -/
theorem uConsts_spec (hd : 2 ≤ d) {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) :
    0 < uAlpha d b μ ∧ (d : ℝ) + uAlpha d b μ < uBeta d b μ ∧
    uBeta d b μ < uQstar d b μ ^ 2 / 2 ∧ uAlpha d b μ < uBeta d b μ - d ∧
    (2 * d + uAlpha d b μ) * uLambda d b μ < uAlpha d b μ ∧
    0 < uLambda d b μ ∧ uLambda d b μ < uAlpha d b μ / (2 * (uAlpha d b μ + d)) ∧
    uAlpha d b μ / (2 * (uAlpha d b μ + d)) < 1 / 2 ∧
    Real.sqrt (2 * uBeta d b μ) < uQbar d b μ ∧ uQbar d b μ < uQstar d b μ ∧
    0 < uNu d b μ ∧ 0 < uTheta d b μ ∧
    ∀ ξ ∈ uSbm d b μ,
      (0 < uEta μ ∧ uEta μ < ξ * (distExp d ξ - Real.sqrt (2 * d))) ∧
      uQ0 d b μ ≤ distExp d ξ - uEta μ / ξ ∧
      uNu d b μ ≤ ξ * distExp d ξ - ξ * uQbar d b μ ∧
      uQstar d b μ ≤ distExp d ξ ∧
      (μ ≤ ξ * distExp d ξ ∧ ξ * distExp d ξ ≤ 1 + Real.sqrt (2 * d) * b) := by
  have hd0 : 0 < d := by omega
  exact ⟨uAlpha_pos hb hμ, add_uAlpha_lt_uBeta hb hμ, uBeta_lt_uQstar_sq hb hμ,
    uAlpha_lt_uBeta_sub hb hμ, two_mul_add_uAlpha_mul_uLambda_lt hb hμ, uLambda_pos hb hμ,
    uLambda_lt_half hb hμ, uAlpha_div_lt_half hd0 hb hμ, sqrt_two_uBeta_lt_uQbar hb hμ,
    uQbar_lt_uQstar hb hμ, uNu_pos hb hμ, uTheta_pos hb hμ, fun ξ hξ =>
      ⟨uEta_lt_of_mem_uSbm hμ hξ, uQ0_le_of_mem_uSbm hμ hξ, uNu_le_of_mem_uSbm hμ hξ,
        uQstar_le_of_mem_uSbm hμ hξ, phi_mem_of_mem_uSbm hd hξ⟩⟩

end HigherDimLQGContinuity
