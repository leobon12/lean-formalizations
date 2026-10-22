import HigherDimLQGContinuity.Seed.Basic

/-!
# Proposition 3.6 (packet P8b), part 2: the depths and the drift ceiling

Blueprint Part A, Proposition `a:prop36`, "Given `a, ξ, η, u`" and "The ceiling" (NA1 item 28, R11; erratum EA
`a:err-36`). Purely real-variable numerics.

* `p8bN0` is the depth of the start (Lemma 3.2 at pin `10`, radius `R_s`, error `ε'`, confidence `q₀'`);
* `p8bNg` is the depth of each step (Proposition 3.3 at slack `δ_g = g/2`, error `ε'`, radius `R_s`), chosen so that
  the depth condition of Proposition 3.3 holds and its failure bound is `≤ q₀'` (`p8b_ng_spec`);
* `p8b_ceiling`: with `v = min(v₀/2, u/(160 M_s))` and Proposition 3.5's bounds `g, t∗ ≥ e^{-𝒫}`,
  `log ε∗⁻¹ ≤ 𝒫` (`𝒫 = polyB A k a⁻¹ v⁻¹`), the three drift constraints `τ ≤ t∗`, `τ n₀ ≤ c₃₂`,
  `τ n_g ≤ c₃ g/2` all hold once `τ ≤ exp(-C₆ a^{-B} u^{-B})`, with `B = max(k, 1)` and `C₆` depending only on the
  fixed data.

The ceiling is proved through the single size variable `Y = 𝒫 + log u⁻¹ + 1 ≥ 1`: each of `1/t∗`, `n₀/c₃₂`,
`n_g/(c₃ g/2)` is at most `exp(K Y)` for a constant `K` (`p8b_ceiling_core`), and
`Y ≤ (|A| K_w^B + 2Ξ^B) a^{-B} u^{-B}` with `Ξ = max(ξ̄, 1)`, `K_w = Ξ + 1 + 2Ξ/v₀ + 160 M_s Ξ` (`p8b_ceiling_Y`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGContinuity

/-! ## The depths -/

/-- The depth `n₀ = C₃₂ (1 + log(1 + R_s) + log ε⁻¹ + log q⁻¹)` of the start of Proposition 3.6 (Lemma 3.2). -/
def p8bN0 (C₃₂ Rs ε q : ℝ) : ℝ := C₃₂ * (1 + Real.log (1 + Rs) + Real.log ε⁻¹ + Real.log q⁻¹)

/-- The logarithmic bracket `Λ` of the step depth of Proposition 3.6. -/
def p8bLam (C₃ M₃ Rs ε q δg : ℝ) : ℝ :=
  1 + Real.log (1 + Rs) + Real.log ε⁻¹ + (1 + M₃) * Real.log δg⁻¹ + Real.log q⁻¹ + |Real.log (C₃ * Rs ^ M₃)|

/-- The step depth `n_g = (C₃ + 1/c₃) δ_g^{-M₃} Λ` of Proposition 3.6 (Proposition 3.3 at slack `δ_g = g/2`). -/
def p8bNg (C₃ c₃ M₃ Rs ε q δg : ℝ) : ℝ := (C₃ + 1 / c₃) * δg ^ (-M₃) * p8bLam C₃ M₃ Rs ε q δg

/-- `δ^{-M} = e^{M log δ⁻¹}` for `δ > 0`. -/
theorem p8b_rpow_neg_eq_exp {δ M : ℝ} (hδ : 0 < δ) : δ ^ (-M) = Real.exp (M * Real.log δ⁻¹) := by
  rw [Real.rpow_def_of_pos hδ, Real.log_inv]
  ring_nf

/-- The step depth satisfies the depth condition of Proposition 3.3 and makes its failure bound at most `q`. -/
theorem p8b_ng_spec {C₃ c₃ M₃ Rs ε q δg : ℝ} (hC₃ : 0 < C₃) (hc₃ : 0 < c₃) (hM₃ : 0 < M₃) (hRs : 1 ≤ Rs)
    (hε : 0 < ε) (hε1 : ε < 1) (hq : 0 < q) (hq1 : q ≤ 1) (hδ : 0 < δg) (hδ1 : δg < 1) :
    C₃ * δg ^ (-M₃) * (1 + Real.log (1 + Rs) + Real.log ε⁻¹ + Real.log δg⁻¹) ≤
        p8bNg C₃ c₃ M₃ Rs ε q δg ∧
      C₃ * Rs ^ M₃ * δg ^ (-M₃) * Real.exp (-c₃ * δg ^ M₃ * p8bNg C₃ c₃ M₃ Rs ε q δg) ≤ q := by
  have hlogR : 0 ≤ Real.log (1 + Rs) := Real.log_nonneg (by linarith)
  have hlogε : 0 ≤ Real.log ε⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hε, hε1.le⟩)
  have hlogδ : 0 ≤ Real.log δg⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hδ, hδ1.le⟩)
  have hlogq : 0 ≤ Real.log q⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hq, hq1⟩)
  have hX : 0 < δg ^ (-M₃) := Real.rpow_pos_of_pos hδ _
  set Λ : ℝ := p8bLam C₃ M₃ Rs ε q δg with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, p8bLam]
    have : 0 ≤ (1 + M₃) * Real.log δg⁻¹ := mul_nonneg (by linarith) hlogδ
    have := abs_nonneg (Real.log (C₃ * Rs ^ M₃))
    linarith
  constructor
  · rw [p8bNg, ← hΛ]
    have hbr : 1 + Real.log (1 + Rs) + Real.log ε⁻¹ + Real.log δg⁻¹ ≤ Λ := by
      rw [hΛ, p8bLam]
      have : 0 ≤ M₃ * Real.log δg⁻¹ := mul_nonneg hM₃.le hlogδ
      have := abs_nonneg (Real.log (C₃ * Rs ^ M₃))
      nlinarith
    have hCc : C₃ ≤ C₃ + 1 / c₃ := by
      have : 0 < 1 / c₃ := by positivity
      linarith
    have hbr0 : 0 ≤ 1 + Real.log (1 + Rs) + Real.log ε⁻¹ + Real.log δg⁻¹ := by linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right hCc hX.le) hbr hbr0 (by positivity)
  · -- `c₃ δ^{M₃} n_g = (c₃ C₃ + 1) Λ ≥ Λ`
    have hprod : δg ^ M₃ * δg ^ (-M₃) = 1 := by
      rw [Real.rpow_neg hδ.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hδ _).ne']
    have hexp1 : -c₃ * δg ^ M₃ * p8bNg C₃ c₃ M₃ Rs ε q δg = -((c₃ * C₃ + 1) * Λ) := by
      rw [p8bNg, ← hΛ]
      have hc : c₃ * (C₃ + 1 / c₃) = c₃ * C₃ + 1 := by rw [mul_add, mul_one_div_cancel hc₃.ne']
      calc -c₃ * δg ^ M₃ * ((C₃ + 1 / c₃) * δg ^ (-M₃) * Λ)
          = -(c₃ * (C₃ + 1 / c₃)) * (δg ^ M₃ * δg ^ (-M₃)) * Λ := by ring
        _ = -((c₃ * C₃ + 1) * Λ) := by rw [hc, hprod]; ring
    have hexp2 : Real.exp (-c₃ * δg ^ M₃ * p8bNg C₃ c₃ M₃ Rs ε q δg) ≤ Real.exp (-Λ) := by
      rw [hexp1]
      apply Real.exp_le_exp.2
      have : 0 ≤ c₃ * C₃ * Λ := by positivity
      nlinarith
    -- `C₃ Rs^{M₃} δ^{-M₃} e^{-Λ} ≤ q`
    have hCR : 0 < C₃ * Rs ^ M₃ := mul_pos hC₃ (Real.rpow_pos_of_pos (by linarith) _)
    have hkey : Real.log (C₃ * Rs ^ M₃) + M₃ * Real.log δg⁻¹ + Real.log q⁻¹ ≤ Λ := by
      rw [hΛ, p8bLam]
      have := le_abs_self (Real.log (C₃ * Rs ^ M₃))
      nlinarith
    have hq' : q = Real.exp (-Real.log q⁻¹) := by
      rw [Real.log_inv, neg_neg, Real.exp_log hq]
    calc C₃ * Rs ^ M₃ * δg ^ (-M₃) * Real.exp (-c₃ * δg ^ M₃ * p8bNg C₃ c₃ M₃ Rs ε q δg)
        ≤ C₃ * Rs ^ M₃ * δg ^ (-M₃) * Real.exp (-Λ) := by gcongr
      _ = Real.exp (Real.log (C₃ * Rs ^ M₃) + M₃ * Real.log δg⁻¹ - Λ) := by
          rw [p8b_rpow_neg_eq_exp hδ, Real.exp_sub, Real.exp_add, Real.exp_log hCR, Real.exp_neg]
          field_simp
      _ ≤ Real.exp (-Real.log q⁻¹) := Real.exp_le_exp.2 (by linarith)
      _ = q := hq'.symm

/-! ## The drift ceiling -/

/-- `e^{-X} A e^{Z} ≤ c` once `Z ≥ 1` and `X ≥ (|log(A/c)| + 1) Z`. -/
theorem p8b_exp_mul_le {A c Z X : ℝ} (hA : 0 < A) (hc : 0 < c) (hZ : 1 ≤ Z)
    (h : (|Real.log (A / c)| + 1) * Z ≤ X) : Real.exp (-X) * (A * Real.exp Z) ≤ c := by
  have h1 : Real.log (A / c) ≤ |Real.log (A / c)| * Z :=
    calc Real.log (A / c) ≤ |Real.log (A / c)| := le_abs_self _
      _ = |Real.log (A / c)| * 1 := (mul_one _).symm
      _ ≤ |Real.log (A / c)| * Z := mul_le_mul_of_nonneg_left hZ (abs_nonneg _)
  have h3 : Z - X ≤ -Real.log (A / c) := by nlinarith
  calc Real.exp (-X) * (A * Real.exp Z) = A * Real.exp (Z - X) := by
        rw [show Z - X = Z + -X by ring, Real.exp_add]
        ring
    _ ≤ A * Real.exp (-Real.log (A / c)) := by gcongr
    _ = c := by
        rw [Real.exp_neg, Real.exp_log (div_pos hA hc)]
        field_simp

/-- `log 16 < 3`. -/
theorem p8b_log_sixteen_lt : Real.log 16 < 3 := by
  have h : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [h]
  have := Real.log_two_lt_d9
  linarith

/-- `log 2 < 1`. -/
theorem p8b_log_two_lt_one : Real.log 2 < 1 := by
  have := Real.log_two_lt_d9
  linarith

/-- The constant `K_a = 1 + log(1 + R_s) + log q⁻¹` of the ceiling. -/
def p8bKa (Rs q : ℝ) : ℝ := 1 + Real.log (1 + Rs) + Real.log q⁻¹

/-- The constant `K_b = K_a + |log(C₃ R_s^{M₃})| + 4 + M₃` of the ceiling (`Λ ≤ K_b Y`). -/
def p8bKb (C₃ M₃ Rs q : ℝ) : ℝ := p8bKa Rs q + |Real.log (C₃ * Rs ^ M₃)| + 4 + M₃

/-- The exponent constant `K` of the ceiling: `1/t∗, n₀/c₃₂, n_g/(c₃ g/2) ≤ e^{K Y}`. -/
def p8bK (C₃₂ c₃₂ C₃ c₃ M₃ Rs q : ℝ) : ℝ :=
  (|Real.log (C₃₂ * (p8bKa Rs q + 3) / c₃₂)| + 1) +
    (|Real.log ((C₃ + 1 / c₃) * p8bKb C₃ M₃ Rs q / c₃)| + 1) * (M₃ + 2)

/-- **The ceiling in terms of `Y`** (blueprint `a:prop36`, "The ceiling"): with `Y = 𝒫 + log u⁻¹ + 1` and
`X ≥ K Y`, the three drift constraints of Proposition 3.6 hold for `τ ≤ e^{-X}`. -/
theorem p8b_ceiling_core {Rs q C₃₂ c₃₂ C₃ c₃ M₃ : ℝ} (hRs : 1 ≤ Rs) (hq : 0 < q) (hq1 : q ≤ 1)
    (hC₃₂ : 0 < C₃₂) (hc₃₂ : 0 < c₃₂) (hC₃ : 0 < C₃) (hc₃ : 0 < c₃) (hM₃ : 0 < M₃)
    {P u gn εs ts X : ℝ} (hP : 0 < P) (hu : 0 < u) (hu1 : u < 1) (hgn : Real.exp (-P) ≤ gn)
    (hεs : 0 < εs) (hlogε : Real.log εs⁻¹ ≤ P) (hts : Real.exp (-P) ≤ ts)
    (hX : p8bK C₃₂ c₃₂ C₃ c₃ M₃ Rs q * (P + Real.log u⁻¹ + 1) ≤ X) :
    Real.exp (-X) ≤ ts ∧ Real.exp (-X) * p8bN0 C₃₂ Rs (min εs (u / 16)) q ≤ c₃₂ ∧
      Real.exp (-X) * p8bNg C₃ c₃ M₃ Rs (min εs (u / 16)) q (gn / 2) ≤ c₃ * (gn / 2) := by
  have hlogu : 0 < Real.log u⁻¹ := Real.log_pos (one_lt_inv_iff₀.2 ⟨hu, hu1⟩)
  set Y : ℝ := P + Real.log u⁻¹ + 1 with hY
  have hY1 : 1 ≤ Y := by linarith
  clear_value Y
  have hlogR : 0 ≤ Real.log (1 + Rs) := Real.log_nonneg (by linarith)
  have hlogq : 0 ≤ Real.log q⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hq, hq1⟩)
  set Ka : ℝ := p8bKa Rs q with hKa
  have hKa1 : 1 ≤ Ka := by rw [hKa, p8bKa]; linarith
  set Kb : ℝ := p8bKb C₃ M₃ Rs q with hKb
  have hKb0 : 0 < Kb := by
    rw [hKb, p8bKb, ← hKa]
    have := abs_nonneg (Real.log (C₃ * Rs ^ M₃))
    linarith
  set K : ℝ := p8bK C₃₂ c₃₂ C₃ c₃ M₃ Rs q with hK
  have hK1 : |Real.log (C₃₂ * (Ka + 3) / c₃₂)| + 1 ≤ K := by
    rw [hK, p8bK, ← hKa, ← hKb]
    have : 0 ≤ (|Real.log ((C₃ + 1 / c₃) * Kb / c₃)| + 1) * (M₃ + 2) := by positivity
    linarith
  have hK2 : (|Real.log ((C₃ + 1 / c₃) * Kb / c₃)| + 1) * (M₃ + 2) ≤ K := by
    rw [hK, p8bK, ← hKa, ← hKb]
    have : 0 ≤ |Real.log (C₃₂ * (Ka + 3) / c₃₂)| + 1 := by positivity
    linarith
  have hKpos : 1 ≤ K := le_trans (by have := abs_nonneg (Real.log (C₃₂ * (Ka + 3) / c₃₂)); linarith) hK1
  have hKY : Y ≤ X := le_trans (by nlinarith) hX
  -- the logarithms in terms of `Y`
  set ε' : ℝ := min εs (u / 16) with hε'
  have hε'0 : 0 < ε' := lt_min hεs (by positivity)
  have hlogε' : Real.log ε'⁻¹ ≤ 3 * Y := by
    rcases min_choice εs (u / 16) with h | h
    · rw [hε', h]
      linarith
    · rw [hε', h, inv_div, div_eq_mul_inv, Real.log_mul (by norm_num) (inv_pos.2 hu).ne']
      have := p8b_log_sixteen_lt
      linarith
  set δg : ℝ := gn / 2 with hδg
  have hgn0 : 0 < gn := lt_of_lt_of_le (Real.exp_pos _) hgn
  have hδg0 : 0 < δg := by positivity
  have hδgY : Real.exp (-Y) ≤ δg := by
    have h1 : Real.exp (-Y) ≤ Real.exp (-P) * Real.exp (-1) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.add_one_le_exp 1
      norm_num
      linarith
    calc Real.exp (-Y) ≤ Real.exp (-P) * Real.exp (-1) := h1
      _ ≤ gn * (1 / 2) := mul_le_mul hgn h2 (Real.exp_pos _).le hgn0.le
      _ = δg := by rw [hδg]; ring
  have hδinv : δg⁻¹ ≤ Real.exp Y := by
    rw [inv_le_comm₀ hδg0 (Real.exp_pos _), ← Real.exp_neg]
    exact hδgY
  have hlogδ : Real.log δg⁻¹ ≤ Y := by
    rw [Real.log_le_iff_le_exp (inv_pos.2 hδg0)]
    exact hδinv
  refine ⟨?_, ?_, ?_⟩
  · -- `τ ≤ t∗`
    exact le_trans (Real.exp_le_exp.2 (by linarith)) hts
  · -- `τ n₀ ≤ c₃₂`
    have hn₀ : p8bN0 C₃₂ Rs ε' q ≤ C₃₂ * (Ka + 3) * Real.exp Y := by
      rw [p8bN0]
      have h1 : 1 + Real.log (1 + Rs) + Real.log ε'⁻¹ + Real.log q⁻¹ ≤ (Ka + 3) * Y := by
        rw [hKa, p8bKa]
        nlinarith
      have h2 : Y ≤ Real.exp Y := by have := Real.add_one_le_exp Y; linarith
      calc C₃₂ * (1 + Real.log (1 + Rs) + Real.log ε'⁻¹ + Real.log q⁻¹) ≤ C₃₂ * ((Ka + 3) * Y) := by gcongr
        _ ≤ C₃₂ * ((Ka + 3) * Real.exp Y) := by gcongr
        _ = C₃₂ * (Ka + 3) * Real.exp Y := by ring
    have hmain := p8b_exp_mul_le (A := C₃₂ * (Ka + 3)) (c := c₃₂) (Z := Y) (X := X) (by positivity) hc₃₂ hY1
      (le_trans (mul_le_mul_of_nonneg_right hK1 (by linarith)) hX)
    calc Real.exp (-X) * p8bN0 C₃₂ Rs ε' q ≤ Real.exp (-X) * (C₃₂ * (Ka + 3) * Real.exp Y) :=
          mul_le_mul_of_nonneg_left hn₀ (Real.exp_pos _).le
      _ ≤ c₃₂ := hmain
  · -- `τ n_g ≤ c₃ g/2`
    have hΛ : p8bLam C₃ M₃ Rs ε' q δg ≤ Kb * Y := by
      rw [p8bLam, hKb, p8bKb, ← hKa, hKa, p8bKa]
      have h1 : (1 + M₃) * Real.log δg⁻¹ ≤ (1 + M₃) * Y := mul_le_mul_of_nonneg_left hlogδ (by linarith)
      have h2 := abs_nonneg (Real.log (C₃ * Rs ^ M₃))
      nlinarith
    have hXg : δg ^ (-M₃) ≤ Real.exp (M₃ * Y) := by
      rw [p8b_rpow_neg_eq_exp hδg0]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlogδ hM₃.le)
    have hng : p8bNg C₃ c₃ M₃ Rs ε' q δg ≤ (C₃ + 1 / c₃) * Kb * Real.exp ((M₃ + 1) * Y) := by
      rw [p8bNg]
      have h2 : Y ≤ Real.exp Y := by have := Real.add_one_le_exp Y; linarith
      have hX0 : 0 < δg ^ (-M₃) := Real.rpow_pos_of_pos hδg0 _
      have hc : 0 < C₃ + 1 / c₃ := by positivity
      calc (C₃ + 1 / c₃) * δg ^ (-M₃) * p8bLam C₃ M₃ Rs ε' q δg
          ≤ (C₃ + 1 / c₃) * δg ^ (-M₃) * (Kb * Real.exp Y) := by
            gcongr
            exact le_trans hΛ (mul_le_mul_of_nonneg_left h2 hKb0.le)
        _ ≤ (C₃ + 1 / c₃) * Real.exp (M₃ * Y) * (Kb * Real.exp Y) := by gcongr
        _ = (C₃ + 1 / c₃) * Kb * Real.exp ((M₃ + 1) * Y) := by
            rw [show (M₃ + 1) * Y = M₃ * Y + Y by ring, Real.exp_add (M₃ * Y) Y]
            ring
    have hZ : 1 ≤ (M₃ + 2) * Y := by nlinarith
    have hmain := p8b_exp_mul_le (A := (C₃ + 1 / c₃) * Kb) (c := c₃) (Z := (M₃ + 2) * Y) (X := X)
      (by positivity) hc₃ hZ (by
        calc (|Real.log ((C₃ + 1 / c₃) * Kb / c₃)| + 1) * ((M₃ + 2) * Y)
            = ((|Real.log ((C₃ + 1 / c₃) * Kb / c₃)| + 1) * (M₃ + 2)) * Y := by ring
          _ ≤ K * Y := mul_le_mul_of_nonneg_right hK2 (by linarith)
          _ ≤ X := hX)
    have hsplit : Real.exp ((M₃ + 1) * Y) = Real.exp ((M₃ + 2) * Y) * Real.exp (-Y) := by
      rw [← Real.exp_add ((M₃ + 2) * Y) (-Y)]
      congr 1
      ring
    calc Real.exp (-X) * p8bNg C₃ c₃ M₃ Rs ε' q δg
        ≤ Real.exp (-X) * ((C₃ + 1 / c₃) * Kb * Real.exp ((M₃ + 1) * Y)) :=
          mul_le_mul_of_nonneg_left hng (Real.exp_pos _).le
      _ = Real.exp (-X) * ((C₃ + 1 / c₃) * Kb * Real.exp ((M₃ + 2) * Y)) * Real.exp (-Y) := by
          rw [hsplit]
          ring
      _ ≤ c₃ * Real.exp (-Y) := mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
      _ ≤ c₃ * δg := mul_le_mul_of_nonneg_left hδgY hc₃.le

/-- `(min p q)⁻¹ ≤ p⁻¹ + q⁻¹` for `p, q > 0`. -/
theorem p8b_inv_min_le {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : (min p q)⁻¹ ≤ p⁻¹ + q⁻¹ := by
  rcases min_choice p q with h | h
  · rw [h]
    have := inv_pos.2 hq
    linarith
  · rw [h]
    have := inv_pos.2 hp
    linarith

/-- The constant `K_w = Ξ + 1 + 2Ξ/v₀ + 160 M_s Ξ` of the ceiling, with `Ξ = max(ξ̄, 1)`. -/
def p8bKw (ξbar v₀ Ms : ℝ) : ℝ := max ξbar 1 + 1 + 2 * max ξbar 1 / v₀ + 160 * Ms * max ξbar 1

/-- **The size variable is polynomial in `a⁻¹ u⁻¹`** (blueprint `a:prop36`, "The ceiling"):
`𝒫(a⁻¹, v⁻¹) + log u⁻¹ + 1 ≤ (|A| K_w^B + 2Ξ^B) a^{-B} u^{-B}` with `v = min(v₀/2, u/(160 M_s))` and
`B = max(k, 1)`. -/
theorem p8b_ceiling_Y {ξbar v₀ Ms Ap kp a u : ℝ} (hv₀ : 0 < v₀) (hMs : 1 ≤ Ms) (ha : 0 < a) (haξ : a ≤ ξbar)
    (hu : 0 < u) (hu1 : u < 1) :
    polyB Ap kp a⁻¹ (min (v₀ / 2) (u / (160 * Ms)))⁻¹ + Real.log u⁻¹ + 1 ≤
      (|Ap| * p8bKw ξbar v₀ Ms ^ max kp 1 + 2 * max ξbar 1 ^ max kp 1) * a ^ (-max kp 1) *
        u ^ (-max kp 1) := by
  set Ξ : ℝ := max ξbar 1 with hΞ
  set B : ℝ := max kp 1 with hB
  set Kw : ℝ := p8bKw ξbar v₀ Ms with hKw
  have hΞ1 : 1 ≤ Ξ := le_max_right _ _
  have hB1 : 1 ≤ B := le_max_right _ _
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have hui : 1 < u⁻¹ := one_lt_inv_iff₀.2 ⟨hu, hu1⟩
  set w : ℝ := a⁻¹ * u⁻¹ with hw
  have hw0 : 0 < w := by positivity
  have hΞa : 1 ≤ Ξ * a⁻¹ := by
    rw [← div_eq_mul_inv, one_le_div ha]
    exact le_trans haξ (le_max_left _ _)
  have hΞw : 1 ≤ Ξ * w := by
    rw [hw, ← mul_assoc]
    nlinarith
  have hpow : a ^ (-B) * u ^ (-B) = w ^ B := by
    rw [hw, Real.mul_rpow hai.le (by positivity), Real.rpow_neg ha.le, Real.rpow_neg hu.le,
      Real.inv_rpow ha.le, Real.inv_rpow hu.le]
  -- `x = 1 + a⁻¹ + v⁻¹ ≤ K_w w`
  set v : ℝ := min (v₀ / 2) (u / (160 * Ms)) with hv
  have hvinv : v⁻¹ ≤ 2 / v₀ + 160 * Ms * u⁻¹ := by
    have := p8b_inv_min_le (p := v₀ / 2) (q := u / (160 * Ms)) (by positivity) (by positivity)
    rw [← hv, inv_div, inv_div] at this
    rw [show 160 * Ms * u⁻¹ = 160 * Ms / u by rw [div_eq_mul_inv]]
    exact this
  set x : ℝ := 1 + a⁻¹ + v⁻¹ with hx
  have hv0 : 0 < v := lt_min (by positivity) (by positivity)
  have hx1 : 1 ≤ x := by have := inv_pos.2 hv0; rw [hx]; linarith
  have hxw : x ≤ Kw * w := by
    have h1 : a⁻¹ ≤ w := by rw [hw]; nlinarith
    have h2 : u⁻¹ ≤ Ξ * w := by rw [hw, ← mul_assoc]; nlinarith
    have h3 : 2 / v₀ ≤ 2 / v₀ * (Ξ * w) := by
      have : 0 ≤ 2 / v₀ := by positivity
      nlinarith
    have h4 : 160 * Ms * u⁻¹ ≤ 160 * Ms * (Ξ * w) := by
      have : 0 ≤ 160 * Ms := by positivity
      exact mul_le_mul_of_nonneg_left h2 this
    have hKw' : Kw * w = Ξ * w + w + 2 / v₀ * (Ξ * w) + 160 * Ms * (Ξ * w) := by
      rw [hKw, p8bKw, ← hΞ]
      ring
    rw [hKw', hx]
    linarith
  -- the polynomial
  have hP : polyB Ap kp a⁻¹ v⁻¹ ≤ |Ap| * Kw ^ B * w ^ B := by
    rw [polyB, ← hx]
    have h1 : Ap * x ^ kp ≤ |Ap| * x ^ kp :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
    have h2 : x ^ kp ≤ x ^ B := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
    have h3 : x ^ B ≤ (Kw * w) ^ B := Real.rpow_le_rpow (by linarith) hxw (by linarith)
    have hKw0 : 0 ≤ Kw := by
      rw [hKw, p8bKw]
      positivity
    rw [Real.mul_rpow hKw0 hw0.le] at h3
    calc Ap * x ^ kp ≤ |Ap| * x ^ kp := h1
      _ ≤ |Ap| * x ^ B := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ ≤ |Ap| * (Kw ^ B * w ^ B) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = |Ap| * Kw ^ B * w ^ B := by ring
  -- the logarithm
  have hlog : Real.log u⁻¹ + 1 ≤ 2 * Ξ ^ B * w ^ B := by
    have h1 : Real.log u⁻¹ + 1 ≤ u⁻¹ := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hu)
      linarith
    have h2 : u⁻¹ ≤ Ξ * w := by rw [hw, ← mul_assoc]; nlinarith
    have h3 : Ξ * w ≤ (Ξ * w) ^ B := by
      calc Ξ * w = (Ξ * w) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Ξ * w) ^ B := Real.rpow_le_rpow_of_exponent_le hΞw hB1
    rw [Real.mul_rpow (by linarith) hw0.le] at h3
    have h4 : 0 ≤ Ξ ^ B * w ^ B := by positivity
    nlinarith
  rw [mul_assoc _ (a ^ (-B)), hpow]
  nlinarith

/-- **The drift ceiling of Proposition 3.6** (blueprint `a:prop36`, "The ceiling"; NA1 R11): there are `B, C₆ > 0`,
depending only on the fixed data, such that `τ ≤ exp(-C₆ a^{-B} u^{-B})` implies the three drift constraints
`τ ≤ t∗`, `τ n₀ ≤ c₃₂` and `τ n_g ≤ c₃ g/2`, for all `a ∈ (0, ξ̄]`, `u ∈ (0, 1)` and all outputs `g, ε∗, t∗` of
Proposition 3.5 at `v = min(v₀/2, u/(160 M_s))`. -/
theorem p8b_ceiling {ξbar Rs q C₃₂ c₃₂ C₃ c₃ M₃ Ap kp v₀ Ms : ℝ} (hRs : 1 ≤ Rs) (hq : 0 < q) (hq1 : q ≤ 1)
    (hC₃₂ : 0 < C₃₂) (hc₃₂ : 0 < c₃₂) (hC₃ : 0 < C₃) (hc₃ : 0 < c₃) (hM₃ : 0 < M₃) (hv₀ : 0 < v₀)
    (hv₀' : v₀ ≤ 1 / 2) (hMs : 1 ≤ Ms) :
    ∃ B C₆ : ℝ, 0 < B ∧ 0 < C₆ ∧ ∀ a u gn εs ts : ℝ, 0 < a → a ≤ ξbar → 0 < u → u < 1 →
      Real.exp (-polyB Ap kp a⁻¹ (min (v₀ / 2) (u / (160 * Ms)))⁻¹) ≤ gn →
      gn ≤ min (v₀ / 2) (u / (160 * Ms)) → 0 < εs →
      Real.log εs⁻¹ ≤ polyB Ap kp a⁻¹ (min (v₀ / 2) (u / (160 * Ms)))⁻¹ →
      Real.exp (-polyB Ap kp a⁻¹ (min (v₀ / 2) (u / (160 * Ms)))⁻¹) ≤ ts →
      Real.exp (-(C₆ * a ^ (-B) * u ^ (-B))) ≤ ts ∧
        Real.exp (-(C₆ * a ^ (-B) * u ^ (-B))) * p8bN0 C₃₂ Rs (min εs (u / 16)) q ≤ c₃₂ ∧
        Real.exp (-(C₆ * a ^ (-B) * u ^ (-B))) * p8bNg C₃ c₃ M₃ Rs (min εs (u / 16)) q (gn / 2) ≤
          c₃ * (gn / 2) := by
  set K : ℝ := p8bK C₃₂ c₃₂ C₃ c₃ M₃ Rs q with hK
  have hK0 : 0 < K := by
    rw [hK, p8bK]
    positivity
  set Kz : ℝ := |Ap| * p8bKw ξbar v₀ Ms ^ max kp 1 + 2 * max ξbar 1 ^ max kp 1 with hKz
  have hKz0 : 0 < Kz := by
    have h1 : 0 < max ξbar 1 ^ max kp 1 := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _)) _
    have h2 : 0 ≤ |Ap| * p8bKw ξbar v₀ Ms ^ max kp 1 := by
      have : 0 ≤ p8bKw ξbar v₀ Ms := by
        rw [p8bKw]
        have : 0 ≤ max ξbar 1 := le_trans zero_le_one (le_max_right _ _)
        positivity
      positivity
    rw [hKz]
    linarith
  refine ⟨max kp 1, K * Kz, lt_of_lt_of_le one_pos (le_max_right _ _), mul_pos hK0 hKz0, ?_⟩
  intro a u gn εs ts ha haξ hu hu1 hgn hgnv hεs hlogε hts
  set P : ℝ := polyB Ap kp a⁻¹ (min (v₀ / 2) (u / (160 * Ms)))⁻¹ with hP
  have hv1 : min (v₀ / 2) (u / (160 * Ms)) < 1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hP0 : 0 < P := by
    have h1 : Real.exp (-P) < 1 := lt_of_le_of_lt (hgn.trans hgnv) hv1
    have h2 : -P < 0 := Real.exp_lt_one_iff.1 h1
    linarith
  have hY := p8b_ceiling_Y (ξbar := ξbar) (Ap := Ap) (kp := kp) hv₀ hMs ha haξ hu hu1
  rw [← hP, ← hKz] at hY
  refine p8b_ceiling_core hRs hq hq1 hC₃₂ hc₃₂ hC₃ hc₃ hM₃ hP0 hu hu1 hgn hεs hlogε hts ?_
  rw [← hK]
  have := mul_le_mul_of_nonneg_left hY hK0.le
  calc K * (P + Real.log u⁻¹ + 1) ≤ K * (Kz * a ^ (-max kp 1) * u ^ (-max kp 1)) := this
    _ = K * Kz * a ^ (-max kp 1) * u ^ (-max kp 1) := by ring

end HigherDimLQGContinuity
