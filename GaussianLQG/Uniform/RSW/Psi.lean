import GaussianLQG.Uniform.RSW.Phi
import LQGMetric.Papers.DDDF.C8High

/-!
# RSW estimates for `ψ` with constants uniform in `ξ` (Route U, item U4, part 2)

Phase B, packet PB-RSW. Uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`, U4;
feasibility study `planning/audits/B1-S6-feasibility.md`, §3b row 17. Templates (not edited):
`psi_rsw_low_quantile` (`LQGMetric/Papers/DDDF/C8.lean`), `psi_rsw_high_quantile`
(`C8High.lean`) and their unconditional wrappers in `RSWUncond.lean`: DDDF Corollary 8,
(3.38)–(3.39).

The template constants are `C = 4C₀ + 1 + |ξ|√(k₁/c) + |ξ|√(k₂/c) + C₀√k₃` (low) and
`C = 2C₀ + 2 + 2|ξ|√(k/c) + C₀√k₃` (high), linear in `|ξ|`, with `C₀` the constant of (3.36)
resp. (3.37) for `φ` and `(C', c)` the Prop 5 constants. Here `C₀` comes from
`rsw_low_quantile_unif` / `rsw_high_quantile_unif`, `(C', c)` from `exists_tail_XAB_unif_W`
(constants before `Ω`), and `|ξ|` is replaced by `ξs` (ledger: "`|ξ| ≤ ξs` in the C8 constants").
Both results are unconditional (no `Prop10` hypothesis). The ledger's per-noise U-forms
`psi_rsw_low_quantile_unif`, `psi_rsw_high_quantile_unif` (white noise first, constants before
`ξ`) are corollaries of the strong forms `_all` (constants before the probability space).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

universe u

/-- **DDDF Corollary 8, (3.38), uniform in `ξ` and in the white noise** (strong form of ledger
U4 `psi_rsw_low_quantile_unif`; template `psi_rsw_low_quantile`): small quantiles of `ψ`,
uniformly over shapes in `[A, B]²`, with one `C ≥ 1` for all white noises and all
`ξ ∈ (0, ξs]`. -/
theorem psi_rsw_low_quantile_unif_all {ξs : ℝ} (hξs : 0 < ξs) (Q : PsiParams) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ellQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
        C * ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  obtain ⟨C₀, hC₀1, hR⟩ := rsw_low_quantile_unif_all.{u} hξs hA hAB
  have hC₀ : 0 < C₀ := by linarith
  obtain ⟨C', c, hC', hc, htail⟩ := exists_tail_XAB_unif_W.{u} Q B
  set d₁ : ℝ := 4 * C₀ with hd₁
  have hd₁1 : 1 ≤ d₁ := by linarith
  set k₁ : ℝ := 2 + 2 * |Real.log C'| + 2 * Real.log d₁
  set k₂ : ℝ := 2 + 2 * |Real.log C'| + 2 * Real.log 2
  set k₃ : ℝ := 1 + 2 * |Real.log (2 * C₀)|
  set s : ℝ := ξs * √(k₁ / c) + ξs * √(k₂ / c) + C₀ * √k₃ with hs
  have hs0 : 0 ≤ s := by positivity
  set C : ℝ := d₁ + 1 + s with hCdef
  have hC1 : 1 ≤ C := by linarith
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ a b a' b' ha hb ha' hb' n ε hε hε2 => ?_⟩
  have := hW.isProbabilityMeasure
  have hξabs : |ξ| ≤ ξs := by rw [abs_of_pos hξ.1]; exact hξ.2
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have ha0 : 0 ≤ a := hA.le.trans ha.1
  have hb0 : 0 ≤ b := hA.le.trans hb.1
  have ha'0 : 0 ≤ a' := hA.le.trans ha'.1
  have hb'0 : 0 ≤ b' := hA.le.trans hb'.1
  set L := |Real.log (ε / C)|
  set M₁ : ℝ := √(max 1 (Real.log (C' / (ε / d₁))) / c)
  set M₂ : ℝ := √(max 1 (Real.log (C' / (ε / 2))) / c)
  -- step 1: `ℓ_{a,b}(φ, ε/2) ≤ e^{|ξ|M₂} ℓ_{a,b}(ψ, ε)`
  have h1 := ellQ_phi_le_of_tail (ξ := ξ) hW Q ha0 hb0 (M := M₂) (Real.sqrt_nonneg _)
    (htail hW a b ha.2 hb.2 (ε / 2) (by positivity)) (p := ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
    (by rw [← ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_lt_one]
        linarith) n
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves] at h1
  -- step 2: (3.36) for `φ` at level `ε/2`
  have h2 := hR hW ξ hξ a b a' b' ha hb ha' hb' n (ε / 2) (by positivity) (by linarith)
  -- step 3: `ℓ_{a',b'}(ψ, ε/d₁) ≤ e^{|ξ|M₁} ℓ_{a',b'}(φ, ε/(2C₀))`
  have e3 : ENNReal.ofReal (ε / d₁) + ENNReal.ofReal (ε / d₁) = ENNReal.ofReal (ε / 2 / C₀) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; rw [hd₁]; field_simp; ring
  have hlt3 : ε / 2 / C₀ < 1 := by rw [div_lt_one hC₀]; linarith
  have h3 := ellQ_psi_le_of_tail (ξ := ξ) hW Q ha'0 hb'0 (M := M₁) (Real.sqrt_nonneg _)
    (htail hW a' b' ha'.2 hb'.2 (ε / d₁) (by positivity)) (p := ENNReal.ofReal (ε / d₁))
    (ENNReal.ofReal_pos.2 (by positivity))
    (by rw [e3, ENNReal.ofReal_lt_one]; exact hlt3) n
  rw [e3] at h3
  -- step 4: monotonicity of the quantile
  have h4 : ellQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
      ellQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / d₁)) :=
    ellQ_mono _ (ENNReal.ofReal_pos.2 (by positivity))
      (by rw [ENNReal.ofReal_lt_one, div_lt_one (by linarith)]; linarith)
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hε.le (by linarith) (by linarith)))
  have hℓ := ellQ_nonneg (ξ := ξ) (P := P) hψ.cont hψ.meas (rectAB a b) (p := ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.2 hε) (by rw [ENNReal.ofReal_lt_one]; linarith)
  set ℓ := ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε)
  -- the exponents, with `|ξ| ≤ ξs`
  have x1 : |ξ| * M₁ ≤ |ξ| * √(k₁ / c) * √L := tailExp_le hC' hc hd₁1 hε hε2 hC1
  have x2 : |ξ| * M₂ ≤ |ξ| * √(k₂ / c) * √L := tailExp_le hC' hc (by norm_num) hε hε2 hC1
  have x1' : |ξ| * √(k₁ / c) * √L ≤ ξs * √(k₁ / c) * √L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hξabs (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have x2' : |ξ| * √(k₂ / c) * √L ≤ ξs * √(k₂ / c) * √L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hξabs (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have x3 : C₀ * √|Real.log (ε / 2 / C₀)| ≤ C₀ * √k₃ * √L := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₀.le
    rw [← Real.sqrt_mul (by positivity), div_div]
    exact Real.sqrt_le_sqrt (abs_log_div_le hε hε2 (by positivity) hC1)
  have hsum : |ξ| * M₁ + |ξ| * M₂ + C₀ * √|Real.log (ε / 2 / C₀)| ≤ C * √L := by
    have : s * √L ≤ C * √L := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    have : s * √L = ξs * √(k₁ / c) * √L + ξs * √(k₂ / c) * √L + C₀ * √k₃ * √L := by ring
    linarith
  set E₁ := Real.exp (|ξ| * M₁)
  set E₂ := Real.exp (|ξ| * M₂)
  set E₃ := Real.exp (C₀ * √|Real.log (ε / 2 / C₀)|)
  have hE : E₁ * E₂ * E₃ ≤ Real.exp (C * √L) := by
    simp only [E₁, E₂, E₃, ← Real.exp_add]; exact Real.exp_le_exp.2 hsum
  calc _ ≤ _ := h4
    _ ≤ E₁ * ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / 2 / C₀)) := h3
    _ ≤ E₁ * (C₀ * ellQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal (ε / 2)) * E₃) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ E₁ * (C₀ * (E₂ * ℓ) * E₃) := by
        gcongr
    _ = C₀ * ℓ * (E₁ * E₂ * E₃) := by ring
    _ ≤ C * ℓ * Real.exp (C * √L) := by
        gcongr
        linarith

/-- **DDDF Corollary 8, (3.39), uniform in `ξ` and in the white noise** (strong form of ledger
U4 `psi_rsw_high_quantile_unif`; template `psi_rsw_high_quantile`, reading D-DDDF-8): high
quantiles of `ψ`, uniformly over shapes in `[A, B]²`, with one `C ≥ 1` for all white noises and
all `ξ ∈ (0, ξs]`, for `3 ε^{1/C} < 1`. -/
theorem psi_rsw_high_quantile_unif_all {ξs : ℝ} (hξs : 0 < ξs) (Q : PsiParams) {A B : ℝ}
    (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 → 3 * ε ^ (1 / C) < 1 →
      ellBarQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (3 * ε ^ (1 / C))) ≤
        C * ellBarQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  obtain ⟨C₀, hC₀1, hR⟩ := rsw_high_quantile_unif_all.{u} hξs hA hAB
  have hC₀ : 0 < C₀ := by linarith
  obtain ⟨C', c, hC', hc, htail⟩ := exists_tail_XAB_unif_W.{u} Q B
  set k : ℝ := 2 + 2 * |Real.log C'| + 2 * Real.log 1
  set k₃ : ℝ := 1 + 2 * |Real.log C₀|
  set s : ℝ := ξs * √(k / c) + ξs * √(k / c) + C₀ * √k₃ with hs
  have hs0 : 0 ≤ s := by positivity
  set C : ℝ := 2 * C₀ + 2 + s with hCdef
  have hC1 : 1 ≤ C := by linarith
  have hC0 : 0 < C := by linarith
  refine ⟨C, hC1, fun {Ω} _ {P} {W} hW ξ hξ a b a' b' ha hb ha' hb' n ε hε hε2 h3u => ?_⟩
  have := hW.isProbabilityMeasure
  have hξabs : |ξ| ≤ ξs := by rw [abs_of_pos hξ.1]; exact hξ.2
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have ha0 : 0 ≤ a := hA.le.trans ha.1
  have hb0 : 0 ≤ b := hA.le.trans hb.1
  have ha'0 : 0 ≤ a' := hA.le.trans ha'.1
  have hb'0 : 0 ≤ b' := hA.le.trans hb'.1
  have hε1 : ε < 1 := by linarith
  set u := ε ^ (1 / C) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hε _
  have hu3 : u < 1 / 3 := by linarith
  have hεu : ε ≤ u := by
    calc ε = ε ^ (1 : ℝ) := (Real.rpow_one ε).symm
      _ ≤ u := Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by rw [div_le_one hC0]; exact hC1)
  -- `ε < 1/9`
  have hε9 : ε < 1 / 9 := by
    have h1 : ε ^ (1 / 2 : ℝ) ≤ u := Real.rpow_le_rpow_of_exponent_ge hε hε1.le
      (one_div_le_one_div_of_le (by norm_num) (by linarith))
    rw [← Real.sqrt_eq_rpow] at h1
    have h2 := Real.sq_sqrt hε.le
    nlinarith [Real.sqrt_nonneg ε]
  set w := (2 * ε) ^ (1 / C₀) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos (by positivity) _
  have hlev : 3 * w ≤ 2 * u := level_le hε hε1 hC₀1 (by linarith) hu3
  set L := |Real.log (ε / C)|
  set M₁ : ℝ := √(max 1 (Real.log (C' / u)) / c)
  set M₂ : ℝ := √(max 1 (Real.log (C' / ε)) / c)
  -- step 1: from `ψ` to `φ` on `R_{a',b'}`
  have h1 := ellQ_psi_le_of_tail (ξ := ξ) hW Q ha'0 hb'0 (M := M₁) (Real.sqrt_nonneg _)
    (htail hW a' b' ha'.2 hb'.2 u hu0) (p := ENNReal.ofReal (1 - 3 * u))
    (ENNReal.ofReal_pos.2 (by linarith))
    (by rw [← ENNReal.ofReal_add (by linarith) hu0.le, ENNReal.ofReal_lt_one]; linarith) n
  rw [← ENNReal.ofReal_add (by linarith) hu0.le] at h1
  -- monotonicity of the quantile
  have hm : ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (1 - 3 * u + u)) ≤
      ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (1 - 3 * w)) :=
    ellQ_mono _ (ENNReal.ofReal_pos.2 (by linarith))
      (by rw [ENNReal.ofReal_lt_one]; linarith) (ENNReal.ofReal_le_ofReal (by linarith))
  -- step 2: (3.37) for `φ` at `2ε`
  have h2 := hR hW ξ hξ a b a' b' ha hb ha' hb' n (2 * ε) (by positivity) (by linarith)
    (by linarith)
  unfold ellBarQ at h2
  rw [one_sub_ofReal' (by positivity), one_sub_ofReal' (by positivity)] at h2
  -- step 3: from `φ` back to `ψ` on `R_{a,b}`
  have h3 := ellQ_phi_le_of_tail (ξ := ξ) hW Q ha0 hb0 (M := M₂) (Real.sqrt_nonneg _)
    (htail hW a b ha.2 hb.2 ε hε) (p := ENNReal.ofReal (1 - 2 * ε))
    (ENNReal.ofReal_pos.2 (by linarith))
    (by rw [← ENNReal.ofReal_add (by linarith) hε.le, ENNReal.ofReal_lt_one]; linarith) n
  rw [← ENNReal.ofReal_add (by linarith) hε.le,
    show 1 - 2 * ε + ε = 1 - ε by ring] at h3
  have hℓ := ellQ_nonneg (ξ := ξ) (P := P) hψ.cont hψ.meas (rectAB a b)
    (p := ENNReal.ofReal (1 - ε)) (ENNReal.ofReal_pos.2 (by linarith))
    (by rw [ENNReal.ofReal_lt_one]; linarith)
  unfold ellBarQ
  rw [one_sub_ofReal' (by positivity), one_sub_ofReal' hε.le]
  set ℓ := ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal (1 - ε))
  -- the exponents, with `|ξ| ≤ ξs`
  have hM : M₁ ≤ M₂ := by
    refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (max_le_max le_rfl ?_) hc.le)
    exact Real.log_le_log (div_pos hC' hu0) (div_le_div_of_nonneg_left hC'.le hε hεu)
  have x2 : |ξ| * M₂ ≤ |ξ| * √(k / c) * √L := by
    have := tailExp_le (ξ := ξ) hC' hc (le_refl (1 : ℝ)) hε hε2 hC1
    rwa [div_one] at this
  have x1 : |ξ| * M₁ ≤ |ξ| * √(k / c) * √L :=
    (mul_le_mul_of_nonneg_left hM (abs_nonneg _)).trans x2
  have x12 : |ξ| * √(k / c) * √L ≤ ξs * √(k / c) * √L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hξabs (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have x3 : C₀ * √|Real.log (2 * ε / C₀)| ≤ C₀ * √k₃ * √L := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₀.le
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ((abs_log_div_le (by positivity) (by linarith) hC₀ hC1).trans ?_)
    exact mul_le_mul_of_nonneg_left (abs_log_div_mono hε (by linarith) (by linarith) hC1)
      (by positivity)
  have hsum : |ξ| * M₁ + |ξ| * M₂ + C₀ * √|Real.log (2 * ε / C₀)| ≤ C * √L := by
    have : s * √L ≤ C * √L := mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    have : s * √L = ξs * √(k / c) * √L + ξs * √(k / c) * √L + C₀ * √k₃ * √L := by ring
    linarith
  set E₁ := Real.exp (|ξ| * M₁)
  set E₂ := Real.exp (|ξ| * M₂)
  set E₃ := Real.exp (C₀ * √|Real.log (2 * ε / C₀)|)
  have hE : E₁ * E₂ * E₃ ≤ Real.exp (C * √L) := by
    simp only [E₁, E₂, E₃, ← Real.exp_add]; exact Real.exp_le_exp.2 hsum
  calc _ ≤ _ := h1
    _ ≤ E₁ * ellQ ξ P (phiMN W P 0 n) (rectAB a' b') (ENNReal.ofReal (1 - 3 * w)) :=
        mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
    _ ≤ E₁ * (C₀ * ellQ ξ P (phiMN W P 0 n) (rectAB a b) (ENNReal.ofReal (1 - 2 * ε)) * E₃) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ ≤ E₁ * (C₀ * (E₂ * ℓ) * E₃) := by
        gcongr
    _ = C₀ * ℓ * (E₁ * E₂ * E₃) := by ring
    _ ≤ C * ℓ * Real.exp (C * √L) := by
        gcongr
        linarith

/-! ### The per-noise forms (ledger U-form) -/

section PerNoise

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DDDF Corollary 8, (3.38), uniform in `ξ`** (ledger U4, `psi_rsw_low_quantile_unif`;
template `psi_rsw_low_quantile'`; strong form `psi_rsw_low_quantile_unif_all`) -/
theorem psi_rsw_low_quantile_unif (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs)
    (Q : PsiParams) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ellQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (ε / C)) ≤
        C * ellQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  obtain ⟨C, hC1, hC⟩ := psi_rsw_low_quantile_unif_all.{u} hξs Q hA hAB
  exact ⟨C, hC1, hC hW⟩

/-- **DDDF Corollary 8, (3.39), uniform in `ξ`** (ledger U4, `psi_rsw_high_quantile_unif`;
template `psi_rsw_high_quantile'`; strong form `psi_rsw_high_quantile_unif_all`) -/
theorem psi_rsw_high_quantile_unif (hW : IsWhiteNoise P W) (ξs : ℝ) (hξs : 0 < ξs)
    (Q : PsiParams) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ ξ ∈ Ioc (0 : ℝ) ξs,
      ∀ a b a' b' : ℝ, a ∈ Icc A B → b ∈ Icc A B → a' ∈ Icc A B → b' ∈ Icc A B →
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 / 2 → 3 * ε ^ (1 / C) < 1 →
      ellBarQ ξ P (psiMN Q W P 0 n) (rectAB a' b') (ENNReal.ofReal (3 * ε ^ (1 / C))) ≤
        C * ellBarQ ξ P (psiMN Q W P 0 n) (rectAB a b) (ENNReal.ofReal ε) *
          Real.exp (C * Real.sqrt |Real.log (ε / C)|) := by
  obtain ⟨C, hC1, hC⟩ := psi_rsw_high_quantile_unif_all.{u} hξs Q hA hAB
  exact ⟨C, hC1, hC hW⟩

end PerNoise

end Uniform
end GaussianLQG
