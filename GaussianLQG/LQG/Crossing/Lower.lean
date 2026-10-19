import GaussianLQG.LQG.Crossing.Bounds

/-!
# The lower bound for the crossing distance (blueprint Proposition `prop:crossing`)

Let `𝖸_γ = (log C_γ - b_γ) / ξ_γ` (`Setup.crossY`). This file proves the lower half of blueprint
Proposition `prop:crossing`: for every `ε > 0`, `P[𝖸_γ < M - ε] → 0` as `γ ↓ 0`
(`Setup.tendsto_measure_crossY_lt`), assuming Lemma `lem:energy-approx`.

Proof (blueprint). Let `m = m(γ)`, `A = A_γ(S)`, `I = I_γ(S, 1)` and `K = ξ^{-1/8}`. On the event
where `A ≤ K`, `I⁻¹ ≤ K`, `|𝓡| < ε/4` on `S_m²`, and
`|H(s,t) - H(s,s)| < Q log r(s,t) + ε/2` on `S_m²` (and `M ≤ H(y,y)` for dyadic `y`), every grid
pair has `(log D(is,1+it) - b)/ξ = Q log r + H(s,t) + 𝓡(s,t) > H(s,s) - 3ε/4 ≥ M - 3ε/4`, and the
discretization step `Crossing.log_crossFn_ge_of_grid` gives
`𝖸_γ ≥ M - 3ε/4 - 2K² 2^{-m/2}/ξ ≥ M - ε` (`Setup.M_sub_le_crossY`). The complementary events are
small: Markov's inequality with (S6) for `A` and `I⁻¹`, Lemma `lem:grid-residual` for `𝓡`, and
Gaussian union bounds for the differences `H(s,t) - H(s,s)` (`Setup.measure_exists_H_sub_ge_le`).

Deviation in the proof route (not in any statement): the blueprint splits `S_m²` into "far" pairs
(`|s - t| ≥ η`), handled through `E max |H| ≤ C (log 1/ξ)^{1/2}` and the tightness of `M ≤ H(0,0)`,
and "near" pairs, handled through `H(s,t) ≥ H(s,s) - |H(s,t) - H(s,s)|`. Here both kinds of pairs
are handled by the second argument: for far pairs `Q log r(s,t) ≥ η²/(8ξ)` and the variance of
`H(s,t) - H(s,s)` is at most `6`, so the Gaussian tail of `H(s,t) - H(s,s)` at level `Q log r`
is already `≤ 2 e^{-1/(768 ξ)}`. We take `η = ξ^{1/4}` instead of `(log 1/ξ)^{-4}`; both choices
make the union bounds over the `≤ 16 ξ^{-6}` grid pairs tend to `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

open LQGMetric Crossing

namespace Crossing

/-- Markov's inequality: if `∫⁻ f ≤ C < ∞` and `κ > 0`, then `μ[f > κ] ≤ C/κ`. -/
theorem measure_ofReal_lt_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {C : ℝ≥0∞} (hC : ∫⁻ a, f a ∂μ ≤ C) (hCtop : C ≠ ⊤) {κ : ℝ}
    (hκ : 0 < κ) :
    μ {a | ENNReal.ofReal κ < f a} ≤ ENNReal.ofReal (C.toReal / κ) := by
  calc μ {a | ENNReal.ofReal κ < f a} ≤ μ {a | ENNReal.ofReal κ ≤ f a} :=
        measure_mono fun a (ha : ENNReal.ofReal κ < f a) => (le_of_lt ha : ENNReal.ofReal κ ≤ f a)
    _ ≤ (∫⁻ a, f a ∂μ) / ENNReal.ofReal κ :=
        meas_ge_le_lintegral_div hf (by simpa using hκ) ENNReal.ofReal_ne_top
    _ ≤ C / ENNReal.ofReal κ := by gcongr
    _ = ENNReal.ofReal (C.toReal / κ) := by
        rw [ENNReal.ofReal_div_of_pos hκ, ENNReal.ofReal_toReal hCtop]

/-- `2 K² (2^{-m})^{1/2} ≤ ξ ε'` for `K = ξ^{-1/8}`, `2^{-m} ≤ ξ³` and `2 ξ^{1/4} ≤ ε'`. -/
theorem two_mul_sq_mul_rpow_le {ξ ε' : ℝ} {m : ℕ} (hξ : 0 < ξ) (hm : ξ⁻¹ ^ 3 ≤ (2 : ℝ) ^ m)
    (hsmall : 2 * ξ ^ (1 / 4 : ℝ) ≤ ε') :
    2 * (ξ ^ (-(1 / 8) : ℝ)) ^ 2 * (1 / (2 : ℝ) ^ m) ^ (1 / 2 : ℝ) ≤ ξ * ε' := by
  have hK2 : (ξ ^ (-(1 / 8) : ℝ)) ^ 2 = ξ ^ (-(1 / 4) : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hξ.le]
    norm_num
  have hm' : 1 / (2 : ℝ) ^ m ≤ ξ ^ 3 := by
    have h := one_div_le_one_div_of_le (by positivity) hm
    rwa [inv_pow, one_div (ξ ^ 3)⁻¹, inv_inv] at h
  have hsqrt : (1 / (2 : ℝ) ^ m) ^ (1 / 2 : ℝ) ≤ ξ ^ (3 / 2 : ℝ) := by
    calc (1 / (2 : ℝ) ^ m) ^ (1 / 2 : ℝ) ≤ (ξ ^ 3) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hm' (by norm_num)
      _ = ξ ^ (3 / 2 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hξ.le]
          norm_num
  have hprod : ξ ^ (-(1 / 4) : ℝ) * ξ ^ (3 / 2 : ℝ) = ξ * ξ ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hξ, show (-(1 / 4) : ℝ) + 3 / 2 = 1 + 1 / 4 by norm_num,
      Real.rpow_add hξ, Real.rpow_one]
  rw [hK2]
  calc 2 * ξ ^ (-(1 / 4) : ℝ) * (1 / (2 : ℝ) ^ m) ^ (1 / 2 : ℝ)
      ≤ 2 * ξ ^ (-(1 / 4) : ℝ) * ξ ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = ξ * (2 * ξ ^ (1 / 4 : ℝ)) := by rw [mul_assoc, hprod]; ring
    _ ≤ ξ * ε' := mul_le_mul_of_nonneg_left hsmall hξ.le

end Crossing

namespace Setup

variable (S : Setup)

/-- `𝖸_γ = (log C_γ - b_γ) / ξ_γ`, with `C_γ` the left–right crossing distance of the unit
square (blueprint Proposition `prop:crossing`). -/
def crossY (γ : ℝ) (ω : Coord) : ℝ := (Real.log (GM.crossFn (S.D γ ω).1) - S.b γ) / S.ξ γ

/-! ## Far and near pairs -/

/-- **Gaussian bound for one grid pair** (blueprint proof of Proposition `prop:crossing`, far and
near pairs, with `η = ξ^{1/4}`). If `0 < ξ ≤ 1` and `ξ Q ≥ 1/2`, then for `s, t ∈ [0, 1]`,
`P[|H(s,t) - H(s,s)| ≥ Q log r(s,t) + 2ε'] ≤ 2 e^{-1/(768 ξ)} + 2 e^{-ε'²/(3 ξ^{1/8})}`. -/
theorem measure_H_sub_ge_le {ξ Q ε' : ℝ} (hξ : 0 < ξ) (hξQ : 1 / 2 ≤ ξ * Q) (hε' : 0 < ε')
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    stdP {ω | Q * Real.log ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖ + 2 * ε' ≤
        |S.H s t ω - S.H s s ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-((1 / 768) / ξ)) +
        2 * Real.exp (-((ε' ^ 2 / 3) / ξ ^ (1 / 8 : ℝ)))) := by
  set x := Q * Real.log ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖ + 2 * ε' with hx
  have hQ : 0 < Q := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hξ.le (not_lt.1 h)
    linarith
  have hlog0 := log_norm_sI_sub_nonneg s t
  have hQlog : 0 ≤ Q * Real.log ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖ :=
    mul_nonneg hQ.le hlog0
  have hx0 : 2 * ε' ≤ x := by linarith
  have hxnn : 0 ≤ x := by linarith
  have he1 : 0 ≤ 2 * Real.exp (-((1 / 768) / ξ)) := by positivity
  have he2 : 0 ≤ 2 * Real.exp (-((ε' ^ 2 / 3) / ξ ^ (1 / 8 : ℝ))) := by positivity
  have hst : |t - s| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  rcases lt_or_ge |t - s| (ξ ^ (1 / 4 : ℝ)) with hnear | hfar
  · -- near pairs: variance `≤ 6 ξ^{1/8}` and level `≥ 2ε'`
    have hp : 0 < ξ ^ (1 / 8 : ℝ) := by positivity
    have hV : 6 * |t - s| ^ (1 / 2 : ℝ) ≤ 6 * ξ ^ (1 / 8 : ℝ) := by
      have h := Real.rpow_le_rpow (abs_nonneg _) hnear.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
      rw [← Real.rpow_mul hξ.le, show (1 / 4 : ℝ) * (1 / 2) = 1 / 8 by norm_num] at h
      linarith
    refine (S.measure_H_sub_tail hs ht hV hxnn).trans (ENNReal.ofReal_le_ofReal ?_)
    have hexp : 2 * Real.exp (-x ^ 2 / (2 * (6 * ξ ^ (1 / 8 : ℝ)))) ≤
        2 * Real.exp (-((ε' ^ 2 / 3) / ξ ^ (1 / 8 : ℝ))) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
      have hsq : (2 * ε') ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ (by positivity) hx0 2
      have e : (ε' ^ 2 / 3) / ξ ^ (1 / 8 : ℝ) = (2 * ε') ^ 2 / (2 * (6 * ξ ^ (1 / 8 : ℝ))) := by
        field_simp
        ring
      rw [neg_div, neg_le_neg_iff, e]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    linarith
  · -- far pairs: variance `≤ 6` and level `≥ Q ξ^{1/2}/4 ≥ 1/(8 ξ^{1/2})`
    have hV : 6 * |t - s| ^ (1 / 2 : ℝ) ≤ 6 := by
      have h : |t - s| ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (abs_nonneg _) hst (by norm_num)
      linarith
    refine (S.measure_H_sub_tail hs ht hV hxnn).trans (ENNReal.ofReal_le_ofReal ?_)
    have hlog := sq_sub_div_four_le_log_norm hs ht
    have hη2 : ξ ^ (1 / 2 : ℝ) ≤ (s - t) ^ 2 := by
      have h : (ξ ^ (1 / 4 : ℝ)) ^ 2 ≤ |t - s| ^ 2 := pow_le_pow_left₀ (by positivity) hfar 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul hξ.le, sq_abs,
        show (1 / 4 : ℝ) * ((2 : ℕ) : ℝ) = 1 / 2 by norm_num] at h
      nlinarith [h]
    have hx1 : Q * ξ ^ (1 / 2 : ℝ) / 4 ≤ x := by
      have h1 : Q * ξ ^ (1 / 2 : ℝ) / 4 ≤ Q * ((s - t) ^ 2 / 4) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (by linarith) hQ.le
      have h2 : Q * ((s - t) ^ 2 / 4) ≤
          Q * Real.log ‖(s : ℂ) * Complex.I - (1 + (t : ℂ) * Complex.I)‖ :=
        mul_le_mul_of_nonneg_left hlog hQ.le
      linarith
    have hsq : (ξ ^ (1 / 2 : ℝ)) ^ 2 = ξ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hξ.le]
      norm_num
    have hy : 0 ≤ Q * ξ ^ (1 / 2 : ℝ) / 4 := by positivity
    have h1 : (Q * ξ ^ (1 / 2 : ℝ) / 4) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hy hx1 2
    have h2 : (Q * ξ ^ (1 / 2 : ℝ) / 4) ^ 2 = (ξ * Q) ^ 2 / (16 * ξ) := by
      rw [div_pow, mul_pow, hsq]
      field_simp
      ring
    have h3 : 1 / 4 ≤ (ξ * Q) ^ 2 := by nlinarith
    have h4 : 1 / (64 * ξ) ≤ (ξ * Q) ^ 2 / (16 * ξ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hx2 : 1 / (64 * ξ) ≤ x ^ 2 := by linarith
    have hexp : 2 * Real.exp (-x ^ 2 / (2 * 6)) ≤ 2 * Real.exp (-((1 / 768) / ξ)) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
      have e : (1 / 768 : ℝ) / ξ = (1 / (64 * ξ)) / (2 * 6) := by
        field_simp
        ring
      rw [neg_div, neg_le_neg_iff, e]
      exact div_le_div_of_nonneg_right hx2 (by norm_num)
    linarith

/-- **Gaussian union bound over the grid** (blueprint proof of Proposition `prop:crossing`): if
`0 < ξ_γ ≤ 1` and `ξ_γ Q_γ ≥ 1/2`, then the probability that
`|H(s,t) - H(s,s)| ≥ Q log r(s,t) + 2ε'` for some `(s,t) ∈ S_{m(γ)}²` is at most
`16 ξ^{-6} (2 e^{-1/(768 ξ)} + 2 e^{-ε'²/(3 ξ^{1/8})})`. -/
theorem measure_exists_H_sub_ge_le {γ ε' : ℝ} (hξ : 0 < S.ξ γ) (hξ1 : S.ξ γ ≤ 1)
    (hξQ : 1 / 2 ≤ S.ξ γ * Q γ) (hε' : 0 < ε') :
    stdP {ω | ∃ k : ℕ, k ≤ 2 ^ S.gridLevel γ ∧ ∃ l : ℕ, l ≤ 2 ^ S.gridLevel γ ∧
        Q γ * Real.log ‖(((k : ℝ) / 2 ^ S.gridLevel γ : ℝ) : ℂ) * Complex.I -
            (1 + (((l : ℝ) / 2 ^ S.gridLevel γ : ℝ) : ℂ) * Complex.I)‖ + 2 * ε' ≤
          |S.H ((k : ℝ) / 2 ^ S.gridLevel γ) ((l : ℝ) / 2 ^ S.gridLevel γ) ω -
            S.H ((k : ℝ) / 2 ^ S.gridLevel γ) ((k : ℝ) / 2 ^ S.gridLevel γ) ω|} ≤
      ENNReal.ofReal (16 * (S.ξ γ)⁻¹ ^ 6 * (2 * Real.exp (-((1 / 768) / S.ξ γ)) +
        2 * Real.exp (-((ε' ^ 2 / 3) / S.ξ γ ^ (1 / 8 : ℝ))))) := by
  set m := S.gridLevel γ with hm
  refine (measure_exists_grid_le stdP (2 ^ m) _ fun k hk l hl =>
    S.measure_H_sub_ge_le hξ hξQ hε' (div_two_pow_mem_Icc hk) (div_two_pow_mem_Icc hl)).trans ?_
  rw [natCast_two_pow_add_one_sq, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  have h := S.sq_two_pow_gridLevel_add_one_le hξ hξ1
  rwa [← hm] at h

/-! ## The deterministic lower bound -/

/-- **The lower bound on a good event** (blueprint proof of Proposition `prop:crossing`,
(eq:lower-grid)). Let `m = m(γ)`, `K = ξ^{-1/8}`, `0 < ξ ≤ 1` and `2 ξ^{1/4} ≤ ε/4`. If
`M ≤ H(y, y)` for dyadic `y`, `A_γ(S) ≤ K`, `I_γ(S, 1)⁻¹ ≤ K`, `|𝓡| < ε/4` on `S_m²` and
`|H(s,t) - H(s,s)| < Q log r(s,t) + ε/2` on `S_m²`, then `𝖸_γ ≥ M - ε`. -/
theorem M_sub_le_crossY {γ ε : ℝ} (hξ : 0 < S.ξ γ) (hξ1 : S.ξ γ ≤ 1)
    (hsmall : 2 * S.ξ γ ^ (1 / 4 : ℝ) ≤ ε / 4) {ω : Coord}
    (hM : ∀ y ∈ dyadicUnit, S.M ω ≤ S.H y y ω)
    (hA : holderConst (S.D γ ω).1 unitSquare ≤ ENNReal.ofReal (S.ξ γ ^ (-(1 / 8) : ℝ)))
    (hI : (sepInf (S.D γ ω).1 unitSquare 1)⁻¹ ≤ ENNReal.ofReal (S.ξ γ ^ (-(1 / 8) : ℝ)))
    (hR : ∀ k : ℕ, k ≤ 2 ^ S.gridLevel γ → ∀ l : ℕ, l ≤ 2 ^ S.gridLevel γ →
      |S.residual γ ((k : ℝ) / 2 ^ S.gridLevel γ) ((l : ℝ) / 2 ^ S.gridLevel γ) ω| < ε / 4)
    (hH : ∀ k : ℕ, k ≤ 2 ^ S.gridLevel γ → ∀ l : ℕ, l ≤ 2 ^ S.gridLevel γ →
      |S.H ((k : ℝ) / 2 ^ S.gridLevel γ) ((l : ℝ) / 2 ^ S.gridLevel γ) ω -
          S.H ((k : ℝ) / 2 ^ S.gridLevel γ) ((k : ℝ) / 2 ^ S.gridLevel γ) ω| <
        Q γ * Real.log ‖(((k : ℝ) / 2 ^ S.gridLevel γ : ℝ) : ℂ) * Complex.I -
            (1 + (((l : ℝ) / 2 ^ S.gridLevel γ : ℝ) : ℂ) * Complex.I)‖ + 2 * (ε / 4)) :
    S.M ω - ε ≤ S.crossY γ ω := by
  set m := S.gridLevel γ with hm
  set ξ := S.ξ γ with hξdef
  set K : ℝ := ξ ^ (-(1 / 8) : ℝ) with hKdef
  have hK : 0 < K := by positivity
  set d := S.D γ ω with hd
  -- the Hölder bound on the unit square
  have hAtop : holderConst d.1 unitSquare ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA
  have hAK : (holderConst d.1 unitSquare).toReal ≤ K := ENNReal.toReal_le_of_le_ofReal hK.le hA
  have hA' : ∀ z ∈ unitSquare, ∀ w ∈ unitSquare, d.1 (z, w) ≤ K * ‖z - w‖ ^ (1 / 2 : ℝ) :=
    fun z hz w hw => (dist_le_holderConst_mul d hAtop hz hw).trans
      (mul_le_mul_of_nonneg_right hAK (by positivity))
  -- the separation bound on the crossing pairs
  have hI' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      K⁻¹ ≤ d.1 ((s : ℂ) * Complex.I, 1 + (t : ℂ) * Complex.I) := by
    intro s hs t ht
    have h1 := sepInf_le_ofReal d.1 (sI_mem_unitSquare hs) (one_add_tI_mem_unitSquare ht)
      (one_le_norm_sI_sub s t)
    have h2 : (ENNReal.ofReal K)⁻¹ ≤ sepInf d.1 unitSquare 1 := ENNReal.inv_le_iff_inv_le.1 hI
    rw [← ENNReal.ofReal_inv_of_pos hK] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (contMetric_nonneg d _ _)).1 (h2.trans h1)
  -- the grid values
  have hgrid : ∀ k : ℕ, k ≤ 2 ^ m → ∀ l : ℕ, l ≤ 2 ^ m →
      S.b γ + ξ * (S.M ω - 3 * (ε / 4)) ≤ Real.log (d.1 ((((k : ℝ) / 2 ^ m : ℝ) : ℂ) *
        Complex.I, 1 + (((l : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I)) := by
    intro k hk l hl
    have hRk := hR k hk l hl
    have hHk := hH k hk l hl
    have hMk := hM ((k : ℝ) / 2 ^ m) ⟨m, k, hk, rfl⟩
    set ℓ := Real.log (d.1 ((((k : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I,
      1 + (((l : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I)) with hℓ
    set lr := Real.log ‖(((k : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I -
      (1 + (((l : ℝ) / 2 ^ m : ℝ) : ℂ) * Complex.I)‖ with hlr
    set a := (ℓ - S.b γ - ξ * Q γ * lr) / ξ with ha
    have hres : S.residual γ ((k : ℝ) / 2 ^ m) ((l : ℝ) / 2 ^ m) ω =
        a - S.H ((k : ℝ) / 2 ^ m) ((l : ℝ) / 2 ^ m) ω := rfl
    rw [hres] at hRk
    have hℓa : ℓ = S.b γ + ξ * Q γ * lr + ξ * a := by
      rw [ha]
      field_simp
      ring
    have hlow : S.M ω - Q γ * lr - 3 * (ε / 4) ≤ a := by
      have h1 := (abs_lt.1 hRk).1
      have h2 := (abs_lt.1 hHk).1
      linarith
    have h3 : ξ * (S.M ω - Q γ * lr - 3 * (ε / 4)) ≤ ξ * a :=
      mul_le_mul_of_nonneg_left hlow hξ.le
    rw [hℓa]
    nlinarith
  -- the discretization step
  have hcross := log_crossFn_ge_of_grid d hK m hA' hI' hgrid
  have hsmall' := two_mul_sq_mul_rpow_le hξ (S.inv_pow_three_le_two_pow_gridLevel hξ hξ1) hsmall
  rw [← hm] at hsmall'
  unfold crossY
  rw [le_div_iff₀ hξ]
  nlinarith

/-! ## The lower bound in probability -/

/-- **Blueprint Proposition `prop:crossing`, lower bound**, assuming Lemma `lem:energy-approx`:
for every `ε > 0`, `P[𝖸_γ < M - ε] → 0` as `γ ↓ 0`. -/
theorem tendsto_measure_crossY_lt (hY : S.EnergyApprox) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun γ => stdP {ω | S.crossY γ ω < S.M ω - ε}) (𝓝[>] 0) (𝓝 0) := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨γ6, hγ6, hS6⟩ := S.S6 1 le_rfl
  obtain ⟨C6, hC6top, hC6⟩ := hS6 unitSquare isCompact_unitSquare 1 one_pos
  obtain ⟨⟨γe, C₁, hγe, hγe2, hb⟩, -, hξQ⟩ := S.exponents
  have hR := S.tendsto_measure_exists_gridResidual hY hε4
  -- eventual conditions on `γ`
  have hev1 : ∀ᶠ γ in 𝓝[>] (0 : ℝ), γ ∈ Ioc (0 : ℝ) (min γ6 γe) :=
    Ioc_mem_nhdsGT (lt_min hγ6 hγe)
  have hev2 : ∀ᶠ γ in 𝓝[>] (0 : ℝ), 1 / 2 < S.ξ γ * Q γ :=
    hξQ.eventually_const_lt (by norm_num)
  have hev3 : ∀ᶠ γ in 𝓝[>] (0 : ℝ), 2 * S.ξ γ ^ (1 / 4 : ℝ) ≤ ε / 4 :=
    (S.tendsto_mul_xi_rpow 2 (by norm_num : (0 : ℝ) < 1 / 4)).eventually (Iic_mem_nhds hε4)
  -- the bound and its limit
  set g : ℝ → ℝ := fun x => 16 * x⁻¹ ^ 6 * (2 * Real.exp (-((1 / 768) / x)) +
    2 * Real.exp (-(((ε / 4) ^ 2 / 3) / x ^ (1 / 8 : ℝ)))) with hg
  have hg0 : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h1 := tendsto_inv_pow_mul_exp_neg_div_rpow 6 (b := 1) one_pos (c := 1 / 768)
      (by norm_num)
    have h2 := tendsto_inv_pow_mul_exp_neg_div_rpow 6 (b := 1 / 8) (by norm_num)
      (c := (ε / 4) ^ 2 / 3) (by positivity)
    have h := (h1.const_mul 32).add (h2.const_mul 32)
    simp only [mul_zero, add_zero] at h
    refine h.congr fun x => ?_
    simp only [hg, Real.rpow_one]
    ring
  have hA0 := S.tendsto_ofReal_mul_xi_rpow C6.toReal (by norm_num : (0 : ℝ) < 1 / 8)
  have hH0 : Tendsto (fun γ => ENNReal.ofReal (g (S.ξ γ))) (𝓝[>] 0) (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp (hg0.comp S.tendsto_xi_nhdsGT)
    rwa [ENNReal.ofReal_zero] at h
  have hlim := ((hA0.add hA0).add hR).add hH0
  rw [add_zero, add_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hev1, hev2, hev3] with γ hγ hγQ hγs
  have hγ6' : γ ∈ Ioc (0 : ℝ) γ6 := ⟨hγ.1, hγ.2.trans (min_le_left _ _)⟩
  have hγe' : γ ∈ Ioc (0 : ℝ) γe := ⟨hγ.1, hγ.2.trans (min_le_right _ _)⟩
  obtain ⟨h1, -, h3, -⟩ := hb γ hγe'
  have hξ : 0 < S.ξ γ := lt_of_lt_of_le (by linarith [hγ.1]) h1
  have hξ1 : S.ξ γ ≤ 1 := h3.trans (by norm_num)
  obtain ⟨hCA, hCI⟩ := hC6 γ hγ6'
  simp only [ENNReal.rpow_one] at hCA hCI
  set K : ℝ := S.ξ γ ^ (-(1 / 8) : ℝ) with hKdef
  have hK : 0 < K := by positivity
  have hKinv : C6.toReal / K = C6.toReal * S.ξ γ ^ (1 / 8 : ℝ) := by
    rw [hKdef, Real.rpow_neg hξ.le, div_inv_eq_mul]
  -- the exceptional events
  set N0 : Set Coord := {ω | ¬ ∀ y ∈ dyadicUnit, S.M ω ≤ S.H y y ω} with hN0def
  have hN0 : stdP N0 = 0 := ae_iff.1 S.ae_M_le_H
  set EA : Set Coord := {ω | ENNReal.ofReal K < holderConst (S.D γ ω).1 unitSquare} with hEA
  set EI : Set Coord := {ω | ENNReal.ofReal K < (sepInf (S.D γ ω).1 unitSquare 1)⁻¹} with hEI
  set ER : Set Coord := {ω | ∃ k : ℕ, k ≤ 2 ^ S.gridLevel γ ∧ ∃ l : ℕ,
    l ≤ 2 ^ S.gridLevel γ ∧ ε / 4 ≤
      |S.residual γ ((k : ℝ) / 2 ^ S.gridLevel γ) ((l : ℝ) / 2 ^ S.gridLevel γ) ω|} with hER
  set EH : Set Coord := {ω | ∃ k : ℕ, k ≤ 2 ^ S.gridLevel γ ∧ ∃ l : ℕ, l ≤ 2 ^ S.gridLevel γ ∧
    Q γ * Real.log ‖(((k : ℝ) / 2 ^ S.gridLevel γ : ℝ) : ℂ) * Complex.I -
        (1 + (((l : ℝ) / 2 ^ S.gridLevel γ : ℝ) : ℂ) * Complex.I)‖ + 2 * (ε / 4) ≤
      |S.H ((k : ℝ) / 2 ^ S.gridLevel γ) ((l : ℝ) / 2 ^ S.gridLevel γ) ω -
        S.H ((k : ℝ) / 2 ^ S.gridLevel γ) ((k : ℝ) / 2 ^ S.gridLevel γ) ω|} with hEH
  have hsub : {ω | S.crossY γ ω < S.M ω - ε} ⊆ N0 ∪ EA ∪ EI ∪ ER ∪ EH := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨h0, hA⟩, hI⟩, hRω⟩, hHω⟩ := hcon
    have hM : ∀ y ∈ dyadicUnit, S.M ω ≤ S.H y y ω := not_not.1 h0
    have hR' : ∀ k : ℕ, k ≤ 2 ^ S.gridLevel γ → ∀ l : ℕ, l ≤ 2 ^ S.gridLevel γ →
        |S.residual γ ((k : ℝ) / 2 ^ S.gridLevel γ) ((l : ℝ) / 2 ^ S.gridLevel γ) ω| < ε / 4 :=
      fun k hk l hl => not_le.1 fun h => hRω ⟨k, hk, l, hl, h⟩
    have hH' : ∀ k : ℕ, k ≤ 2 ^ S.gridLevel γ → ∀ l : ℕ, l ≤ 2 ^ S.gridLevel γ →
        |S.H ((k : ℝ) / 2 ^ S.gridLevel γ) ((l : ℝ) / 2 ^ S.gridLevel γ) ω -
            S.H ((k : ℝ) / 2 ^ S.gridLevel γ) ((k : ℝ) / 2 ^ S.gridLevel γ) ω| <
          Q γ * Real.log ‖(((k : ℝ) / 2 ^ S.gridLevel γ : ℝ) : ℂ) * Complex.I -
              (1 + (((l : ℝ) / 2 ^ S.gridLevel γ : ℝ) : ℂ) * Complex.I)‖ + 2 * (ε / 4) :=
      fun k hk l hl => not_le.1 fun h => hHω ⟨k, hk, l, hl, h⟩
    have hle := S.M_sub_le_crossY hξ hξ1 hγs hM (not_lt.1 hA) (not_lt.1 hI) hR' hH'
    exact absurd hω (not_lt.2 hle)
  have hEAle : stdP EA ≤ ENNReal.ofReal (C6.toReal * S.ξ γ ^ (1 / 8 : ℝ)) := by
    rw [← hKinv]
    exact measure_ofReal_lt_le (S.measurable_holderConst γ unitSquare).aemeasurable hCA
      hC6top hK
  have hEIle : stdP EI ≤ ENNReal.ofReal (C6.toReal * S.ξ γ ^ (1 / 8 : ℝ)) := by
    rw [← hKinv]
    exact measure_ofReal_lt_le (S.measurable_sepInf γ unitSquare 1).inv.aemeasurable hCI
      hC6top hK
  have hEHle : stdP EH ≤ ENNReal.ofReal (g (S.ξ γ)) :=
    S.measure_exists_H_sub_ge_le hξ hξ1 hγQ.le hε4
  calc stdP {ω | S.crossY γ ω < S.M ω - ε} ≤ stdP (N0 ∪ EA ∪ EI ∪ ER ∪ EH) := measure_mono hsub
    _ ≤ stdP N0 + stdP EA + stdP EI + stdP ER + stdP EH := by
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        refine (measure_union_le _ _).trans (add_le_add_left ?_ _)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (C6.toReal * S.ξ γ ^ (1 / 8 : ℝ)) +
          ENNReal.ofReal (C6.toReal * S.ξ γ ^ (1 / 8 : ℝ)) + stdP ER +
            ENNReal.ofReal (g (S.ξ γ)) := by
        rw [hN0, zero_add]
        gcongr

end Setup

end GaussianLQG
