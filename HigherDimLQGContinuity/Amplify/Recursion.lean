import HigherDimLQGContinuity.Amplify.Analytic

/-!
# Closed-form solutions of the band recursion (packet P7)

Blueprint `a:prop33`, "Estimates" (recursion `a:eq-recursion`, NA1 R9). Instead of the exact recursion
`C_j = b' + q_*(C_{j-1} - b')⁺ + ε_j`, `e_j = C'_{j-1} 2^{2+σ} H̄ e^{-σ a_j n} + e_{j-1}` we use explicit upper
solutions (any upper solution may be fed to Lemma 3.1(b), whose conclusion is monotone in `C` and `e`):

* `p7X qs C0 εbar j = q_*^j C₀ + j ε̄` (the excess over `b'` after `j` bands),
* `p7E e0 Γ H σ n a j = e₀ + j Γ (4H) e^{-σ a_j n}` (the additive error after `j` bands),

with band `j` (`0`-indexed) at radii `[e^{-2 a_{j+1} n}, e^{-a_{j+1} n}]`. `p7_stepC` and `p7_stepE` are the one-step
inequalities `hstepC`, `hstepE` of `p7_band_iter`, under the single condition `hεbar` on `ε̄` (which `p7_eps_bound`
verifies for the geometric exponents `a_j = L^{-j}/4`) and `b' + C₀ + N ε̄ ≤ Γ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-- The excess bound `q_*^j C₀ + j ε̄`. -/
def p7X (qs C0 εbar : ℝ) (j : ℕ) : ℝ := qs ^ j * C0 + j * εbar

/-- The additive error bound `e₀ + j Γ (4H) e^{-σ a_j n}`. -/
def p7E (e0 Γ H σ n : ℝ) (a : ℕ → ℝ) (j : ℕ) : ℝ := e0 + j * (Γ * (4 * H) * Real.exp (-(σ * (a j * n))))

theorem p7X_zero (qs C0 εbar : ℝ) : p7X qs C0 εbar 0 = C0 := by simp [p7X]

theorem p7E_zero (e0 Γ H σ n : ℝ) (a : ℕ → ℝ) : p7E e0 Γ H σ n a 0 = e0 := by simp [p7E]

theorem p7X_nonneg {qs C0 εbar : ℝ} (hqs : 0 ≤ qs) (hC0 : 0 ≤ C0) (hε : 0 ≤ εbar) (j : ℕ) :
    0 ≤ p7X qs C0 εbar j := by
  unfold p7X; positivity

theorem p7E_nonneg {e0 Γ H σ n : ℝ} {a : ℕ → ℝ} (he0 : 0 ≤ e0) (hΓ : 0 ≤ Γ) (hH : 0 ≤ H) (j : ℕ) :
    0 ≤ p7E e0 Γ H σ n a j := by
  unfold p7E; positivity

theorem p7X_le {qs C0 εbar : ℝ} (hqs : 0 ≤ qs) (hqs1 : qs ≤ 1) (hC0 : 0 ≤ C0) (hε : 0 ≤ εbar) {j N : ℕ}
    (hj : j ≤ N) : p7X qs C0 εbar j ≤ C0 + N * εbar := by
  unfold p7X
  have h1 : qs ^ j * C0 ≤ C0 := mul_le_of_le_one_left hC0 (pow_le_one₀ hqs hqs1)
  have h2 : (j : ℝ) * εbar ≤ N * εbar := mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hε
  linarith

/-- `e / (H⁻¹ (e^{-2x}/4)^β) = e H 4^β e^{2βx}`. -/
theorem p7_div_band (E H β x : ℝ) (hH : 0 < H) :
    E / (H⁻¹ * (Real.exp (-2 * x) / 4) ^ β) = E * H * 4 ^ β * Real.exp (2 * β * x) := by
  have h4 : (0 : ℝ) < 4 ^ β := Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.div_rpow (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
  have hx : Real.exp (2 * β * x) = (Real.exp (-2 * x * β))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hx]
  have he : 0 < Real.exp (-2 * x * β) := Real.exp_pos _
  field_simp

/-- `(2 e^{-x})^σ ≤ 2 e^{-σ x}` for `0 < σ ≤ 1`. -/
theorem p7_two_exp_rpow_le {x σ : ℝ} (hσ1 : σ ≤ 1) :
    (2 * Real.exp (-x)) ^ σ ≤ 2 * Real.exp (-(σ * x)) := by
  rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
  have h2 : (2 : ℝ) ^ σ ≤ 2 := by
    calc (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
      _ = 2 := Real.rpow_one 2
  have : Real.exp (-x * σ) = Real.exp (-(σ * x)) := by congr 1; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-- **One-step inequality for the coefficient** (`hstepC` of `p7_band_iter`). -/
theorem p7_stepC {qs C0 εbar e0 Γ H σ β n : ℝ} {a : ℕ → ℝ} {N : ℕ} (hqs1 : qs ≤ 1)
    (hε : 0 ≤ εbar) (hH : 0 < H)
    (hεbar : ∀ j < N, p7E e0 Γ H σ n a j * H * 4 ^ β * Real.exp (2 * β * (a (j + 1) * n)) ≤ εbar) :
    ∀ j < N, qs * p7X qs C0 εbar j +
      p7E e0 Γ H σ n a j / (H⁻¹ * (Real.exp (-2 * (a (j + 1) * n)) / 4) ^ β) ≤
        p7X qs C0 εbar (j + 1) := by
  intro j hj
  rw [p7_div_band _ H β _ hH]
  have h := hεbar j hj
  unfold p7X
  have h1 : qs * (qs ^ j * C0 + j * εbar) ≤ qs ^ (j + 1) * C0 + j * εbar := by
    have : qs * (j * εbar) ≤ j * εbar := mul_le_of_le_one_left (by positivity) hqs1
    rw [pow_succ]
    nlinarith
  push_cast
  linarith

/-- **One-step inequality for the additive error** (`hstepe` of `p7_band_iter`). -/
theorem p7_stepE {qs C0 εbar e0 Γ H σ n b' : ℝ} {a : ℕ → ℝ} {N : ℕ} (hqs : 0 ≤ qs) (hqs1 : qs ≤ 1)
    (hC0 : 0 ≤ C0) (hε : 0 ≤ εbar) (hH : 0 ≤ H) (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hn : 0 ≤ n) (hb' : 0 ≤ b')
    (ha : ∀ j, a (j + 1) ≤ a j) (hΓ : b' + C0 + N * εbar ≤ Γ) :
    ∀ j < N, (b' + p7X qs C0 εbar j) * (2 * H * (2 * Real.exp (-(a (j + 1) * n))) ^ σ) +
      p7E e0 Γ H σ n a j ≤ p7E e0 Γ H σ n a (j + 1) := by
  intro j hj
  have hX := p7X_le hqs hqs1 hC0 hε hj.le
  have hbX : b' + p7X qs C0 εbar j ≤ Γ := by linarith
  have hΓ0 : 0 ≤ Γ := by
    have : 0 ≤ (N : ℝ) * εbar := by positivity
    linarith
  have hpow := p7_two_exp_rpow_le (x := a (j + 1) * n) (σ := σ) hσ1
  have hexp : Real.exp (-(σ * (a j * n))) ≤ Real.exp (-(σ * (a (j + 1) * n))) := by
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right (ha j) hn
    have h2 := mul_le_mul_of_nonneg_left h1 hσ
    linarith
  have hfac : 0 ≤ 2 * H * (2 * Real.exp (-(a (j + 1) * n))) ^ σ := by positivity
  have h2 : (b' + p7X qs C0 εbar j) * (2 * H * (2 * Real.exp (-(a (j + 1) * n))) ^ σ) ≤
      Γ * (2 * H * (2 * Real.exp (-(σ * (a (j + 1) * n))))) := by
    calc (b' + p7X qs C0 εbar j) * (2 * H * (2 * Real.exp (-(a (j + 1) * n))) ^ σ)
        ≤ Γ * (2 * H * (2 * Real.exp (-(a (j + 1) * n))) ^ σ) := mul_le_mul_of_nonneg_right hbX hfac
      _ ≤ Γ * (2 * H * (2 * Real.exp (-(σ * (a (j + 1) * n))))) := by
        apply mul_le_mul_of_nonneg_left _ hΓ0
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have h3 : (j : ℝ) * (Γ * (4 * H) * Real.exp (-(σ * (a j * n)))) ≤
      (j : ℝ) * (Γ * (4 * H) * Real.exp (-(σ * (a (j + 1) * n)))) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg j)
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  unfold p7E
  push_cast
  calc (b' + p7X qs C0 εbar j) * (2 * H * (2 * Real.exp (-(a (j + 1) * n))) ^ σ) +
        (e0 + (j : ℝ) * (Γ * (4 * H) * Real.exp (-(σ * (a j * n)))))
      ≤ Γ * (2 * H * (2 * Real.exp (-(σ * (a (j + 1) * n))))) +
        (e0 + (j : ℝ) * (Γ * (4 * H) * Real.exp (-(σ * (a (j + 1) * n))))) := by
        linarith
    _ = e0 + ((j : ℝ) + 1) * (Γ * (4 * H) * Real.exp (-(σ * (a (j + 1) * n)))) := by ring

/-- **The bound on the recursion increments** (`hεbar` of `p7_stepC`) for exponents with `a_{j+1} = a_j / L`
(`2β ≤ σL/4`): the increment of band `j` is at most
`ε̄ = e₀ H 4^β e^{2β a₁ n} + N Γ (4H) H 4^β e^{-(3/4)σ a_N n}`. -/
theorem p7_eps_bound {e0 Γ H σ β n L : ℝ} {a : ℕ → ℝ} {N : ℕ} (he0 : 0 ≤ e0) (hΓ : 0 ≤ Γ) (hH : 0 ≤ H)
    (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hn : 0 ≤ n) (hL : 0 < L) (ha0 : ∀ j, 0 ≤ a j) (ha : ∀ j, a (j + 1) = a j / L)
    (hanti : Antitone a) (hβL : 2 * β ≤ σ / 4 * L) :
    ∀ j < N, p7E e0 Γ H σ n a j * H * 4 ^ β * Real.exp (2 * β * (a (j + 1) * n)) ≤
      e0 * H * 4 ^ β * Real.exp (2 * β * (a 1 * n)) +
        N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * (a N * n))) := by
  intro j hj
  have h4 : (0 : ℝ) ≤ 4 ^ β := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hA1 : Real.exp (2 * β * (a (j + 1) * n)) ≤ Real.exp (2 * β * (a 1 * n)) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right (hanti (by omega : 1 ≤ j + 1)) hn
  have hA2 : Real.exp (-(σ * (a j * n))) * Real.exp (2 * β * (a (j + 1) * n)) ≤
      Real.exp (-(3 / 4 * σ * (a N * n))) := by
    rw [← Real.exp_add, ha j]
    apply Real.exp_le_exp.mpr
    have hajn : 0 ≤ a j * n := mul_nonneg (ha0 j) hn
    have h1 : 2 * β * (a j / L * n) ≤ σ / 4 * (a j * n) := by
      have heq : 2 * β * (a j / L * n) = (2 * β) * (a j * n) / L := by ring
      rw [heq, div_le_iff₀ hL]
      have := mul_le_mul_of_nonneg_left hβL hajn
      linarith
    have h2 : a N * n ≤ a j * n := mul_le_mul_of_nonneg_right (hanti hj.le) hn
    have h3 : σ * (a N * n) ≤ σ * (a j * n) := mul_le_mul_of_nonneg_left h2 hσ
    linarith
  have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj.le
  have hK : 0 ≤ Γ * (4 * H) * H * 4 ^ β := by positivity
  unfold p7E
  have hsplit : (e0 + j * (Γ * (4 * H) * Real.exp (-(σ * (a j * n))))) * H * 4 ^ β *
      Real.exp (2 * β * (a (j + 1) * n)) =
      e0 * H * 4 ^ β * Real.exp (2 * β * (a (j + 1) * n)) +
        j * (Γ * (4 * H) * H * 4 ^ β) *
          (Real.exp (-(σ * (a j * n))) * Real.exp (2 * β * (a (j + 1) * n))) := by ring
  rw [hsplit]
  have hfirst : e0 * H * 4 ^ β * Real.exp (2 * β * (a (j + 1) * n)) ≤
      e0 * H * 4 ^ β * Real.exp (2 * β * (a 1 * n)) :=
    mul_le_mul_of_nonneg_left hA1 (by positivity)
  have hsecond : (j : ℝ) * (Γ * (4 * H) * H * 4 ^ β) *
      (Real.exp (-(σ * (a j * n))) * Real.exp (2 * β * (a (j + 1) * n))) ≤
      N * (Γ * (4 * H) * H * 4 ^ β) * Real.exp (-(3 / 4 * σ * (a N * n))) := by
    apply mul_le_mul _ hA2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hj' hK
  linarith

end HigherDimLQGContinuity
