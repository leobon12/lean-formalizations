/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb7Obs

/-!
# The Lyapunov inequality for the side oscillation of the inner reference

Packet PROVE-TRIALS-HI2. For the inner reference of Aux. lemma 111 (Specification p. 364; plan in
`planning/handoffs/PROVE-TRIALS-HI.md`, "Details" §5), the side oscillation `∫ (1/X_near² − 1/X_far²)` is controlled by
`∫ D^{−θ−2} y^{−θ−2}` with `y = 1 − U` the relative distance of the driver to the nearest right mark. That integral has
finite expectation by a Lyapunov function `D^{−θ} (ψ_ε(1 − U) + λ)` with the globally smooth regularization
`ψ_ε(y) = (y² + ε²)^{−θ/2}`: its generator along the evolution is `D^{−θ−2} J(U)` with

  `J(u) = −2θ H(u)/(u(1 − u)) + H'(u)(a/u − b/(1 − u)) + (κ/2) H''(u)`,  `H(u) = ψ_ε(1 − u) + λ`,

(the factor `−2θ/(u(1 − u))` is `D^{θ}·(d/dt) D^{−θ}`), and this file proves the pointwise inequality
`J(u) ≤ −c₀ ((1 − u)² + ε²)^{−θ/2−1}` on `(0, 1)` uniformly in `ε > 0`, for `a > 0` and `b > κ/2` (`exists_oscJ_le`):
the `b`-term of the drift dominates the Itô correction when `θ < 2b/κ − 1`, the cross term `a/u` is absorbed by the `λ`
term near `u = 0`, and by Young's inequality elsewhere.

## Main results

* `psiE`, `psiE'`, `psiE''`, `hasDerivAt_psiE`, `hasDerivAt_psiE'`, `contDiff_psiE`;
* `oscH`, `oscH'`, `oscH''`, `oscJ`;
* **`exists_oscJ_le`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace InteractingSLE

namespace Sec7

namespace TrialsHi2

/-! ### The regularized power -/

section Psi

/-- `ψ_ε(x) = (x² + ε²)^{−θ/2}`. -/
def psiE (θ ε x : ℝ) : ℝ := (x ^ 2 + ε ^ 2) ^ (-θ / 2)

/-- `ψ_ε'(x) = −θ x (x² + ε²)^{−θ/2−1}`. -/
def psiE' (θ ε x : ℝ) : ℝ := -θ * x * (x ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)

/-- `ψ_ε''(x) = −θ (x² + ε²)^{−θ/2−1} + θ(θ + 2) x² (x² + ε²)^{−θ/2−2}`. -/
def psiE'' (θ ε x : ℝ) : ℝ :=
  -θ * (x ^ 2 + ε ^ 2) ^ (-θ / 2 - 1) + θ * (θ + 2) * x ^ 2 * (x ^ 2 + ε ^ 2) ^ (-θ / 2 - 2)

variable {θ ε : ℝ}

theorem sq_add_sq_pos' (hε : 0 < ε) (x : ℝ) : 0 < x ^ 2 + ε ^ 2 := by positivity

theorem hasDerivAt_psiE (hε : 0 < ε) (x : ℝ) : HasDerivAt (psiE θ ε) (psiE' θ ε x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + ε ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (ε ^ 2)
  have h2 := h1.rpow_const (p := -θ / 2) (Or.inl (sq_add_sq_pos' hε x).ne')
  unfold psiE psiE'
  convert h2 using 1
  ring

theorem hasDerivAt_psiE' (hε : 0 < ε) (x : ℝ) : HasDerivAt (psiE' θ ε) (psiE'' θ ε x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + ε ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const (ε ^ 2)
  have h2 := h1.rpow_const (p := -θ / 2 - 1) (Or.inl (sq_add_sq_pos' hε x).ne')
  have e : (-θ / 2 - 1 - 1 : ℝ) = -θ / 2 - 2 := by ring
  rw [e] at h2
  have h3 := ((hasDerivAt_id x).const_mul (-θ)).fun_mul h2
  unfold psiE' psiE''
  refine h3.congr_deriv ?_
  simp only [id]; ring

theorem contDiff_psiE (hε : 0 < ε) {n : WithTop ℕ∞} : ContDiff ℝ n (psiE θ ε) := by
  unfold psiE
  exact ContDiff.rpow_const_of_ne (by fun_prop) fun x => (sq_add_sq_pos' hε x).ne'

theorem psiE_nonneg (x : ℝ) : 0 ≤ psiE θ ε x := Real.rpow_nonneg (by positivity) _

/-- `ψ_ε(x) ≤ (x²)^{−θ/2}` for `x ≠ 0`, `θ ≥ 0` (uniformly in `ε`). -/
theorem psiE_le (hθ : 0 ≤ θ) {x : ℝ} (hx : x ≠ 0) : psiE θ ε x ≤ (x ^ 2) ^ (-θ / 2) :=
  Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by linarith)

end Psi

/-! ### The Lyapunov bracket -/

section Bracket

/-- `H(u) = ψ_ε(1 − u) + λ`. -/
def oscH (θ ε lam u : ℝ) : ℝ := psiE θ ε (1 - u) + lam

/-- `H'(u) = −ψ_ε'(1 − u)`. -/
def oscH' (θ ε u : ℝ) : ℝ := -psiE' θ ε (1 - u)

/-- `H''(u) = ψ_ε''(1 − u)`. -/
def oscH'' (θ ε u : ℝ) : ℝ := psiE'' θ ε (1 - u)

/-- **The Lyapunov bracket** `J(u) = −2θ H(u)/(u(1 − u)) + H'(u)(a/u − b/(1 − u)) + (κ/2) H''(u)`. -/
def oscJ (κ a b θ ε lam u : ℝ) : ℝ :=
  -2 * θ * oscH θ ε lam u / (u * (1 - u)) + oscH' θ ε u * Clock.angDrift a b u + κ / 2 * oscH'' θ ε u

variable {θ ε : ℝ}

theorem hasDerivAt_oscH (hε : 0 < ε) (lam u : ℝ) : HasDerivAt (oscH θ ε lam) (oscH' θ ε u) u := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := by simpa using (hasDerivAt_id u).const_sub 1
  have h3 := ((hasDerivAt_psiE (θ := θ) hε (1 - u)).comp u h1).add_const lam
  exact h3.congr_deriv (by simp only [oscH']; ring)

theorem hasDerivAt_oscH' (hε : 0 < ε) (u : ℝ) : HasDerivAt (oscH' θ ε) (oscH'' θ ε u) u := by
  have h1 : HasDerivAt (fun u : ℝ => 1 - u) (-1) u := by simpa using (hasDerivAt_id u).const_sub 1
  have h3 := ((hasDerivAt_psiE' (θ := θ) hε (1 - u)).comp u h1).neg
  exact h3.congr_deriv (by simp only [oscH'']; ring)

theorem contDiff_oscH (hε : 0 < ε) (lam : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (oscH θ ε lam) := by
  unfold oscH
  exact ((contDiff_psiE hε).comp (contDiff_const.sub contDiff_id)).add contDiff_const

theorem oscH_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (u : ℝ) : 0 ≤ oscH θ ε lam u :=
  add_nonneg (psiE_nonneg _) hlam

/-- `(1/4)^{−2} = 16`. -/
theorem quarter_rpow_neg_two : (1 / 4 : ℝ) ^ (-2 : ℝ) = 16 := by
  rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]; norm_num

/-- **The Lyapunov inequality** for the side oscillation: for `a > 0` and `b > κ/2` there are `0 < θ ≤ 1`, `λ ≥ 0`
and `c₀ > 0` with `J(u) ≤ −c₀ ((1 − u)² + ε²)^{−θ/2−1}` for every `ε > 0` and `u ∈ (0, 1)`. -/
theorem exists_oscJ_le {κ a b : ℝ} (hκ : 0 < κ) (ha : 0 < a) (hb : κ / 2 < b) :
    ∃ θ lam c₀ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ lam ∧ 0 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ∀ u ∈ Ioo (0 : ℝ) 1,
      oscJ κ a b θ ε lam u ≤ -c₀ * ((1 - u) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1) := by
  set θ := min 1 ((2 * b / κ - 1) / 2) with hθdef
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hb' : 1 < 2 * b / κ := by rw [lt_div_iff₀ hκ]; linarith
  have hθ0 : 0 < θ := lt_min one_pos (by linarith)
  have hθb : θ ≤ (2 * b / κ - 1) / 2 := min_le_right _ _
  set δ := b - κ * (θ + 1) / 2 with hδdef
  have hδ : (b - κ / 2) / 2 ≤ δ := by
    have h1 : κ * θ ≤ b - κ / 2 := by
      have := mul_le_mul_of_nonneg_left hθb hκ.le
      have e : κ * ((2 * b / κ - 1) / 2) = b - κ / 2 := by field_simp
      linarith
    rw [hδdef]; linarith
  have hδ0 : 0 < δ := lt_of_lt_of_le (by linarith) hδ
  set η := δ / (4 * a) with hηdef
  have hη0 : 0 < η := by positivity
  set Cη := (η ^ 2) ^ (-θ / 2 - 1) with hCηdef
  have hCη0 : 0 < Cη := Real.rpow_pos_of_pos (by positivity) _
  set lam := max (8 * a) (a * Cη / 4) with hlamdef
  have hlam1 : 8 * a ≤ lam := le_max_left _ _
  have hlam2 : a * Cη / 4 ≤ lam := le_max_right _ _
  have hlam0 : 0 ≤ lam := (by positivity : (0 : ℝ) ≤ 8 * a).trans hlam1
  refine ⟨θ, lam, θ * δ / 2, hθ0, hθ1, hlam0, by positivity, fun ε hε u hu => ?_⟩
  clear_value lam Cη η δ θ
  set y := 1 - u with hydef
  have hy0 : 0 < y := by rw [hydef]; linarith [hu.2]
  have hy1 : y < 1 := by rw [hydef]; linarith [hu.1]
  set Pq := y ^ 2 + ε ^ 2 with hPdef
  have hP : 0 < Pq := sq_add_sq_pos' hε y
  set A := Pq ^ (-θ / 2 - 1) with hAdef
  set Bq := Pq ^ (-θ / 2 - 2) with hBdef
  have hA0 : 0 < A := Real.rpow_pos_of_pos hP _
  have hB0 : 0 < Bq := Real.rpow_pos_of_pos hP _
  have hAB : A = Bq * Pq := by
    rw [hAdef, hBdef, ← Real.rpow_add_one hP.ne']
    congr 1; ring
  have hyB : y ^ 2 * Bq ≤ A := by
    rw [hAB, hPdef]
    have := mul_nonneg (sq_nonneg ε) hB0.le
    linarith [show Bq * (y ^ 2 + ε ^ 2) = y ^ 2 * Bq + ε ^ 2 * Bq by ring]
  -- the terms of `J`
  have hψ : 0 ≤ psiE θ ε y := psiE_nonneg y
  have hu0 := hu.1
  have huy : 0 < u * y := mul_pos hu0 hy0
  have hJ : oscJ κ a b θ ε lam u = -2 * θ * (psiE θ ε y + lam) / (u * y) + θ * a * y * A / u - θ * b * A +
      κ / 2 * (-θ * A + θ * (θ + 2) * y ^ 2 * Bq) := by
    simp only [oscJ, oscH, oscH', oscH'', psiE', psiE'', Clock.angDrift, ← hydef, ← hPdef, ← hAdef, ← hBdef]
    field_simp
    ring
  rw [hJ]
  clear_value A Bq Pq y
  have hIto : κ / 2 * (-θ * A + θ * (θ + 2) * y ^ 2 * Bq) ≤ κ / 2 * (θ * (θ + 1) * A) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hyB (by positivity : (0 : ℝ) ≤ θ * (θ + 2))
    linarith [show θ * (θ + 2) * (y ^ 2 * Bq) = θ * (θ + 2) * y ^ 2 * Bq by ring]
  have hX3 : -(θ * b * A) + κ / 2 * (-θ * A + θ * (θ + 2) * y ^ 2 * Bq) ≤ -(θ * δ * A) := by
    have e : θ * b * A - κ / 2 * (θ * (θ + 1) * A) = θ * δ * A := by rw [hδdef]; ring
    linarith
  have hψt : -2 * θ * (psiE θ ε y + lam) / (u * y) ≤ -2 * θ * lam / (u * y) := by
    apply div_le_div_of_nonneg_right _ huy.le
    have := mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * θ) hψ
    linarith [show -2 * θ * (psiE θ ε y + lam) = -2 * θ * lam - 2 * θ * psiE θ ε y by ring]
  have hc0 : 0 ≤ θ * δ / 2 * A := by positivity
  have hlam' : -2 * θ * lam ≤ 0 := by nlinarith
  rcases le_or_gt u (1 / 2) with hu2 | hu2
  · -- near `u = 0`: the cross term is absorbed by `λ`
    have hy2 : 1 / 2 ≤ y := by rw [hydef]; linarith
    have hy2' : (1 / 4 : ℝ) ≤ y ^ 2 := by
      calc (1 / 4 : ℝ) = (1 / 2) * (1 / 2) := by norm_num
        _ ≤ y * y := mul_le_mul hy2 hy2 (by norm_num) hy0.le
        _ = y ^ 2 := (sq y).symm
    have hAy : A ≤ 16 := by
      have hyP : y ^ 2 ≤ Pq := by rw [hPdef]; linarith [sq_nonneg ε]
      have h1 : A ≤ (y ^ 2) ^ (-θ / 2 - 1) := by
        rw [hAdef]; exact Real.rpow_le_rpow_of_nonpos (pow_pos hy0 2) hyP (by linarith)
      have h2 : (y ^ 2) ^ (-θ / 2 - 1) ≤ (1 / 4 : ℝ) ^ (-θ / 2 - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hy2' (by linarith)
      have h3 : (1 / 4 : ℝ) ^ (-θ / 2 - 1) ≤ (1 / 4 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      rw [quarter_rpow_neg_two] at h3
      linarith
    have hcross : θ * a * y * A / u ≤ 16 * θ * a / u := by
      apply div_le_div_of_nonneg_right _ hu0.le
      have h1 : y * A ≤ 16 := by
        calc y * A ≤ 1 * A := mul_le_mul_of_nonneg_right hy1.le hA0.le
          _ ≤ 16 := by linarith
      have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ θ * a)
      linarith [show θ * a * (y * A) = θ * a * y * A by ring, show θ * a * 16 = 16 * θ * a by ring]
    have hlamt : -2 * θ * lam / (u * y) ≤ -2 * θ * lam / u := by
      have e : -2 * θ * lam / (u * y) - -2 * θ * lam / u = -2 * θ * lam * (1 - y) / (u * y) := by
        field_simp; ring
      have : -2 * θ * lam * (1 - y) / (u * y) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hlam' (by linarith)) huy.le
      linarith
    have hsum : 16 * θ * a / u + -2 * θ * lam / u ≤ 0 := by
      rw [← add_div]
      refine div_nonpos_of_nonpos_of_nonneg ?_ hu0.le
      have := mul_le_mul_of_nonneg_left hlam1 (by positivity : (0 : ℝ) ≤ 2 * θ)
      linarith [show 2 * θ * (8 * a) = 16 * θ * a by ring]
    have hfin : -(θ * δ * A) ≤ -(θ * δ / 2) * A := by linarith
    linarith
  · -- away from `u = 0`: Young's inequality
    have hyA : y * A ≤ η * A + Cη := by
      rcases le_or_gt y η with hyη | hyη
      · have := mul_le_mul_of_nonneg_right hyη hA0.le
        linarith
      · have hηP : η ^ 2 ≤ Pq := by
          rw [hPdef]
          have : η ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hη0.le hyη.le 2
          linarith [sq_nonneg ε]
        have h1 : A ≤ Cη := by
          rw [hCηdef, hAdef]; exact Real.rpow_le_rpow_of_nonpos (pow_pos hη0 2) hηP (by linarith)
        have h2 : y * A ≤ 1 * A := mul_le_mul_of_nonneg_right hy1.le hA0.le
        have h3 : 0 ≤ η * A := by positivity
        linarith
    have hcross : θ * a * y * A / u ≤ 2 * θ * a * (η * A + Cη) := by
      rw [div_le_iff₀ hu0]
      have h1 : θ * a * (y * A) ≤ θ * a * (η * A + Cη) := mul_le_mul_of_nonneg_left hyA (by positivity)
      have h2 : 0 ≤ θ * a * (η * A + Cη) := by positivity
      have h3 : θ * a * (η * A + Cη) ≤ θ * a * (η * A + Cη) * (2 * u) := by
        have : (1 : ℝ) ≤ 2 * u := by linarith
        exact le_mul_of_one_le_right h2 this
      linarith [show θ * a * (y * A) = θ * a * y * A by ring,
        show θ * a * (η * A + Cη) * (2 * u) = 2 * θ * a * (η * A + Cη) * u by ring]
    have hlamt : -2 * θ * lam / (u * y) ≤ -8 * θ * lam := by
      have h4 : 4 * (u * y) ≤ 1 := by
        have hs : u + y = 1 := by rw [hydef]; ring
        linarith [sq_nonneg (u - y), show (u - y) ^ 2 = (u + y) ^ 2 - 4 * (u * y) by ring,
          show (u + y) ^ 2 = 1 by rw [hs]; norm_num]
      have e : -2 * θ * lam / (u * y) - -8 * θ * lam = -2 * θ * lam * (1 - 4 * (u * y)) / (u * y) := by
        field_simp; ring
      have : -2 * θ * lam * (1 - 4 * (u * y)) / (u * y) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hlam' (by linarith)) huy.le
      linarith
    have hη4 : 2 * θ * a * η = θ * δ / 2 := by rw [hηdef]; field_simp; ring
    have hlamC : 2 * θ * a * Cη ≤ 8 * θ * lam := by
      have := mul_le_mul_of_nonneg_left hlam2 (by positivity : (0 : ℝ) ≤ 8 * θ)
      linarith [show 8 * θ * (a * Cη / 4) = 2 * θ * a * Cη by ring]
    have hsplit : 2 * θ * a * (η * A + Cη) = θ * δ / 2 * A + 2 * θ * a * Cη := by
      rw [← hη4]; ring
    have hfin : -(θ * δ * A) + θ * δ / 2 * A = -(θ * δ / 2) * A := by ring
    linarith

end Bracket

end TrialsHi2

end Sec7

end InteractingSLE
