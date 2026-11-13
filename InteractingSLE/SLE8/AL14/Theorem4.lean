import QuantumZipper.Proofs.RS.MartingaleBound
import QuantumZipper.Proofs.RS.LocalDynkinSuper
import QuantumZipper.Proofs.RS.OnePointState
import QuantumZipper.Proofs.ItoLite.Oscillation
import QuantumZipper.Proofs.RS.BMModulus
import QuantumZipper.Proofs.RS.TransienceCanon
import InteractingSLE.SLE8.ReverseFlow

/-!
# Alvisio–Lawler, Theorem 4 (upper bound): the κ = 8 reverse-flow derivative tail

Source: [AL14] M. Alvisio, G. F. Lawler, *Note on the existence and modulus of continuity of the
SLE₈ curve* (pinned preprint, `source/external/AL14/AL14.md`, anchors `thm-4`, `prop-4`, `prop-5`,
§§3.2–3.3, pp. 7–11). In [AL14]'s normalization (`a = 1/4`, standard Brownian driver `U`) the
reverse flow is `∂_t h_t(z) = 1/(4 (U_t − h_t(z)))`, `h_0(z) = z` (their (9)), and
`R_t = |h'_{e^{t/2}}(i)|`. **Theorem 4 (upper bound):** for `0 < β < 2` there is `c₂` with
`P{R_t ≥ e^{t/4} t^{−β}} ≤ c₂ e^{−t/2} t^{2β − 3/2} (log t)^5` for `t ≥ 2`.

## Route (deviation from [AL14]: a supersolution instead of Girsanov)

[AL14] weight the measure by the martingale `M = Φ²/sin Θ` (Proposition 4), pass to the
imaginary-part parametrization (§3.2), and bound Brownian probabilities under the weighted
measure (Proposition 5, Lemma 2, Lemmas 4–5). We prove the same upper bound with no change of
measure, time change or Brownian estimate, by one application of QuantumZipper's local Dynkin
supermartingale inequality `QuantumZipper.RS.integral_localDynkin_stopped_le` to an explicit
test function of the reverse-flow state. We work in the SLE₈ note's normalization (QuantumZipper's
`revMap (drive 8 B ω)`, `∂_s h = −2/(h − V)`, `V = √8 B`), with state `x = (Z, L)`,
`Z = X + iY = revMap V s z`, `L = log |∂_z revMap V s z|`, `N = X² + Y²`. For `θ > 0`, `c` and
`τ₁` put
* `σ = τ₁ − log Y` (a clock that decreases as the point rises),
* `ξ = ½ log N − log Y + c = log (|Z|/Y) + c ≥ c`,
* `superTest θ c τ₁ (Z, L) = e^{(2 + θ/2) L} Y^{−θ/2} σ^{−3/2} ξ exp(ξ − ξ²/(8σ))`.

In the height clock `u = log Y` and with `j = arsinh(X/Y)`, this is
`M · (Φ/Y)^{θ/2} · |Z|/Y`-free form of `M · e^{−θ I} · H(σ, ξ)`, where `M = Φ² |Z|/Y` is the
critical martingale of [AL14, Prop. 4] (the note's `𝓜 = Φ̂² cosh J`), `I = ∫ sech² J du` is the
occupation functional of (16), and `H(σ, x) = x σ^{−3/2} e^{−x²/(8σ)}` is the Dirichlet heat
kernel derivative, shifted by `c` in the variable `log cosh j`. Its Dynkin generator is
(`dynkinGen_superTest`)

`L superTest = (2Y²/N²) · E · [2 − 2r + (ξ/(2σ))(3 − r) − θξ]`, `r = ξ²/(4σ)`, `E > 0`,

which is `≤ 0` as soon as `ξ ≥ 4/θ` and `σ ≥ 3/θ` (`superBracket_nonpos`). The supersolution
inequality `E superTest(x_T) ≤ superTest(x_0)` at a deterministic time then gives
(`measure_deriv_revMap_tail_le`, the core estimate): with `Y* = √(y² + 4T)`, any `ℓ > 0` with
`log(Y*/a) ≤ 2ℓ`, `x_max = 4ℓ + ½ log(1 + m²/a²)`, `τ₀ = 3ℓ + x_max²`,

`P{a ≤ y |∂_z revMap V T (iy)|, |Re revMap V T (iy)| ≤ m} ≤ e^{9/8} (y/a)² ((τ₀ + 2ℓ)/(log(Y*/y) + τ₀))^{3/2}`.

On the event the state at time `T` has `Y ≥ a`, `Y ≤ Y*`, `|X| ≤ m`, so the test function is
`≥ (a/y)² e^{−9/8}` (with `θ = 1/ℓ`, `c = 4ℓ`, `τ₁ = log Y* + τ₀`), while at time `0` it is
`≤ ((τ₀ + 2ℓ)/(log(Y*/y) + τ₀))^{3/2}` after normalization. The constraint `|X_T| ≤ m` replaces
[AL14]'s endpoint analysis (Proposition 5): by Lemma 2.2 of the note, `|X_T| ≤ 2 sup |V|`, whose
tail is Gaussian (`measure_deriv_revMap_tail_le'`).

## Main results
* `superBracket_nonpos`, `dynkinGen_superTest`: the supersolution.
* `measure_deriv_revMap_tail_le`: the core estimate (any `T ≥ 0`, `y > 0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped ENNReal NNReal

namespace InteractingSLE.SLE8.AL14

open QuantumZipper

/-! ## The scalar inequality -/

/-- **The bracket of the generator is nonpositive.** If `θ > 0`, `ξ ≥ 4/θ` and `σ ≥ 3/θ`, then
`2 − 2r + (ξ/(2σ))(3 − r) − θξ ≤ 0` with `r = ξ²/(4σ)`. -/
theorem superBracket_nonpos {θ ξ σ : ℝ} (hθ : 0 < θ) (hξ : 4 / θ ≤ ξ) (hσ : 3 / θ ≤ σ) :
    2 - 2 * (ξ ^ 2 / (4 * σ)) + ξ / (2 * σ) * (3 - ξ ^ 2 / (4 * σ)) - θ * ξ ≤ 0 := by
  have hσ0 : 0 < σ := (div_pos (by norm_num) hθ).trans_le hσ
  have hξ0 : 0 < ξ := (div_pos (by norm_num) hθ).trans_le hξ
  have hr : 0 ≤ ξ ^ 2 / (4 * σ) := by positivity
  have h1 : ξ / (2 * σ) * (3 - ξ ^ 2 / (4 * σ)) ≤ 3 * ξ / (2 * σ) := by
    have : 0 ≤ ξ / (2 * σ) := by positivity
    have : ξ / (2 * σ) * (3 - ξ ^ 2 / (4 * σ)) ≤ ξ / (2 * σ) * 3 :=
      mul_le_mul_of_nonneg_left (by linarith) this
    calc _ ≤ ξ / (2 * σ) * 3 := this
      _ = 3 * ξ / (2 * σ) := by ring
  have h2 : 3 * ξ / (2 * σ) ≤ θ * ξ / 2 := by
    have h3 : 3 / σ ≤ θ := by
      rw [div_le_iff₀ hσ0]
      rw [div_le_iff₀ hθ] at hσ
      linarith
    calc 3 * ξ / (2 * σ) = (3 / σ) * ξ / 2 := by field_simp
      _ ≤ θ * ξ / 2 := by gcongr
  have h4 : 4 ≤ θ * ξ := by
    rw [div_le_iff₀ hθ] at hξ
    linarith
  linarith

/-! ## The test function -/

/-- The clock `σ = τ₁ − log Y` of the test function, at a state `x = (Z, L)`. -/
def superSigma (τ₁ : ℝ) (x : ℂ × ℝ) : ℝ := τ₁ - Real.log x.1.im

/-- The shifted angular variable `ξ = ½ log (X² + Y²) − log Y + c = log (|Z|/Y) + c`. -/
def superXi (c : ℝ) (x : ℂ × ℝ) : ℝ :=
  Real.log (x.1.re ^ 2 + x.1.im ^ 2) / 2 - Real.log x.1.im + c

/-- The supersolution `e^{(2 + θ/2) L} Y^{−θ/2} σ^{−3/2} ξ exp(ξ − ξ²/(8σ))`. -/
def superTest (θ c τ₁ : ℝ) (x : ℂ × ℝ) : ℝ :=
  Real.exp ((2 + θ / 2) * x.2) * x.1.im ^ (-(θ / 2)) * superSigma τ₁ x ^ (-(3 / 2 : ℝ)) *
    superXi c x * Real.exp (superXi c x - superXi c x ^ 2 / (8 * superSigma τ₁ x))

/-- The open set `{0 < Y < e^{τ₁}}` on which the test function is smooth (`σ > 0` there). -/
def superDom (τ₁ : ℝ) : Set (ℂ × ℝ) := {x | 0 < x.1.im ∧ x.1.im < Real.exp τ₁}

theorem isOpen_superDom (τ₁ : ℝ) : IsOpen (superDom τ₁) := by
  have him : Continuous fun x : ℂ × ℝ => x.1.im := Complex.continuous_im.comp continuous_fst
  exact (isOpen_lt continuous_const him).inter (isOpen_lt him continuous_const)

theorem superSigma_pos {τ₁ : ℝ} {x : ℂ × ℝ} (hx : x ∈ superDom τ₁) : 0 < superSigma τ₁ x := by
  have h := Real.log_lt_log hx.1 hx.2
  rw [Real.log_exp] at h
  simp only [superSigma]
  linarith

theorem superXi_ge {c : ℝ} {x : ℂ × ℝ} (hx : 0 < x.1.im) : c ≤ superXi c x := by
  have hN : x.1.im ^ 2 ≤ x.1.re ^ 2 + x.1.im ^ 2 := by nlinarith [sq_nonneg x.1.re]
  have h := Real.log_le_log (by positivity) hN
  rw [Real.log_pow] at h
  simp only [superXi]
  push_cast at h
  linarith

/-! ## Derivatives along lines -/

/-- The test function along a line `x + s v`, in real coordinates. -/
theorem superTest_line (θ c τ₁ : ℝ) (x v : ℂ × ℝ) (s : ℝ) :
    superTest θ c τ₁ (x + s • v) =
      Real.exp ((2 + θ / 2) * (x.2 + s * v.2)) * (x.1.im + s * v.1.im) ^ (-(θ / 2)) *
        (τ₁ - Real.log (x.1.im + s * v.1.im)) ^ (-(3 / 2 : ℝ)) *
        (Real.log ((x.1.re + s * v.1.re) ^ 2 + (x.1.im + s * v.1.im) ^ 2) / 2 -
          Real.log (x.1.im + s * v.1.im) + c) *
        Real.exp ((Real.log ((x.1.re + s * v.1.re) ^ 2 + (x.1.im + s * v.1.im) ^ 2) / 2 -
          Real.log (x.1.im + s * v.1.im) + c) -
          (Real.log ((x.1.re + s * v.1.re) ^ 2 + (x.1.im + s * v.1.im) ^ 2) / 2 -
            Real.log (x.1.im + s * v.1.im) + c) ^ 2 /
          (8 * (τ₁ - Real.log (x.1.im + s * v.1.im)))) := by
  simp only [superTest, superSigma, superXi, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]

/-- **Product rule for the test-function shape.** For `f(s) = e^{α ℓ(s)} y(s)^{−θ/2}
σ(s)^{−3/2} ξ(s) exp(ξ(s) − ξ(s)²/(8σ(s)))` with `y(0), σ(0) > 0`. -/
theorem hasDerivAt_superProd {α θ : ℝ} {ℓ y σ ξ : ℝ → ℝ} {ℓ' y' σ' ξ' : ℝ}
    (hℓ : HasDerivAt ℓ ℓ' 0) (hy : HasDerivAt y y' 0) (hσ : HasDerivAt σ σ' 0)
    (hξ : HasDerivAt ξ ξ' 0) (hy0 : 0 < y 0) (hσ0 : 0 < σ 0) :
    HasDerivAt (fun s => Real.exp (α * ℓ s) * y s ^ (-(θ / 2)) * σ s ^ (-(3 / 2 : ℝ)) * ξ s *
        Real.exp (ξ s - ξ s ^ 2 / (8 * σ s)))
      (Real.exp (α * ℓ 0) * y 0 ^ (-(θ / 2)) * σ 0 ^ (-(3 / 2 : ℝ)) *
        Real.exp (ξ 0 - ξ 0 ^ 2 / (8 * σ 0)) *
        (ξ 0 * (α * ℓ' - θ / 2 * (y' / y 0) - 3 / 2 * (σ' / σ 0)) + ξ' +
          ξ 0 * (ξ' - ξ 0 * ξ' / (4 * σ 0) + ξ 0 ^ 2 * σ' / (8 * σ 0 ^ 2)))) 0 := by
  have h1 := (hℓ.const_mul α).exp
  have h2 := hy.rpow_const (p := -(θ / 2)) (Or.inl hy0.ne')
  have h3 := hσ.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hσ0.ne')
  have h8 : 8 * σ 0 ≠ 0 := by positivity
  have h5 := (hξ.fun_sub ((hξ.fun_pow 2).fun_div (hσ.const_mul 8) h8)).exp
  refine ((((h1.fun_mul h2).fun_mul h3).fun_mul hξ).fun_mul h5).congr_deriv ?_
  -- the derivative of the product
  rw [Real.rpow_sub_one hy0.ne', Real.rpow_sub_one hσ0.ne']
  field_simp
  ring

/-! ## The profile along the noise direction -/

/-- The profile `ψ(ξ) = K ξ exp(ξ − ξ²/(8σ))` of the test function in the noise direction. -/
def superPsi (K σ : ℝ) (ξ : ℝ) : ℝ := K * ξ * Real.exp (ξ - ξ ^ 2 / (8 * σ))

theorem hasDerivAt_superPsi (K σ ξ : ℝ) (hσ : σ ≠ 0) :
    HasDerivAt (superPsi K σ) (K * Real.exp (ξ - ξ ^ 2 / (8 * σ)) *
      (1 + ξ * (1 - ξ / (4 * σ)))) ξ := by
  have hq : HasDerivAt (fun t : ℝ => t - t ^ 2 / (8 * σ)) (1 - ξ / (4 * σ)) ξ := by
    have := (hasDerivAt_id' ξ).fun_sub ((hasDerivAt_pow 2 ξ).div_const (8 * σ))
    refine this.congr_deriv ?_
    field_simp
    ring
  refine (((hasDerivAt_id' ξ).const_mul K).fun_mul hq.exp).congr_deriv ?_
  ring

theorem deriv_superPsi (K σ : ℝ) (hσ : σ ≠ 0) :
    deriv (superPsi K σ) = fun ξ => K * Real.exp (ξ - ξ ^ 2 / (8 * σ)) *
      (1 + ξ * (1 - ξ / (4 * σ))) :=
  funext fun ξ => (hasDerivAt_superPsi K σ ξ hσ).deriv

theorem deriv_deriv_superPsi (K σ ξ : ℝ) (hσ : σ ≠ 0) :
    deriv (deriv (superPsi K σ)) ξ = K * Real.exp (ξ - ξ ^ 2 / (8 * σ)) *
      ((1 - ξ / (4 * σ)) * (1 + ξ * (1 - ξ / (4 * σ))) + (1 - ξ / (2 * σ))) := by
  rw [deriv_superPsi K σ hσ]
  have hq : HasDerivAt (fun t : ℝ => t - t ^ 2 / (8 * σ)) (1 - ξ / (4 * σ)) ξ := by
    have := (hasDerivAt_id' ξ).fun_sub ((hasDerivAt_pow 2 ξ).div_const (8 * σ))
    refine this.congr_deriv ?_
    field_simp
    ring
  have hr : HasDerivAt (fun t : ℝ => 1 + t * (1 - t / (4 * σ))) (1 - ξ / (2 * σ)) ξ := by
    have := ((hasDerivAt_id' ξ).fun_mul (((hasDerivAt_id' ξ).div_const (4 * σ)).const_sub 1)).const_add 1
    refine this.congr_deriv ?_
    field_simp
    ring
  exact ((hq.exp.const_mul K).fun_mul hr).deriv.trans (by ring)

theorem contDiff_superPsi (K σ : ℝ) : ContDiff ℝ 2 (superPsi K σ) := by
  unfold superPsi
  exact (contDiff_const.mul contDiff_id).mul
    (Real.contDiff_exp.comp (contDiff_id.sub ((contDiff_id.pow 2).div_const _)))

/-- The angular variable along a horizontal line: `h(s) = ½ log((X + s a)² + Y²) − log Y + c`. -/
def noiseXi (X Y a c : ℝ) (s : ℝ) : ℝ :=
  Real.log ((X + s * a) ^ 2 + Y ^ 2) / 2 - Real.log Y + c

theorem hasDerivAt_noiseXi (X Y a c s : ℝ) (hY : 0 < Y) :
    HasDerivAt (noiseXi X Y a c) ((X + s * a) * a / ((X + s * a) ^ 2 + Y ^ 2)) s := by
  have hN : 0 < (X + s * a) ^ 2 + Y ^ 2 := by positivity
  have hl : HasDerivAt (fun t : ℝ => X + t * a) a s := by
    simpa using ((hasDerivAt_id' s).mul_const a).const_add X
  have := ((((hl.fun_pow 2).add_const (Y ^ 2)).log hN.ne').div_const 2).sub_const
    (Real.log Y) |>.add_const c
  refine this.congr_deriv ?_
  field_simp
  ring

theorem contDiffAt_noiseXi (X Y a c : ℝ) (hY : 0 < Y) : ContDiffAt ℝ 2 (noiseXi X Y a c) 0 := by
  unfold noiseXi
  have hN : ((X + 0 * a) ^ 2 + Y ^ 2) ≠ 0 := by positivity
  exact ((((contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)).pow 2).add
    contDiffAt_const).log hN |>.div_const 2 |>.sub contDiffAt_const).add contDiffAt_const

theorem deriv_noiseXi_zero (X Y a c : ℝ) (hY : 0 < Y) :
    deriv (noiseXi X Y a c) 0 = X * a / (X ^ 2 + Y ^ 2) := by
  rw [(hasDerivAt_noiseXi X Y a c 0 hY).deriv]
  simp

theorem deriv_deriv_noiseXi_zero (X Y a c : ℝ) (hY : 0 < Y) :
    deriv (deriv (noiseXi X Y a c)) 0 = a ^ 2 * (Y ^ 2 - X ^ 2) / (X ^ 2 + Y ^ 2) ^ 2 := by
  have hd : deriv (noiseXi X Y a c) = fun s => (X + s * a) * a / ((X + s * a) ^ 2 + Y ^ 2) :=
    funext fun s => (hasDerivAt_noiseXi X Y a c s hY).deriv
  rw [hd]
  have hN : (X + 0 * a) ^ 2 + Y ^ 2 ≠ 0 := by positivity
  have hl : HasDerivAt (fun t : ℝ => X + t * a) a 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add X
  have := (hl.mul_const a).fun_div ((hl.fun_pow 2).add_const (Y ^ 2)) hN
  rw [this.deriv]
  have hN0 : X ^ 2 + Y ^ 2 ≠ 0 := by positivity
  simp only [zero_mul, add_zero, Nat.cast_ofNat]
  field_simp
  ring

/-! ## Smoothness and the generator -/

theorem contDiffOn_superTest (θ c τ₁ : ℝ) :
    ContDiffOn ℝ 3 (superTest θ c τ₁) (superDom τ₁) := by
  have him : ContDiff ℝ 3 (fun x : ℂ × ℝ => x.1.im) :=
    Complex.imCLM.contDiff.comp (contDiff_fst (𝕜 := ℝ) (E := ℂ) (F := ℝ) (n := 3))
  have hre : ContDiff ℝ 3 (fun x : ℂ × ℝ => x.1.re) :=
    Complex.reCLM.contDiff.comp (contDiff_fst (𝕜 := ℝ) (E := ℂ) (F := ℝ) (n := 3))
  have hN : ContDiff ℝ 3 (fun x : ℂ × ℝ => x.1.re ^ 2 + x.1.im ^ 2) := (hre.pow 2).add (him.pow 2)
  have hlogY : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => Real.log x.1.im) (superDom τ₁) :=
    him.contDiffOn.log fun x hx => hx.1.ne'
  have hlogN : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => Real.log (x.1.re ^ 2 + x.1.im ^ 2))
      (superDom τ₁) :=
    hN.contDiffOn.log fun x hx => by have := hx.1; positivity
  have hσ : ContDiffOn ℝ 3 (superSigma τ₁) (superDom τ₁) := contDiffOn_const.sub hlogY
  have hξ : ContDiffOn ℝ 3 (superXi c) (superDom τ₁) :=
    ((hlogN.div_const 2).sub hlogY).add contDiffOn_const
  have h1 : ContDiff ℝ 3 (fun x : ℂ × ℝ => Real.exp ((2 + θ / 2) * x.2)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)
  have h2 : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => x.1.im ^ (-(θ / 2))) (superDom τ₁) :=
    him.contDiffOn.rpow_const_of_ne fun x hx => hx.1.ne'
  have h3 : ContDiffOn ℝ 3 (fun x => superSigma τ₁ x ^ (-(3 / 2 : ℝ))) (superDom τ₁) :=
    hσ.rpow_const_of_ne fun x hx => (superSigma_pos hx).ne'
  have h5 : ContDiffOn ℝ 3
      (fun x => Real.exp (superXi c x - superXi c x ^ 2 / (8 * superSigma τ₁ x))) (superDom τ₁) :=
    Real.contDiff_exp.comp_contDiffOn (hξ.sub ((hξ.pow 2).div (contDiffOn_const.mul hσ)
      fun x hx => by have := superSigma_pos hx; positivity))
  exact (((h1.contDiffOn.mul h2).mul h3).mul hξ).mul h5

theorem mem_superDom {τ₁ : ℝ} {x : ℂ × ℝ} (hx : 0 < x.1.im) (hσ : 0 < superSigma τ₁ x) :
    x ∈ superDom τ₁ := by
  refine ⟨hx, ?_⟩
  have h : Real.log x.1.im < τ₁ := by simp only [superSigma] at hσ; linarith
  calc x.1.im = Real.exp (Real.log x.1.im) := (Real.exp_log hx).symm
    _ < Real.exp τ₁ := Real.exp_lt_exp.2 h

/-- **The Dynkin generator of the test function** (where the taming of the drift is inactive):
`(2Y²/N²) · E · [2 − 2r + (ξ/(2σ))(3 − r) − θξ]`, `r = ξ²/(4σ)`,
`E = e^{(2+θ/2)L} Y^{−θ/2} σ^{−3/2} exp(ξ − ξ²/(8σ))`. -/
theorem dynkinGen_superTest {θ c τ₁ y₀ : ℝ} {x : ℂ × ℝ} (hx : 0 < x.1.im) (hy : y₀ ≤ x.1.im)
    (hσ : 0 < superSigma τ₁ x) :
    dynkinGen (RS.rsDrift y₀) (RS.rsNoise 8) (superTest θ c τ₁) x =
      2 * x.1.im ^ 2 / (x.1.re ^ 2 + x.1.im ^ 2) ^ 2 *
        (Real.exp ((2 + θ / 2) * x.2) * x.1.im ^ (-(θ / 2)) * superSigma τ₁ x ^ (-(3 / 2 : ℝ)) *
          Real.exp (superXi c x - superXi c x ^ 2 / (8 * superSigma τ₁ x))) *
        (2 - 2 * (superXi c x ^ 2 / (4 * superSigma τ₁ x)) +
          superXi c x / (2 * superSigma τ₁ x) * (3 - superXi c x ^ 2 / (4 * superSigma τ₁ x)) -
          θ * superXi c x) := by
  have hdom := mem_superDom hx hσ
  have hF : ContDiffAt ℝ 3 (superTest θ c τ₁) x :=
    (contDiffOn_superTest θ c τ₁).contDiffAt ((isOpen_superDom τ₁).mem_nhds hdom)
  unfold dynkinGen
  rw [FrozenMart.fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    FrozenMart.iteratedFDeriv_two_eq_deriv_deriv_line (hF.of_le (by norm_num))]
  set v := RS.rsDrift y₀ x with hv
  -- the drift direction
  have hℓ : HasDerivAt (fun s : ℝ => x.2 + s * v.2) v.2 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const v.2).const_add x.2
  have hyl : HasDerivAt (fun s : ℝ => x.1.im + s * v.1.im) v.1.im 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const v.1.im).const_add x.1.im
  have hxl : HasDerivAt (fun s : ℝ => x.1.re + s * v.1.re) v.1.re 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const v.1.re).const_add x.1.re
  have hY0 : (x.1.im + 0 * v.1.im) ≠ 0 := by simpa using hx.ne'
  have hN0 : 0 < x.1.re ^ 2 + x.1.im ^ 2 := by positivity
  have hlogY := hyl.log hY0
  have hlogN := ((hxl.fun_pow 2).fun_add (hyl.fun_pow 2)).log (by simpa using hN0.ne')
  have hσl := hlogY.const_sub τ₁
  have hξl := ((hlogN.div_const 2).fun_sub hlogY).add_const c
  have hD := hasDerivAt_superProd (α := 2 + θ / 2) (θ := θ) hℓ hyl hσl hξl
    (by simpa using hx) (by simpa [superSigma] using hσ)
  have hD' : HasDerivAt (fun s : ℝ => superTest θ c τ₁ (x + s • v)) _ 0 :=
    hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => superTest_line θ c τ₁ x v s)
  rw [hD'.deriv]
  -- the noise direction
  set σ₀ := superSigma τ₁ x with hσ₀
  set K := Real.exp ((2 + θ / 2) * x.2) * x.1.im ^ (-(θ / 2)) * σ₀ ^ (-(3 / 2 : ℝ)) with hK
  have e2 : (fun s : ℝ => superTest θ c τ₁ (x + s • RS.rsNoise 8)) =
      fun s => superPsi K σ₀ (noiseXi x.1.re x.1.im (-Real.sqrt 8) c s) := by
    funext s
    rw [superTest_line]
    simp only [RS.rsNoise, superPsi, noiseXi, hK, hσ₀, superSigma, Complex.neg_re,
      Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero, mul_zero, add_zero]
  have hσne : σ₀ ≠ 0 := hσ.ne'
  rw [e2, RS.deriv_deriv_comp_zero ((contDiff_superPsi K σ₀).contDiffAt)
    (contDiffAt_noiseXi _ _ _ c hx), deriv_deriv_superPsi K σ₀ _ hσne,
    deriv_superPsi K σ₀ hσne, deriv_noiseXi_zero _ _ _ c hx,
    deriv_deriv_noiseXi_zero _ _ _ c hx]
  -- algebra
  have h8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  simp only [hv, RS.rsDrift, FwdHolo.proj_of_le hy]
  rw [RS.re_two_div_sq]
  simp only [Complex.neg_re, Complex.neg_im, RS.re_two_div, RS.im_two_div, zero_mul, add_zero,
    noiseXi, hK]
  simp only [superXi, superSigma] at hσ₀ ⊢
  rw [← hσ₀]
  generalize Real.log (x.1.re ^ 2 + x.1.im ^ 2) / 2 - Real.log x.1.im + c = ξ
  generalize Real.exp ((2 + θ / 2) * x.2) = E1
  generalize x.1.im ^ (-(θ / 2)) = E2
  generalize σ₀ ^ (-(3 / 2 : ℝ)) = E3
  generalize Real.exp (ξ - ξ ^ 2 / (8 * σ₀)) = E4
  field_simp
  ring_nf
  rw [h8]
  ring

/-- **The test function is a supersolution** where `ξ ≥ 4/θ` (guaranteed by `c ≥ 4/θ`) and
`σ ≥ 3/θ`. -/
theorem dynkinGen_superTest_nonpos {θ c τ₁ y₀ : ℝ} {x : ℂ × ℝ} (hθ : 0 < θ) (hc : 4 / θ ≤ c)
    (hx : 0 < x.1.im) (hy : y₀ ≤ x.1.im) (hσ : 3 / θ ≤ superSigma τ₁ x) :
    dynkinGen (RS.rsDrift y₀) (RS.rsNoise 8) (superTest θ c τ₁) x ≤ 0 := by
  have hσ0 : 0 < superSigma τ₁ x := (div_pos (by norm_num) hθ).trans_le hσ
  rw [dynkinGen_superTest hx hy hσ0]
  have hbr := superBracket_nonpos hθ (hc.trans (superXi_ge hx)) hσ
  have h1 : 0 ≤ 2 * x.1.im ^ 2 / (x.1.re ^ 2 + x.1.im ^ 2) ^ 2 := by positivity
  have h2 : 0 ≤ Real.exp ((2 + θ / 2) * x.2) * x.1.im ^ (-(θ / 2)) *
      superSigma τ₁ x ^ (-(3 / 2 : ℝ)) *
      Real.exp (superXi c x - superXi c x ^ 2 / (8 * superSigma τ₁ x)) := by
    have := Real.rpow_nonneg hx.le (-(θ / 2))
    have := Real.rpow_nonneg hσ0.le (-(3 / 2 : ℝ))
    positivity
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg h1 h2) hbr

theorem measurable_superTest (θ c τ₁ : ℝ) : Measurable (superTest θ c τ₁) := by
  unfold superTest superSigma superXi
  fun_prop

theorem superTest_nonneg {θ c τ₁ : ℝ} {x : ℂ × ℝ} (hx : 0 < x.1.im) (hc : 0 ≤ c)
    (hσ : 0 < superSigma τ₁ x) : 0 ≤ superTest θ c τ₁ x := by
  unfold superTest
  have := Real.rpow_nonneg hx.le (-(θ / 2))
  have := Real.rpow_nonneg hσ.le (-(3 / 2 : ℝ))
  have := hc.trans (superXi_ge (c := c) hx)
  positivity

/-- `ξ e^{ξ − ξ²/(8σ)} ≤ e^{8σ}` for `σ > 0`. -/
theorem mul_exp_le_exp_eight_mul {ξ σ : ℝ} (hσ : 0 < σ) :
    ξ * Real.exp (ξ - ξ ^ 2 / (8 * σ)) ≤ Real.exp (8 * σ) := by
  have h1 : ξ ≤ Real.exp ξ := by linarith [Real.add_one_le_exp ξ]
  have h2 : ξ + (ξ - ξ ^ 2 / (8 * σ)) ≤ 8 * σ := by
    have : 0 ≤ (ξ - 8 * σ) ^ 2 / (8 * σ) := by positivity
    have e : (ξ - 8 * σ) ^ 2 / (8 * σ) = 8 * σ - 2 * ξ + ξ ^ 2 / (8 * σ) := by
      field_simp; ring
    linarith
  calc ξ * Real.exp (ξ - ξ ^ 2 / (8 * σ)) ≤ Real.exp ξ * Real.exp (ξ - ξ ^ 2 / (8 * σ)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (ξ + (ξ - ξ ^ 2 / (8 * σ))) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (8 * σ) := Real.exp_le_exp.2 h2

/-- An upper bound for the test function on the region visited by the flow. -/
theorem superTest_le {θ c τ₁ y Λ τ₀ : ℝ} {x : ℂ × ℝ} (hθ : 0 < θ) (hc : 0 ≤ c) (hy : 0 < y)
    (hτ₀ : 0 < τ₀) (hxy : y ≤ x.1.im) (hσ : τ₀ ≤ superSigma τ₁ x)
    (hL : x.2 ≤ Λ) :
    superTest θ c τ₁ x ≤ Real.exp ((2 + θ / 2) * Λ) * y ^ (-(θ / 2)) * τ₀ ^ (-(3 / 2 : ℝ)) *
      Real.exp (8 * (τ₁ - Real.log y)) := by
  have hx : 0 < x.1.im := hy.trans_le hxy
  have hσ0 : 0 < superSigma τ₁ x := hτ₀.trans_le hσ
  have hξ := hc.trans (superXi_ge (c := c) hx)
  unfold superTest
  have e1 : Real.exp ((2 + θ / 2) * x.2) ≤ Real.exp ((2 + θ / 2) * Λ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hL (by positivity))
  have e2 : x.1.im ^ (-(θ / 2)) ≤ y ^ (-(θ / 2)) :=
    Real.rpow_le_rpow_of_nonpos hy hxy (by linarith)
  have e3 : superSigma τ₁ x ^ (-(3 / 2 : ℝ)) ≤ τ₀ ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hτ₀ hσ (by norm_num)
  have e4 : superXi c x * Real.exp (superXi c x - superXi c x ^ 2 / (8 * superSigma τ₁ x)) ≤
      Real.exp (8 * (τ₁ - Real.log y)) := by
    refine (mul_exp_le_exp_eight_mul hσ0).trans (Real.exp_le_exp.2 ?_)
    have : Real.log y ≤ Real.log x.1.im := Real.log_le_log hy hxy
    simp only [superSigma]
    linarith
  have p2 := Real.rpow_nonneg hx.le (-(θ / 2))
  have p3 := Real.rpow_nonneg hσ0.le (-(3 / 2 : ℝ))
  calc Real.exp ((2 + θ / 2) * x.2) * x.1.im ^ (-(θ / 2)) * superSigma τ₁ x ^ (-(3 / 2 : ℝ)) *
        superXi c x * Real.exp (superXi c x - superXi c x ^ 2 / (8 * superSigma τ₁ x))
      = Real.exp ((2 + θ / 2) * x.2) * x.1.im ^ (-(θ / 2)) * superSigma τ₁ x ^ (-(3 / 2 : ℝ)) *
        (superXi c x * Real.exp (superXi c x - superXi c x ^ 2 / (8 * superSigma τ₁ x))) := by
        ring
    _ ≤ Real.exp ((2 + θ / 2) * Λ) * y ^ (-(θ / 2)) * τ₀ ^ (-(3 / 2 : ℝ)) *
        Real.exp (8 * (τ₁ - Real.log y)) := by
        have q1 : 0 ≤ Real.exp ((2 + θ / 2) * x.2) := (Real.exp_pos _).le
        have q4 : 0 ≤ superXi c x * Real.exp (superXi c x - superXi c x ^ 2 /
            (8 * superSigma τ₁ x)) := mul_nonneg hξ (Real.exp_pos _).le
        gcongr

/-! ## The parameters of the core estimate and the two evaluations of the test function -/

/-- `x_max = 4ℓ + ½ log(1 + m²/a²)`: the largest value of `ξ` on the event. -/
def coreXmax (ℓ a m : ℝ) : ℝ := 4 * ℓ + Real.log (1 + m ^ 2 / a ^ 2) / 2

/-- `τ₀ = 3ℓ + x_max²`: the offset of the clock `σ`. -/
def coreTau (ℓ a m : ℝ) : ℝ := 3 * ℓ + coreXmax ℓ a m ^ 2

/-- The bound of the core estimate: `e^{9/8} (y/a)² ((τ₀ + 2ℓ)/(log(Y*/y) + τ₀))^{3/2}`. -/
def coreBound (y a m ℓ Ys : ℝ) : ℝ :=
  Real.exp (9 / 8) * (y / a) ^ 2 *
    ((coreTau ℓ a m + 2 * ℓ) / (Real.log (Ys / y) + coreTau ℓ a m)) ^ (3 / 2 : ℝ)

theorem coreXmax_pos {ℓ a m : ℝ} (hℓ : 0 < ℓ) : 0 < coreXmax ℓ a m := by
  have : 0 ≤ Real.log (1 + m ^ 2 / a ^ 2) :=
    Real.log_nonneg (by have := div_nonneg (sq_nonneg m) (sq_nonneg a); linarith)
  unfold coreXmax
  linarith

theorem coreTau_pos {ℓ a m : ℝ} (hℓ : 0 < ℓ) : 0 < coreTau ℓ a m := by
  unfold coreTau
  have := sq_nonneg (coreXmax ℓ a m)
  linarith

theorem coreBound_nonneg (y a m ℓ Ys : ℝ) (hℓ : 0 < ℓ) (hyY : 0 ≤ Real.log (Ys / y)) :
    0 ≤ coreBound y a m ℓ Ys := by
  unfold coreBound
  have := coreTau_pos (a := a) (m := m) hℓ
  have : 0 ≤ (coreTau ℓ a m + 2 * ℓ) / (Real.log (Ys / y) + coreTau ℓ a m) := by positivity
  have := Real.rpow_nonneg this (3 / 2 : ℝ)
  positivity

/-- The lower bound `κ` of the test function on the event. -/
def coreKappa (y a m ℓ : ℝ) : ℝ :=
  (a / y) ^ 2 * y ^ (-(1 / ℓ / 2)) * Real.exp (-1) * (coreTau ℓ a m + 2 * ℓ) ^ (-(3 / 2 : ℝ)) *
    (4 * ℓ) * Real.exp (4 * ℓ) * Real.exp (-(1 / 8))

theorem coreKappa_pos {y a m ℓ : ℝ} (hy : 0 < y) (ha : 0 < a) (hℓ : 0 < ℓ) :
    0 < coreKappa y a m ℓ := by
  unfold coreKappa
  have := coreTau_pos (a := a) (m := m) hℓ
  have := Real.rpow_pos_of_pos hy (-(1 / ℓ / 2))
  have := Real.rpow_pos_of_pos (by positivity : 0 < coreTau ℓ a m + 2 * ℓ) (-(3 / 2 : ℝ))
  positivity

/-- **The test function is large on the event.** -/
theorem coreKappa_le_superTest {ℓ a y m Ys : ℝ} {x : ℂ × ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (hy : 0 < y) (hYa : Real.log (Ys / a) ≤ 2 * ℓ) (hL : Real.log (a / y) ≤ x.2)
    (hax : a ≤ x.1.im) (hxY : x.1.im ≤ Ys) (hm : |x.1.re| ≤ m) :
    coreKappa y a m ℓ ≤ superTest (1 / ℓ) (4 * ℓ) (Real.log Ys + coreTau ℓ a m) x := by
  set θ := 1 / ℓ with hθ
  set τ₀ := coreTau ℓ a m with hτ₀
  have hθ0 : 0 < θ := by positivity
  have hθℓ : θ * ℓ = 1 := by rw [hθ]; field_simp
  have hx : 0 < x.1.im := ha.trans_le hax
  have hYs : 0 < Ys := hx.trans_le hxY
  have hτ0 : 0 < τ₀ := coreTau_pos hℓ
  have hlogYa : Real.log Ys - Real.log a ≤ 2 * ℓ := by
    rwa [Real.log_div hYs.ne' ha.ne'] at hYa
  -- (i) the derivative and height factors
  have i1 : (a / y) ^ 2 * y ^ (-(θ / 2)) * Real.exp (-1) ≤
      Real.exp ((2 + θ / 2) * x.2) * x.1.im ^ (-(θ / 2)) := by
    rw [Real.rpow_def_of_pos hy, Real.rpow_def_of_pos hx,
      show (a / y) ^ 2 = Real.exp (2 * Real.log (a / y)) by
        rw [← Real.log_rpow (by positivity), Real.exp_log (by positivity)]; norm_cast,
      ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    rw [Real.log_div ha.ne' hy.ne'] at hL ⊢
    have h1 : Real.log x.1.im ≤ Real.log Ys := Real.log_le_log hx hxY
    have h2 : (2 + θ / 2) * (Real.log a - Real.log y) ≤ (2 + θ / 2) * x.2 :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    have h3 : θ / 2 * (Real.log Ys - Real.log a) ≤ 1 := by
      calc θ / 2 * (Real.log Ys - Real.log a) ≤ θ / 2 * (2 * ℓ) :=
            mul_le_mul_of_nonneg_left hlogYa (by positivity)
        _ = 1 := by rw [← hθℓ]; ring
    have h4 : θ / 2 * Real.log x.1.im ≤ θ / 2 * Real.log Ys :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith
  -- (ii) the clock
  have hσlo : τ₀ ≤ superSigma (Real.log Ys + τ₀) x := by
    have := Real.log_le_log hx hxY
    simp only [superSigma]
    linarith
  have hσhi : superSigma (Real.log Ys + τ₀) x ≤ τ₀ + 2 * ℓ := by
    have := Real.log_le_log ha hax
    simp only [superSigma]
    linarith
  have hσ0 : 0 < superSigma (Real.log Ys + τ₀) x := hτ0.trans_le hσlo
  have i2 : (τ₀ + 2 * ℓ) ^ (-(3 / 2 : ℝ)) ≤ superSigma (Real.log Ys + τ₀) x ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hσ0 hσhi (by norm_num)
  -- (iii) the angular variable
  have hξlo : 4 * ℓ ≤ superXi (4 * ℓ) x := superXi_ge hx
  have hξhi : superXi (4 * ℓ) x ≤ coreXmax ℓ a m := by
    have hN : 0 < x.1.re ^ 2 + x.1.im ^ 2 := by positivity
    have hq : (x.1.re ^ 2 + x.1.im ^ 2) / x.1.im ^ 2 ≤ 1 + m ^ 2 / a ^ 2 := by
      rw [add_div, div_self (by positivity), add_comm (x.1.re ^ 2 / x.1.im ^ 2)]
      have hre : x.1.re ^ 2 ≤ m ^ 2 := by
        have := sq_abs x.1.re
        nlinarith [abs_nonneg x.1.re]
      have : x.1.re ^ 2 / x.1.im ^ 2 ≤ m ^ 2 / a ^ 2 := by
        calc x.1.re ^ 2 / x.1.im ^ 2 ≤ m ^ 2 / x.1.im ^ 2 := by gcongr
          _ ≤ m ^ 2 / a ^ 2 := by gcongr
      linarith
    have hl := Real.log_le_log (by positivity) hq
    rw [Real.log_div hN.ne' (by positivity), Real.log_pow] at hl
    simp only [superXi, coreXmax]
    push_cast at hl
    linarith
  -- (iv) the Gaussian factor
  have i4 : Real.exp (4 * ℓ) * Real.exp (-(1 / 8)) ≤ Real.exp (superXi (4 * ℓ) x -
      superXi (4 * ℓ) x ^ 2 / (8 * superSigma (Real.log Ys + τ₀) x)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hxm := coreXmax_pos (a := a) (m := m) hℓ
    have hsq : superXi (4 * ℓ) x ^ 2 ≤ coreXmax ℓ a m ^ 2 := by
      have : 0 ≤ superXi (4 * ℓ) x := by linarith
      nlinarith
    have : superXi (4 * ℓ) x ^ 2 / (8 * superSigma (Real.log Ys + τ₀) x) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      have : coreXmax ℓ a m ^ 2 ≤ τ₀ := by
        simp only [hτ₀, coreTau]; linarith
      nlinarith
    linarith
  -- assemble
  have p1 : 0 ≤ (a / y) ^ 2 * y ^ (-(θ / 2)) * Real.exp (-1) := by
    have := Real.rpow_nonneg hy.le (-(θ / 2)); positivity
  have p2 : 0 ≤ (τ₀ + 2 * ℓ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  unfold coreKappa superTest
  rw [← hθ, ← hτ₀]
  calc (a / y) ^ 2 * y ^ (-(θ / 2)) * Real.exp (-1) * (τ₀ + 2 * ℓ) ^ (-(3 / 2 : ℝ)) * (4 * ℓ) *
        Real.exp (4 * ℓ) * Real.exp (-(1 / 8))
      = ((a / y) ^ 2 * y ^ (-(θ / 2)) * Real.exp (-1)) * (τ₀ + 2 * ℓ) ^ (-(3 / 2 : ℝ)) *
        (4 * ℓ) * (Real.exp (4 * ℓ) * Real.exp (-(1 / 8))) := by ring
    _ ≤ (Real.exp ((2 + θ / 2) * x.2) * x.1.im ^ (-(θ / 2))) *
        superSigma (Real.log Ys + τ₀) x ^ (-(3 / 2 : ℝ)) * superXi (4 * ℓ) x *
        Real.exp (superXi (4 * ℓ) x - superXi (4 * ℓ) x ^ 2 /
          (8 * superSigma (Real.log Ys + τ₀) x)) := by
        gcongr
        exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hx.le _))
          (Real.rpow_nonneg hσ0.le _)) (by linarith)

/-- The test function at the starting state `(iy, 0)`. -/
theorem superTest_start_le {θ c τ₁ y : ℝ} (hy : 0 < y) (hc : 0 ≤ c) (hσ : 0 < τ₁ - Real.log y) :
    superTest θ c τ₁ ((y : ℂ) * I, 0) ≤
      y ^ (-(θ / 2)) * (τ₁ - Real.log y) ^ (-(3 / 2 : ℝ)) * c * Real.exp c := by
  have hre : ((y : ℂ) * I).re = 0 := by simp
  have him : ((y : ℂ) * I).im = y := by simp
  have hξ : superXi c ((y : ℂ) * I, (0 : ℝ)) = c := by
    simp only [superXi, hre, him]
    rw [show (0 : ℝ) ^ 2 + y ^ 2 = y ^ 2 by ring, Real.log_pow]
    push_cast
    ring
  unfold superTest
  rw [hξ]
  simp only [superSigma, him, mul_zero, Real.exp_zero, one_mul]
  have h1 : Real.exp (c - c ^ 2 / (8 * (τ₁ - Real.log y))) ≤ Real.exp c :=
    Real.exp_le_exp.2 (by have : 0 ≤ c ^ 2 / (8 * (τ₁ - Real.log y)) := by positivity
                          linarith)
  have p1 := Real.rpow_nonneg hy.le (-(θ / 2))
  have p2 := Real.rpow_nonneg hσ.le (-(3 / 2 : ℝ))
  gcongr

/-- **The two evaluations match the bound:** `coreBound · κ` is the upper bound of the test
function at the start (with `θ = 1/ℓ`, `c = 4ℓ`, `τ₁ = log Y* + τ₀`). -/
theorem coreBound_mul_coreKappa {y a m ℓ Ys : ℝ} (hy : 0 < y) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hYs : 0 < Ys) (hyY : 0 ≤ Real.log (Ys / y)) :
    coreBound y a m ℓ Ys * coreKappa y a m ℓ =
      y ^ (-(1 / ℓ / 2)) * (Real.log Ys + coreTau ℓ a m - Real.log y) ^ (-(3 / 2 : ℝ)) *
        (4 * ℓ) * Real.exp (4 * ℓ) := by
  have hτ := coreTau_pos (a := a) (m := m) hℓ
  have hD : 0 < Real.log (Ys / y) + coreTau ℓ a m := by linarith
  have hA : 0 < coreTau ℓ a m + 2 * ℓ := by linarith
  have eD : Real.log Ys + coreTau ℓ a m - Real.log y = Real.log (Ys / y) + coreTau ℓ a m := by
    rw [Real.log_div hYs.ne' hy.ne']; ring
  rw [eD]
  unfold coreBound coreKappa
  rw [Real.div_rpow hA.le hD.le, Real.rpow_neg hA.le, Real.rpow_neg hD.le]
  have e1 : Real.exp (9 / 8) * Real.exp (-1) * Real.exp (-(1 / 8)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have hA' : 0 < (coreTau ℓ a m + 2 * ℓ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hA _
  have hD' : 0 < (Real.log (Ys / y) + coreTau ℓ a m) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hD _
  field_simp
  linear_combination e1

/-! ## The core estimate -/

section Core

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The pathwise facts used on the region: for a continuous driver and `0 ≤ t ≤ T`, the
reverse flow from `iy` has `y ≤ Y_t ≤ √(y² + 4T)` and `log Φ_t ≤ log(√(y² + 4T)/y)`. -/
theorem revMap_region {V : ℝ → ℝ} (hV : Continuous V) {y t T : ℝ} (hy : 0 < y) (ht : 0 ≤ t)
    (htT : t ≤ T) :
    y ≤ (revMap V t ((y : ℂ) * I)).im ∧
      (revMap V t ((y : ℂ) * I)).im ≤ Real.sqrt (y ^ 2 + 4 * T) ∧
      y * ‖deriv (revMap V t) ((y : ℂ) * I)‖ ≤ (revMap V t ((y : ℂ) * I)).im ∧
      Real.log ‖deriv (revMap V t) ((y : ℂ) * I)‖ ≤ Real.log (Real.sqrt (y ^ 2 + 4 * T) / y) := by
  have hz : ((y : ℂ) * I) ∈ H := by show 0 < ((y : ℂ) * I).im; simpa using hy
  have hzim : ((y : ℂ) * I).im = y := by simp
  obtain ⟨h1, h2, h3, -⟩ := revFlow_bounds hV hz ht
  rw [hzim] at h1 h2 h3
  rw [deriv_revFlow] at h3
  have hYt : (revMap V t ((y : ℂ) * I)).im ≤ Real.sqrt (y ^ 2 + 4 * T) :=
    h2.trans (Real.sqrt_le_sqrt (by linarith))
  have hΦ : y * ‖deriv (revMap V t) ((y : ℂ) * I)‖ ≤ (revMap V t ((y : ℂ) * I)).im := by
    rwa [le_div_iff₀ hy, mul_comm] at h3
  refine ⟨h1, hYt, hΦ, ?_⟩
  have hpos : 0 < ‖deriv (revMap V t) ((y : ℂ) * I)‖ :=
    norm_pos_iff.2 (deriv_revMap_ne_zero V hV ht hz)
  refine Real.log_le_log hpos ?_
  rw [le_div_iff₀ hy, mul_comm]
  exact hΦ.trans hYt

/-- **Core estimate, for a good version of the Brownian motion.** -/
theorem measureReal_core_good {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hBm : ∀ t, Measurable (B t))
    (T : ℝ≥0) {y a m ℓ : ℝ} (hy : 0 < y) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hYa : Real.log (Real.sqrt (y ^ 2 + 4 * T) / a) ≤ 2 * ℓ) :
    P.real {ω | a ≤ y * ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖ ∧
      |(revMap (drive 8 B ω) T ((y : ℂ) * I)).re| ≤ m} ≤
      coreBound y a m ℓ (Real.sqrt (y ^ 2 + 4 * T)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set Ys := Real.sqrt (y ^ 2 + 4 * T) with hYsdef
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hyYs : y ≤ Ys := Real.le_sqrt_of_sq_le (by linarith)
  have hYs : 0 < Ys := hy.trans_le hyYs
  have hlogyY : 0 ≤ Real.log (Ys / y) := Real.log_nonneg (by rw [le_div_iff₀ hy]; linarith)
  set τ₀ := coreTau ℓ a m with hτ₀
  have hτ0 : 0 < τ₀ := coreTau_pos hℓ
  set τ₁ := Real.log Ys + τ₀ with hτ₁
  set θ := 1 / ℓ with hθ
  have hθ0 : 0 < θ := by positivity
  have h3θ : 3 / θ = 3 * ℓ := by rw [hθ]; field_simp
  have h4θ : 4 / θ = 4 * ℓ := by rw [hθ]; field_simp
  set F := superTest θ (4 * ℓ) τ₁ with hF
  set z : ℂ := (y : ℂ) * I with hz
  have hzim : z.im = y := by simp [hz]
  have hz0 : 0 < z.im := by rw [hzim]; exact hy
  set U := RS.rsProc 8 B z with hU
  have hUeq := RS.rsProc_integralEq hBc 8 hz0
  have hb := RS.lipschitz_rsDrift hz0
  have hbM := RS.norm_rsDrift_le hz0
  have hUc : ∀ ω, Continuous (U · ω) :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hUeq
  have hWc : ∀ ω, Continuous (drive 8 B ω) := NonSwallow.continuous_drive_ns hBc 8
  have hU1 : ∀ ω (t : ℝ≥0), (U t ω).1 = revMap (drive 8 B ω) t z := fun _ _ => rfl
  have hU2 : ∀ ω (t : ℝ≥0), (U t ω).2 = Real.log ‖deriv (revMap (drive 8 B ω) t) z‖ :=
    fun ω t => (log_norm_deriv_revMap _ (hWc ω) t.coe_nonneg (show 0 < z.im from hz0)).symm
  -- the region
  set K : Set (ℂ × ℝ) := {x | y ≤ x.1.im ∧ x.1.im ≤ Ys ∧ x.2 ≤ Real.log (Ys / y)} with hK
  have him : Continuous fun x : ℂ × ℝ => x.1.im := Complex.continuous_im.comp continuous_fst
  have hKc : IsClosed K :=
    (isClosed_le continuous_const him).inter ((isClosed_le him continuous_const).inter
      (isClosed_le continuous_snd continuous_const))
  have hσK : ∀ x ∈ K, τ₀ ≤ superSigma τ₁ x := by
    intro x hx
    have := Real.log_le_log (hy.trans_le hx.1) hx.2.1
    simp only [superSigma, hτ₁]
    linarith
  have hKO : K ⊆ superDom τ₁ := fun x hx =>
    mem_superDom (hy.trans_le hx.1) (hτ0.trans_le (hσK x hx))
  have hLF : ∀ x ∈ K, x ∉ (∅ : Set (ℂ × ℝ)) →
      dynkinGen (RS.rsDrift z.im) (RS.rsNoise 8) F x ≤ 0 := by
    intro x hx _
    refine dynkinGen_superTest_nonpos hθ0 (by rw [h4θ]) (hy.trans_le hx.1) (by rw [hzim]; exact hx.1)
      ?_
    rw [h3θ]
    have := hσK x hx
    have : 3 * ℓ ≤ τ₀ := by
      simp only [hτ₀, coreTau]; have := sq_nonneg (coreXmax ℓ a m); linarith
    linarith
  have hUK : ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ (∅ : Set (ℂ × ℝ))) → U t ω ∈ K := by
    intro ω t htT _
    obtain ⟨r1, r2, -, r4⟩ := revMap_region (hWc ω) hy t.coe_nonneg (show (t : ℝ) ≤ T from htT)
    exact ⟨by rw [hU1]; exact r1, by rw [hU1]; exact r2, by rw [hU2]; exact r4⟩
  set Mb : ℝ := Real.exp ((2 + θ / 2) * Real.log (Ys / y)) * y ^ (-(θ / 2)) *
    τ₀ ^ (-(3 / 2 : ℝ)) * Real.exp (8 * (τ₁ - Real.log y)) with hMb
  have hFnn : ∀ x ∈ K, 0 ≤ F x := fun x hx =>
    superTest_nonneg (hy.trans_le hx.1) (by positivity) (hτ0.trans_le (hσK x hx))
  have hFM : ∀ x ∈ K, |F x| ≤ Mb := by
    intro x hx
    rw [abs_of_nonneg (hFnn x hx)]
    exact superTest_le hθ0 (by positivity) hy hτ0 hx.1 (hσK x hx) hx.2.2
  -- the supersolution inequality
  have hint := RS.integral_localDynkin_stopped_le hB hBc (NonSwallow.bmFilt hBm)
    (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) hb hbM hUeq
    (isOpen_superDom τ₁) isClosed_empty hKc hKO (contDiffOn_superTest θ (4 * ℓ) τ₁) hLF T hUK hFM
  simp only [MeasureTheory.hittingBtwn_empty, min_self] at hint
  -- integrability of `F(U_T)`
  have hUm : Measurable (U T) :=
    (Dynkin.measurable_of_integralEq (NonSwallow.bmFilt hBm) (NonSwallow.bmFilt_adapted hBm) hBc hb
      hbM hUeq hUc T).mono
      ((NonSwallow.bmFilt hBm).le T) le_rfl
  have hFU_K : ∀ ω, U T ω ∈ K := fun ω => hUK ω T le_rfl fun _ _ h => h
  have hFi : Integrable (fun ω => F (U T ω)) P :=
    ItoLite.integrable_of_bound_abs ((measurable_superTest θ (4 * ℓ) τ₁).comp hUm).stronglyMeasurable
      (fun ω => hFM _ (hFU_K ω))
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (Filter.Eventually.of_forall fun ω => hFnn _ (hFU_K ω)) hFi (coreKappa y a m ℓ)
  -- the event is inside `{κ ≤ F(U_T)}`
  have hsub : {ω | a ≤ y * ‖deriv (revMap (drive 8 B ω) T) z‖ ∧
      |(revMap (drive 8 B ω) T z).re| ≤ m} ⊆ {ω | coreKappa y a m ℓ ≤ F (U T ω)} := by
    intro ω hω
    obtain ⟨r1, r2, r3, -⟩ := revMap_region (hWc ω) hy T.coe_nonneg le_rfl
    have hpos : 0 < ‖deriv (revMap (drive 8 B ω) T) z‖ :=
      norm_pos_iff.2 (deriv_revMap_ne_zero _ (hWc ω) T.coe_nonneg (show 0 < z.im from hz0))
    have hL : Real.log (a / y) ≤ (U T ω).2 := by
      rw [hU2]
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hy, mul_comm]
      exact hω.1
    exact coreKappa_le_superTest hℓ ha hy hYa hL (by rw [hU1]; exact hω.1.trans r3)
      (by rw [hU1]; exact r2) (by rw [hU1]; exact hω.2)
  have hstart : F (z, 0) ≤ coreBound y a m ℓ Ys * coreKappa y a m ℓ := by
    rw [coreBound_mul_coreKappa hy ha hℓ hYs hlogyY]
    have := Real.log_le_log hy hyYs
    exact superTest_start_le hy (by positivity) (by simp only [hτ₁]; linarith)
  have hκ := coreKappa_pos (m := m) hy ha hℓ
  have hfin : coreKappa y a m ℓ * P.real {ω | a ≤ y * ‖deriv (revMap (drive 8 B ω) T) z‖ ∧
      |(revMap (drive 8 B ω) T z).re| ≤ m} ≤ coreBound y a m ℓ Ys * coreKappa y a m ℓ :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hκ.le).trans
      (hmk.trans (hint.trans hstart))
  nlinarith

/-- **Core estimate** (the upper bound of [AL14, Theorem 4] in the note's normalization, on the
event `|X_T| ≤ m`), for any standard Brownian motion: for `T ≥ 0`, `y, a, ℓ > 0` with
`log(√(y² + 4T)/a) ≤ 2ℓ`,
`P{a ≤ y |∂_z revMap V T (iy)|, |Re revMap V T (iy)| ≤ m} ≤ coreBound y a m ℓ √(y² + 4T)`. -/
theorem measure_deriv_revMap_tail_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {T : ℝ}
    (hT : 0 ≤ T) {y a m ℓ : ℝ} (hy : 0 < y) (ha : 0 < a) (hℓ : 0 < ℓ)
    (hYa : Real.log (Real.sqrt (y ^ 2 + 4 * T) / a) ≤ 2 * ℓ) :
    P {ω | a ≤ y * ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖ ∧
      |(revMap (drive 8 B ω) T ((y : ℂ) * I)).re| ≤ m} ≤
      ENNReal.ofReal (coreBound y a m ℓ (Real.sqrt (y ^ 2 + 4 * T))) := by
  obtain ⟨B'', hB''m, hB''c, -, hB'', hB''eq⟩ := RS.exists_good_version0 hB
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT
  have hcore := measureReal_core_good (m := m) hB''.toIsPreBrownianReal hB''c hB''m T.toNNReal hy
    ha hℓ (by rwa [hTT])
  rw [hTT] at hcore
  calc P {ω | a ≤ y * ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖ ∧
        |(revMap (drive 8 B ω) T ((y : ℂ) * I)).re| ≤ m}
      ≤ P {ω | a ≤ y * ‖deriv (revMap (drive 8 B'' ω) T) ((y : ℂ) * I)‖ ∧
        |(revMap (drive 8 B'' ω) T ((y : ℂ) * I)).re| ≤ m} := by
        refine measure_mono_ae ?_
        filter_upwards [hB''eq] with ω hω hmem
        have hdr : drive 8 B'' ω = drive 8 B ω := funext fun t => by simp only [drive, hω]
        simpa only [mem_ofPred_eq, hdr] using hmem
    _ = ENNReal.ofReal (P.real {ω | a ≤ y * ‖deriv (revMap (drive 8 B'' ω) T) ((y : ℂ) * I)‖ ∧
        |(revMap (drive 8 B'' ω) T ((y : ℂ) * I)).re| ≤ m}) := (ofReal_measureReal).symm
    _ ≤ ENNReal.ofReal (coreBound y a m ℓ (Real.sqrt (y ^ 2 + 4 * T))) :=
        ENNReal.ofReal_le_ofReal hcore

/-- The horizontal displacement is controlled by the oscillation of the Brownian motion: for a
continuous path with `B 0 = 0`, `|Re revMap (drive 8 B ω) T (iy)| ≤ 2√8 · osc_{[0,T]} B`. -/
theorem abs_re_revMap_le_bmOsc {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (hc : Continuous (B · ω))
    (h0 : B 0 ω = 0) {T y : ℝ} (hT : 0 ≤ T) (hy : 0 < y) :
    |(revMap (drive 8 B ω) T ((y : ℂ) * I)).re| ≤
      2 * (Real.sqrt 8 * bmOsc B 0 T.toNNReal ω) := by
  have hV : Continuous (drive 8 B ω) :=
    continuous_const.mul (hc.comp continuous_real_toNNReal)
  refine (abs_re_revMap_mul_I_le_two_mul_sSup hV hy hT).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine csSup_le ((nonempty_Icc.2 hT).image _) ?_
  rintro _ ⟨v, hv, rfl⟩
  have hr : v.toNNReal ∈ Icc (0 : ℝ≥0) (0 + T.toNNReal) := by
    rw [zero_add]
    exact ⟨zero_le, Real.toNNReal_le_toNNReal hv.2⟩
  have h1 := RS.abs_sub_le_bmOsc hc hr
  rw [h0, sub_zero] at h1
  simp only [drive, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)

/-- **Core estimate, full tail.** For `T > 0`, `m > 0` and `y, a, ℓ` as in
`measure_deriv_revMap_tail_le`,
`P{a ≤ y |∂_z revMap V T (iy)|} ≤ coreBound y a m ℓ √(y² + 4T) + 2 exp(−m²/(64T))`. -/
theorem measure_deriv_revMap_ge_le {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {T : ℝ}
    (hT : 0 < T) {y a m ℓ : ℝ} (hy : 0 < y) (ha : 0 < a) (hm : 0 < m) (hℓ : 0 < ℓ)
    (hYa : Real.log (Real.sqrt (y ^ 2 + 4 * T) / a) ≤ 2 * ℓ) :
    P {ω | a ≤ y * ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖} ≤
      ENNReal.ofReal (coreBound y a m ℓ (Real.sqrt (y ^ 2 + 4 * T))) +
        ENNReal.ofReal (2 * Real.exp (-(m ^ 2) / (64 * T))) := by
  obtain ⟨B'', hB''m, hB''c, hB''0, hB'', hB''eq⟩ := RS.exists_good_version0 hB
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT.le
  have hT' : 0 < T.toNNReal := Real.toNNReal_pos.2 hT
  have h8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have hosc := BMOsc.bmOsc_tail hB''.toIsPreBrownianReal hB''m hB''c 0 T.toNNReal hT'
    (a := m / (2 * Real.sqrt 8)) (by positivity)
  have hexp : -(m / (2 * Real.sqrt 8)) ^ 2 / (2 * ((T.toNNReal : ℝ≥0) : ℝ)) =
      -(m ^ 2) / (64 * T) := by
    rw [hTT, div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    field_simp
    ring
  rw [hexp] at hosc
  calc P {ω | a ≤ y * ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖}
      ≤ P {ω | a ≤ y * ‖deriv (revMap (drive 8 B'' ω) T) ((y : ℂ) * I)‖} := by
        refine measure_mono_ae ?_
        filter_upwards [hB''eq] with ω hω hmem
        have hdr : drive 8 B'' ω = drive 8 B ω := funext fun t => by simp only [drive, hω]
        simpa only [mem_ofPred_eq, hdr] using hmem
    _ ≤ P ({ω | a ≤ y * ‖deriv (revMap (drive 8 B'' ω) T) ((y : ℂ) * I)‖ ∧
          |(revMap (drive 8 B'' ω) T ((y : ℂ) * I)).re| ≤ m} ∪
          {ω | m / (2 * Real.sqrt 8) < bmOsc B'' 0 T.toNNReal ω}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hX : |(revMap (drive 8 B'' ω) T ((y : ℂ) * I)).re| ≤ m
        · exact Or.inl ⟨hω, hX⟩
        · refine Or.inr ?_
          have h1 := abs_re_revMap_le_bmOsc (hB''c ω) (hB''0 ω) hT.le hy
          show m / (2 * Real.sqrt 8) < bmOsc B'' 0 T.toNNReal ω
          rw [div_lt_iff₀ (by positivity)]
          linarith [not_le.1 hX]
    _ ≤ P {ω | a ≤ y * ‖deriv (revMap (drive 8 B'' ω) T) ((y : ℂ) * I)‖ ∧
          |(revMap (drive 8 B'' ω) T ((y : ℂ) * I)).re| ≤ m} +
          P {ω | m / (2 * Real.sqrt 8) < bmOsc B'' 0 T.toNNReal ω} := measure_union_le _ _
    _ ≤ _ := add_le_add (measure_deriv_revMap_tail_le hB'' hT.le hy ha hℓ hYa) hosc

/-- **The tail is empty above the deterministic height bound**: `y Φ_T ≤ Y_T ≤ √(y² + 4T)`. -/
theorem measure_deriv_revMap_ge_eq_zero {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {T : ℝ}
    (hT : 0 ≤ T) {y a : ℝ} (hy : 0 < y) (ha : Real.sqrt (y ^ 2 + 4 * T) < a) :
    P {ω | a ≤ y * ‖deriv (revMap (drive 8 B ω) T) ((y : ℂ) * I)‖} = 0 := by
  obtain ⟨B'', -, hB''c, -, -, hB''eq⟩ := RS.exists_good_version0 hB
  refine measure_mono_null_ae ?_ (measure_empty (μ := P))
  filter_upwards [hB''eq] with ω hω hmem
  have hdr : drive 8 B'' ω = drive 8 B ω := funext fun t => by simp only [drive, hω]
  have hV : Continuous (drive 8 B ω) := hdr ▸ NonSwallow.continuous_drive_ns hB''c 8 ω
  obtain ⟨-, r2, r3, -⟩ := revMap_region hV hy hT le_rfl
  exact absurd (lt_of_le_of_lt (hmem.trans r3) (r2.trans_lt ha)) (lt_irrefl a)

end Core

/-- **The bound in polylogarithmic form.** If `ℓ ≤ Λ`, `½ log(1 + m²/a²) ≤ Λ`, `1 ≤ Λ` and
`0 < D ≤ log(Y*/y)`, then `coreBound ≤ e^{9/8} (y/a)² (30Λ²/D)^{3/2}`. -/
theorem coreBound_le {y a m ℓ Ys Λ D : ℝ} (hℓ : 0 < ℓ) (hℓΛ : ℓ ≤ Λ)
    (hmΛ : Real.log (1 + m ^ 2 / a ^ 2) / 2 ≤ Λ) (hΛ : 1 ≤ Λ) (hD : 0 < D)
    (hDY : D ≤ Real.log (Ys / y)) :
    coreBound y a m ℓ Ys ≤ Real.exp (9 / 8) * (y / a) ^ 2 * (30 * Λ ^ 2 / D) ^ (3 / 2 : ℝ) := by
  unfold coreBound
  have hτ := coreTau_pos (a := a) (m := m) hℓ
  have hx : coreXmax ℓ a m ≤ 5 * Λ := by unfold coreXmax; linarith
  have hx0 := coreXmax_pos (a := a) (m := m) hℓ
  have hnum : coreTau ℓ a m + 2 * ℓ ≤ 30 * Λ ^ 2 := by
    unfold coreTau
    have : coreXmax ℓ a m ^ 2 ≤ 25 * Λ ^ 2 := by nlinarith
    nlinarith
  have hq : (coreTau ℓ a m + 2 * ℓ) / (Real.log (Ys / y) + coreTau ℓ a m) ≤ 30 * Λ ^ 2 / D := by
    rw [div_le_div_iff₀ (by linarith) hD]
    have : 0 ≤ coreTau ℓ a m + 2 * ℓ := by linarith
    nlinarith
  have h0 : 0 ≤ (coreTau ℓ a m + 2 * ℓ) / (Real.log (Ys / y) + coreTau ℓ a m) :=
    div_nonneg (by linarith) (by linarith)
  gcongr

/-! ## [AL14]'s normalization: the reverse flow (9) -/

/-- [AL14]'s reverse Loewner flow (9), `∂_t h_t(z) = 1/(4 (U_t − h_t(z)))`, `h_0(z) = z`, written
through the note's uncentred reverse flow driven by `√8 U`: `h_t(z) = revFlow (√8 U) t (√8 z)/√8`
(`alRevFlow_zero`, `hasDerivWithinAt_alRevFlow`). -/
def alRevFlow (U : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  revFlow (fun r => Real.sqrt 8 * U r) t ((Real.sqrt 8 : ℂ) * z) / (Real.sqrt 8 : ℂ)

theorem sqrt8_mul_mem_H {z : ℂ} (hz : z ∈ H) : (Real.sqrt 8 : ℂ) * z ∈ H := by
  show 0 < ((Real.sqrt 8 : ℂ) * z).im
  have h8 : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have : 0 < z.im := hz
  simpa using mul_pos h8 this

theorem alRevFlow_zero {U : ℝ → ℝ} (hU : Continuous U) {z : ℂ} (hz : z ∈ H) :
    alRevFlow U 0 z = z := by
  have h8 : (Real.sqrt 8 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num)).ne'
  have hV : Continuous fun r => Real.sqrt 8 * U r := continuous_const.mul hU
  rw [alRevFlow, revFlow_zero hV (sqrt8_mul_mem_H hz)]
  field_simp

/-- **[AL14] (9).** `∂_t h_t(z) = 1/(4 (U_t − h_t(z)))` on every `[0, S]`. -/
theorem hasDerivWithinAt_alRevFlow {U : ℝ → ℝ} (hU : Continuous U) {z : ℂ} (hz : z ∈ H)
    {S s : ℝ} (hS : 0 ≤ S) (hs : s ∈ Icc 0 S) :
    HasDerivWithinAt (fun r => alRevFlow U r z) (1 / (4 * (U s - alRevFlow U s z))) (Icc 0 S)
      s := by
  have hV : Continuous fun r => Real.sqrt 8 * U r := continuous_const.mul hU
  have h := (hasDerivWithinAt_revFlow hV (sqrt8_mul_mem_H hz) hS hs).div_const (Real.sqrt 8 : ℂ)
  refine h.congr_deriv ?_
  have h8 : (Real.sqrt 8 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num)).ne'
  have h88 : (Real.sqrt 8 : ℂ) * (Real.sqrt 8 : ℂ) = 8 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  set w := revFlow (fun r => Real.sqrt 8 * U r) s ((Real.sqrt 8 : ℂ) * z)
  have hw : w = (Real.sqrt 8 : ℂ) * alRevFlow U s z := by
    simp only [alRevFlow, w]; field_simp
  rw [hw]
  push_cast
  rw [show (Real.sqrt 8 : ℂ) * alRevFlow U s z - (Real.sqrt 8 : ℂ) * (U s : ℂ) =
    (Real.sqrt 8 : ℂ) * (alRevFlow U s z - U s) by ring]
  rw [div_div, mul_comm ((Real.sqrt 8 : ℂ)) (alRevFlow U s z - U s), mul_assoc, h88,
    show (U s : ℂ) - alRevFlow U s z = -(alRevFlow U s z - U s) by ring]
  by_cases hx : alRevFlow U s z - U s = 0
  · rw [hx]; simp
  · field_simp
    ring

theorem deriv_alRevFlow (U : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    deriv (alRevFlow U t) z =
      deriv (revMap (fun r => Real.sqrt 8 * U r) t) ((Real.sqrt 8 : ℂ) * z) := by
  have h8 : (Real.sqrt 8 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 (by norm_num)).ne'
  have e : alRevFlow U t = fun w => revFlow (fun r => Real.sqrt 8 * U r) t
      ((Real.sqrt 8 : ℂ) * w) / (Real.sqrt 8 : ℂ) := rfl
  rw [e, deriv_div_const, deriv_comp_mul_left, deriv_revFlow, smul_eq_mul]
  field_simp

/-! ## [AL14] Theorem 4, upper bound: scalar estimates -/

theorem log_two_bounds : 0.69 < Real.log 2 ∧ Real.log 2 < 0.7 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

theorem log_ge_log_two {t : ℝ} (ht : 2 ≤ t) : Real.log 2 ≤ Real.log t :=
  Real.log_le_log (by norm_num) ht

/-- `2 e^{−t} ≤ (16/(log 2)^5) e^{−t/2} t^{2β − 3/2} (log t)^5` for `t ≥ 2`, `β ≥ 0`. -/
theorem thm4_tail_le {β t : ℝ} (hβ : 0 ≤ β) (ht : 2 ≤ t) :
    2 * Real.exp (-t) ≤
      16 / Real.log 2 ^ 5 * Real.exp (-(t / 2)) * t ^ (2 * β - 3 / 2) * Real.log t ^ 5 := by
  have ht0 : 0 < t := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt := log_ge_log_two ht
  -- `e^{t/2} ≥ t²/8`
  have hq := Real.quadratic_le_exp_of_nonneg (x := t / 2) (by linarith)
  have hexp : t ^ 2 / 8 ≤ Real.exp (t / 2) := by nlinarith
  -- `e^{−t/2} ≤ 8 t^{−3/2}`
  have h32 : t ^ (-(3 / 2 : ℝ)) * t ^ 2 = t ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht0]; norm_num
  have hhalf : 1 ≤ t ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have he1 : Real.exp (-(t / 2)) ≤ 8 * t ^ (-(3 / 2 : ℝ)) := by
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have hpos : 0 < t ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos ht0 _
    calc (1 : ℝ) ≤ t ^ (1 / 2 : ℝ) := hhalf
      _ = t ^ (-(3 / 2 : ℝ)) * t ^ 2 := h32.symm
      _ ≤ t ^ (-(3 / 2 : ℝ)) * (8 * Real.exp (t / 2)) := by gcongr; linarith
      _ = 8 * t ^ (-(3 / 2 : ℝ)) * Real.exp (t / 2) := by ring
  have hβt : t ^ (-(3 / 2 : ℝ)) ≤ t ^ (2 * β - 3 / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hl5 : 1 ≤ Real.log t ^ 5 / Real.log 2 ^ 5 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hl2.le hlt 5
  have hsplit : Real.exp (-t) = Real.exp (-(t / 2)) * Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have hE : 0 < Real.exp (-(t / 2)) := Real.exp_pos _
  have hT : 0 ≤ t ^ (2 * β - 3 / 2) := Real.rpow_nonneg ht0.le _
  calc 2 * (Real.exp (-(t / 2)) * Real.exp (-(t / 2)))
      ≤ 2 * (Real.exp (-(t / 2)) * (8 * t ^ (2 * β - 3 / 2))) := by gcongr; linarith
    _ = 16 * Real.exp (-(t / 2)) * t ^ (2 * β - 3 / 2) * 1 := by ring
    _ ≤ 16 * Real.exp (-(t / 2)) * t ^ (2 * β - 3 / 2) * (Real.log t ^ 5 / Real.log 2 ^ 5) := by
        gcongr
    _ = 16 / Real.log 2 ^ 5 * Real.exp (-(t / 2)) * t ^ (2 * β - 3 / 2) * Real.log t ^ 5 := by
        field_simp

/-- `(c L²/t)^{3/2} = c^{3/2} L³ t^{−3/2}` for `c, L ≥ 0`, `t > 0`. -/
theorem rpow_three_halves_eq {c L t : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) (ht : 0 < t) :
    (c * L ^ 2 / t) ^ (3 / 2 : ℝ) = c ^ (3 / 2 : ℝ) * L ^ 3 * t ^ (-(3 / 2 : ℝ)) := by
  rw [Real.div_rpow (by positivity) ht.le, Real.mul_rpow hc (by positivity), Real.rpow_neg ht.le,
    ← Real.rpow_natCast L 2, ← Real.rpow_mul hL]
  norm_num
  rw [div_eq_mul_inv]

/-! ## [AL14] Theorem 4, upper bound -/

/-- The constant `c₂` of our proof of the upper bound of [AL14, Theorem 4]. -/
def thm4Const (β : ℝ) : ℝ :=
  Real.exp (9 / 8) * (420 * (3 / Real.log 2 + 1 + β) ^ 2) ^ (3 / 2 : ℝ) / Real.log 2 ^ 2 +
    16 / Real.log 2 ^ 5

section Thm4Params

/-! The parameters of the proof of Theorem 4, as opaque reals with their defining equations:
`T = e^{t/2}`, `y = √8`, `λ = e^{t/4} t^{−β}`, `a = yλ`, `m = 8 e^{t/4} √t`, `ℓ = β log t/2 + 1`,
`Y* = √(y² + 4T)`, `Λ = 3 + (1 + β) log t`, `D = t/4 − log 2/2`. -/

variable {β t T y lam a m ℓ Ys : ℝ}

theorem thm4_sqrt_exp (t : ℝ) : Real.sqrt (Real.exp (t / 2)) = Real.exp (t / 4) := by
  rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add]; ring_nf

theorem thm4_exp_sq (t : ℝ) : Real.exp (t / 4) ^ 2 = Real.exp (t / 2) := by
  rw [← Real.exp_nat_mul]; ring_nf

theorem thm4_Ys_le (ht : 2 ≤ t) (hT : T = Real.exp (t / 2)) (hy : y = Real.sqrt 8)
    (hYs : Ys = Real.sqrt (y ^ 2 + 4 * T)) : Ys ≤ y * Real.exp (t / 4) := by
  have hT2 : 2 ≤ T := by
    have := Real.add_one_le_exp (t / 2)
    rw [hT]; linarith
  have hy2 : y ^ 2 = 8 := by rw [hy]; exact Real.sq_sqrt (by norm_num)
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  rw [hYs, Real.sqrt_le_left (by positivity), mul_pow, hy2, thm4_exp_sq, ← hT]
  nlinarith

theorem thm4_hYa (ht : 2 ≤ t) (hT : T = Real.exp (t / 2)) (hy : y = Real.sqrt 8)
    (hlam : lam = Real.exp (t / 4) * t ^ (-β)) (ha : a = y * lam)
    (hℓ : ℓ = β * Real.log t / 2 + 1) (hYs : Ys = Real.sqrt (y ^ 2 + 4 * T)) :
    Real.log (Ys / a) ≤ 2 * ℓ := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := by rw [hy]; exact Real.sqrt_pos.2 (by norm_num)
  have hT0 : 0 < T := by rw [hT]; exact Real.exp_pos _
  have ha0 : 0 < a := by rw [ha, hlam]; positivity
  have hYs0 : 0 < Ys := by rw [hYs]; exact Real.sqrt_pos.2 (by positivity)
  have htβ : 0 < t ^ β := Real.rpow_pos_of_pos ht0 β
  have h1 : Ys / a ≤ t ^ β := by
    rw [div_le_iff₀ ha0, ha, hlam, Real.rpow_neg ht0.le]
    calc Ys ≤ y * Real.exp (t / 4) := thm4_Ys_le ht hT hy hYs
      _ = t ^ β * (y * (Real.exp (t / 4) * (t ^ β)⁻¹)) := by field_simp
  have h2 := Real.log_le_log (div_pos hYs0 ha0) h1
  rw [Real.log_rpow ht0] at h2
  have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t)
  rw [hℓ]
  linarith

theorem thm4_hmΛ (hβ : 0 < β) (ht : 2 ≤ t) (hT : T = Real.exp (t / 2)) (hy : y = Real.sqrt 8)
    (hlam : lam = Real.exp (t / 4) * t ^ (-β)) (ha : a = y * lam)
    (hm : m = 8 * Real.exp (t / 4) * Real.sqrt t) :
    Real.log (1 + m ^ 2 / a ^ 2) / 2 ≤ 3 + (1 + β) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hT0 : 0 < T := by rw [hT]; exact Real.exp_pos _
  have hy2 : y ^ 2 = 8 := by rw [hy]; exact Real.sq_sqrt (by norm_num)
  have hm2 : m ^ 2 = 64 * T * t := by
    rw [hm, mul_pow, mul_pow, Real.sq_sqrt ht0.le, thm4_exp_sq, ← hT]; ring
  have ha2 : a ^ 2 = 8 * T * (t ^ (2 * β))⁻¹ := by
    rw [ha, hlam, mul_pow, mul_pow, hy2, thm4_exp_sq, ← hT, ← Real.rpow_natCast (t ^ (-β)),
      ← Real.rpow_mul ht0.le, ← Real.rpow_neg ht0.le]
    push_cast; ring_nf
  have htb : 1 ≤ t ^ (2 * β) := Real.one_le_rpow ht1 (by linarith)
  have hq : m ^ 2 / a ^ 2 = 8 * t * t ^ (2 * β) := by
    rw [hm2, ha2]; field_simp; norm_num
  have hle : 1 + m ^ 2 / a ^ 2 ≤ 9 * t * t ^ (2 * β) := by rw [hq]; nlinarith
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_rpow ht0] at hlog
  have h9 : Real.log 9 ≤ 6 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have := Real.quadratic_le_exp_of_nonneg (x := 6) (by norm_num)
    linarith
  have := Real.log_nonneg ht1
  linarith

theorem thm4_hDY (hT : T = Real.exp (t / 2)) (hy : y = Real.sqrt 8)
    (hYs : Ys = Real.sqrt (y ^ 2 + 4 * T)) : t / 4 - Real.log 2 / 2 ≤ Real.log (Ys / y) := by
  have hy0 : 0 < y := by rw [hy]; exact Real.sqrt_pos.2 (by norm_num)
  have hy2 : y ^ 2 = 8 := by rw [hy]; exact Real.sq_sqrt (by norm_num)
  have hT0 : 0 < T := by rw [hT]; exact Real.exp_pos _
  have h1 : 2 * Real.exp (t / 4) / y ≤ Ys / y := by
    refine div_le_div_of_nonneg_right ?_ hy0.le
    rw [hYs, Real.le_sqrt (by positivity) (by positivity), mul_pow, thm4_exp_sq, ← hT, hy2]
    linarith
  have h2 := Real.log_le_log (by positivity) h1
  have hlogy : Real.log y = 3 * Real.log 2 / 2 := by
    rw [hy, Real.log_sqrt (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    push_cast; ring
  rw [Real.log_div (by positivity) hy0.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
    Real.log_exp, hlogy] at h2
  linarith

theorem thm4_hya2 (ht : 2 ≤ t) (hy : y = Real.sqrt 8)
    (hlam : lam = Real.exp (t / 4) * t ^ (-β)) (ha : a = y * lam) :
    (y / a) ^ 2 = Real.exp (-(t / 2)) * t ^ (2 * β) := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < y := by rw [hy]; exact Real.sqrt_pos.2 (by norm_num)
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have h1 : y / a = lam⁻¹ := by rw [ha]; field_simp
  have hl2' : lam ^ 2 = Real.exp (t / 2) * (t ^ (2 * β))⁻¹ := by
    rw [hlam, mul_pow, thm4_exp_sq, ← Real.rpow_natCast (t ^ (-β)), ← Real.rpow_mul ht0.le,
      ← Real.rpow_neg ht0.le]
    push_cast; ring_nf
  rw [h1, inv_pow, hl2', mul_inv, inv_inv, ← Real.exp_neg]

/-- `(30Λ²/D)^{3/2} ≤ (420 K₁²)^{3/2} (log t)³ t^{−3/2}` with `K₁ = 3/log 2 + 1 + β`. -/
theorem thm4_hq (hβ : 0 < β) (ht : 2 ≤ t) :
    (30 * (3 + (1 + β) * Real.log t) ^ 2 / (t / 4 - Real.log 2 / 2)) ^ (3 / 2 : ℝ) ≤
      (420 * (3 / Real.log 2 + 1 + β) ^ 2) ^ (3 / 2 : ℝ) * Real.log t ^ 3 *
        t ^ (-(3 / 2 : ℝ)) := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hl2a, hl2b⟩ := log_two_bounds
  have hl2 : 0 < Real.log 2 := by linarith
  have hlt := log_ge_log_two ht
  have hlt0 : 0 < Real.log t := by linarith
  have hD0 : 0 < t / 4 - Real.log 2 / 2 := by linarith
  have hDt : t / 14 ≤ t / 4 - Real.log 2 / 2 := by linarith
  have hΛK : 3 + (1 + β) * Real.log t ≤ (3 / Real.log 2 + 1 + β) * Real.log t := by
    have h1 : 1 ≤ Real.log t / Real.log 2 := (one_le_div hl2).2 hlt
    have e : (3 / Real.log 2 + 1 + β) * Real.log t =
        3 * (Real.log t / Real.log 2) + (1 + β) * Real.log t := by field_simp; ring
    rw [e]; linarith
  have hq : 30 * (3 + (1 + β) * Real.log t) ^ 2 / (t / 4 - Real.log 2 / 2) ≤
      420 * (3 / Real.log 2 + 1 + β) ^ 2 * Real.log t ^ 2 / t := by
    rw [div_le_div_iff₀ hD0 ht0]
    have hsq : (3 + (1 + β) * Real.log t) ^ 2 ≤ ((3 / Real.log 2 + 1 + β) * Real.log t) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hΛK 2
    calc 30 * (3 + (1 + β) * Real.log t) ^ 2 * t
        ≤ 30 * ((3 / Real.log 2 + 1 + β) * Real.log t) ^ 2 * t := by gcongr
      _ ≤ 30 * ((3 / Real.log 2 + 1 + β) * Real.log t) ^ 2 * (14 * (t / 4 - Real.log 2 / 2)) := by
          gcongr; linarith
      _ = 420 * (3 / Real.log 2 + 1 + β) ^ 2 * Real.log t ^ 2 * (t / 4 - Real.log 2 / 2) := by
          ring
  have hK2 : 0 ≤ 420 * (3 / Real.log 2 + 1 + β) ^ 2 := by positivity
  rw [← rpow_three_halves_eq hK2 hlt0.le ht0]
  exact Real.rpow_le_rpow (div_nonneg (by positivity) hD0.le) hq (by norm_num)

theorem thm4_log_cube_le (ht : 2 ≤ t) : Real.log t ^ 3 ≤ Real.log t ^ 5 / Real.log 2 ^ 2 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt := log_ge_log_two ht
  rw [le_div_iff₀ (pow_pos hl2 2)]
  have h2 : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hl2.le hlt 2
  have h3 : 0 ≤ Real.log t ^ 3 := pow_nonneg (hl2.le.trans hlt) 3
  calc Real.log t ^ 3 * Real.log 2 ^ 2 ≤ Real.log t ^ 3 * Real.log t ^ 2 :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = Real.log t ^ 5 := by ring

/-- The scalar part of Theorem 4: the core bound and the Gaussian tail are at most
`c₂ e^{−t/2} t^{2β − 3/2} (log t)^5`. -/
theorem thm4_scalar (hβ : 0 < β) (ht : 2 ≤ t) (hT : T = Real.exp (t / 2))
    (hy : y = Real.sqrt 8) (hlam : lam = Real.exp (t / 4) * t ^ (-β)) (ha : a = y * lam)
    (hm : m = 8 * Real.exp (t / 4) * Real.sqrt t) (hℓ : ℓ = β * Real.log t / 2 + 1)
    (hYs : Ys = Real.sqrt (y ^ 2 + 4 * T)) :
    coreBound y a m ℓ Ys + 2 * Real.exp (-(m ^ 2) / (64 * T)) ≤
      thm4Const β * Real.exp (-(t / 2)) * t ^ (2 * β - 3 / 2) * Real.log t ^ 5 := by
  have ht0 : 0 < t := by linarith
  obtain ⟨hl2a, hl2b⟩ := log_two_bounds
  have hlt := log_ge_log_two ht
  have hlt0 : 0 < Real.log t := by linarith
  have hT0 : 0 < T := by rw [hT]; exact Real.exp_pos _
  have hℓ0 : 0 < ℓ := by rw [hℓ]; positivity
  have hℓΛ : ℓ ≤ 3 + (1 + β) * Real.log t := by rw [hℓ]; nlinarith
  have hΛ1 : 1 ≤ 3 + (1 + β) * Real.log t := by nlinarith
  have hD0 : 0 < t / 4 - Real.log 2 / 2 := by linarith
  have hcb := coreBound_le hℓ0 hℓΛ (thm4_hmΛ hβ ht hT hy hlam ha hm) hΛ1 hD0
    (thm4_hDY hT hy hYs)
  rw [thm4_hya2 ht hy hlam ha] at hcb
  have hq := thm4_hq hβ ht
  have hl3 := thm4_log_cube_le (t := t) ht
  have hm2 : m ^ 2 = 64 * T * t := by
    rw [hm, mul_pow, mul_pow, Real.sq_sqrt ht0.le, thm4_exp_sq, ← hT]; ring
  have htail : 2 * Real.exp (-(m ^ 2) / (64 * T)) = 2 * Real.exp (-t) := by
    rw [hm2]; congr 2; field_simp
  rw [htail]
  have htl := thm4_tail_le hβ.le ht
  have hsplit : t ^ (2 * β - 3 / 2) = t ^ (2 * β) * t ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add ht0]; ring_nf
  have hE : 0 ≤ Real.exp (9 / 8) * (Real.exp (-(t / 2)) * t ^ (2 * β)) := by positivity
  have hcore : Real.exp (9 / 8) * (Real.exp (-(t / 2)) * t ^ (2 * β)) *
      (30 * (3 + (1 + β) * Real.log t) ^ 2 / (t / 4 - Real.log 2 / 2)) ^ (3 / 2 : ℝ) ≤
      Real.exp (9 / 8) * (420 * (3 / Real.log 2 + 1 + β) ^ 2) ^ (3 / 2 : ℝ) / Real.log 2 ^ 2 *
        Real.exp (-(t / 2)) * t ^ (2 * β - 3 / 2) * Real.log t ^ 5 := by
    calc _ ≤ Real.exp (9 / 8) * (Real.exp (-(t / 2)) * t ^ (2 * β)) *
          ((420 * (3 / Real.log 2 + 1 + β) ^ 2) ^ (3 / 2 : ℝ) * Real.log t ^ 3 *
            t ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hq hE
      _ ≤ Real.exp (9 / 8) * (Real.exp (-(t / 2)) * t ^ (2 * β)) *
          ((420 * (3 / Real.log 2 + 1 + β) ^ 2) ^ (3 / 2 : ℝ) *
            (Real.log t ^ 5 / Real.log 2 ^ 2) * t ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by rw [hsplit]; field_simp
  unfold thm4Const
  linarith

end Thm4Params

/-- **[AL14] Theorem 4, upper bound.** For `β > 0` there is `c₂` such that, for every standard
Brownian motion `U` and every `t ≥ 2`, with `h_t` [AL14]'s reverse flow (9) (`alRevFlow`) and
`R_t = |h'_{e^{t/2}}(i)|`, `P{R_t ≥ e^{t/4} t^{−β}} ≤ c₂ e^{−t/2} t^{2β − 3/2} (log t)^5`.
([AL14] state it for `0 < β < 2` together with the lower bound.) -/
theorem al14_theorem4_upper {β : ℝ} (hβ : 0 < β) :
    ∃ c₂ : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℝ≥0 → Ω → ℝ},
      IsBrownianReal U P → ∀ t : ℝ, 2 ≤ t →
        P {ω | Real.exp (t / 4) * t ^ (-β) ≤
            ‖deriv (alRevFlow (fun r => U r.toNNReal ω) (Real.exp (t / 2))) I‖} ≤
          ENNReal.ofReal (c₂ * Real.exp (-(t / 2)) * t ^ (2 * β - 3 / 2) * Real.log t ^ 5) := by
  refine ⟨thm4Const β, fun {Ω} _ {P} {U} hU t ht => ?_⟩
  obtain ⟨T, hT⟩ : ∃ T, T = Real.exp (t / 2) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = Real.sqrt 8 := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = Real.exp (t / 4) * t ^ (-β) := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m, m = 8 * Real.exp (t / 4) * Real.sqrt t := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = β * Real.log t / 2 + 1 := ⟨_, rfl⟩
  obtain ⟨Ys, hYs⟩ : ∃ Ys, Ys = Real.sqrt (y ^ 2 + 4 * T) := ⟨_, rfl⟩
  have ht0 : 0 < t := by linarith
  have hT0 : 0 < T := by rw [hT]; exact Real.exp_pos _
  have hy0 : 0 < y := by rw [hy]; exact Real.sqrt_pos.2 (by norm_num)
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have ha0 : 0 < y * lam := mul_pos hy0 hlam0
  have hm0 : 0 < m := by rw [hm]; have := Real.sqrt_pos.2 ht0; positivity
  have hℓ0 : 0 < ℓ := by
    rw [hℓ]; have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ t); positivity
  have hset : {ω | Real.exp (t / 4) * t ^ (-β) ≤
      ‖deriv (alRevFlow (fun r => U r.toNNReal ω) (Real.exp (t / 2))) I‖} =
      {ω | y * lam ≤ y * ‖deriv (revMap (drive 8 U ω) T) ((y : ℂ) * I)‖} := by
    ext ω
    simp only [mem_ofPred_eq, deriv_alRevFlow]
    rw [mul_le_mul_iff_of_pos_left hy0, hlam, hT, hy]
    rfl
  rw [hset]
  have hYa := thm4_hYa ht hT hy hlam rfl hℓ hYs
  have hmain := measure_deriv_revMap_ge_le hU hT0 hy0 ha0 hm0 hℓ0 (hYs ▸ hYa)
  rw [← hYs] at hmain
  refine hmain.trans ?_
  have hsc := thm4_scalar hβ ht hT hy hlam rfl hm hℓ hYs
  have hc0 := coreBound_nonneg y (y * lam) m ℓ Ys hℓ0 (by
    rw [hYs]; exact Real.log_nonneg (by
      rw [le_div_iff₀ hy0, one_mul]; exact Real.le_sqrt_of_sq_le (by linarith)))
  rw [← ENNReal.ofReal_add hc0 (by positivity)]
  exact ENNReal.ofReal_le_ofReal hsc

end InteractingSLE.SLE8.AL14
