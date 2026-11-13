import QuantumZipper.Proofs.RS.MartingaleBoundGen
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The exponential test functions of the critical change of measure (SLE₈ note, (3.4), (3.9))

SLE₈ note `source/sle8-continuity.pdf`, §3.1, pp. 4–5 (transcription `source/sle8/sle8-continuity.md`,
anchor `lem-3.1-proof`).

State space `ℂ × ℝ`, state `x = (Z, L)` with `Z = X + iY` the centred reverse flow and `L = log Φ`
(QuantumZipper's `RS.rsProc`); drift `RS.rsDrift y₀` and noise `RS.rsNoise 8` (the reverse flow driven
by `√8 B`). In the note's coordinates `J = arsinh (X / Y)`, `u = log Y`, `Φ = e^L`, the function

`expTest θ (Z, L) = e^{2L} Y^{-2θ²} cosh J e^{θ J} = Φ² cosh J · e^{θ J - 2θ² u}`

has zero Dynkin generator for every real `θ` (`dynkinGen_expTest`). For `θ = 0` it is the note's
critical martingale `𝓜 = Φ̂² cosh J` of (3.9); for general `θ` it is `𝓜 · exp(θ J − 2θ² u)`, the
density times the exponential martingale of a Brownian motion of variance rate `4` in the height
parameter, which identifies the law of `J` under the tilted measure `ℚ`.

Writing `t = X / Y`, `cosh J = √(1 + t²)` and `e^{θ J} = e^{θ arsinh t}`, so
`expTest θ (Z, L) = e^{2L} Y^{-2θ²} g_θ(X / Y)` with `g_θ t = √(1 + t²) e^{θ arsinh t}` (`expProfile`).
The generator is `e^{2L} Y^{-2θ²} / (Y² (1 + t²))` times
`4(1+t²) g'' − 4 t g' + (−4θ² + 4 (t² − 1)/(1 + t²)) g`, which vanishes identically
(`expProfile_ode`).

## Main results

* `contDiffOn_expTest`: `expTest θ` is `C³` on `{Im Z > 0}`;
* `dynkinGen_expTest`: its Dynkin generator vanishes where the taming of the drift is inactive;
* `expTest_sq_le`: `expTest θ ² ≤ C · RS.rsTest 8 (1 + |θ|)` on `{y ≤ Y ≤ √5, e^L ≤ Y / y}` (the
  domination used for uniform integrability).
-/

noncomputable section

open Set Filter Topology Real

namespace InteractingSLE.SLE8.ChangeOfMeasure

open QuantumZipper QuantumZipper.RS FwdHolo FrozenMart

/-! ### The profile `g_θ t = √(1 + t²) e^{θ arsinh t}` -/

/-- The profile `g_θ t = √(1 + t²) e^{θ arsinh t} = cosh J · e^{θ J}` with `t = sinh J`. -/
def expProfile (θ t : ℝ) : ℝ := √(1 + t ^ 2) * Real.exp (θ * Real.arsinh t)

/-- `g_θ'(t) = (t / √(1 + t²) + θ) e^{θ arsinh t}`. -/
def expProfile' (θ t : ℝ) : ℝ := (t / √(1 + t ^ 2) + θ) * Real.exp (θ * Real.arsinh t)

/-- `g_θ''(t) = (1 / √(1 + t²)³ + θ t / (1 + t²) + θ² / √(1 + t²)) e^{θ arsinh t}`. -/
def expProfile'' (θ t : ℝ) : ℝ :=
  (1 / √(1 + t ^ 2) ^ 3 + θ * t / (1 + t ^ 2) + θ ^ 2 / √(1 + t ^ 2)) *
    Real.exp (θ * Real.arsinh t)

theorem one_add_sq_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem sqrt_one_add_sq_pos (t : ℝ) : 0 < √(1 + t ^ 2) := Real.sqrt_pos.2 (one_add_sq_pos t)

theorem sq_sqrt_one_add_sq (t : ℝ) : √(1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
  Real.sq_sqrt (one_add_sq_pos t).le

theorem hasDerivAt_sqrt_one_add_sq (t : ℝ) :
    HasDerivAt (fun t : ℝ => √(1 + t ^ 2)) (t / √(1 + t ^ 2)) t := by
  have h := ((hasDerivAt_pow 2 t).const_add 1).sqrt (one_add_sq_pos t).ne'
  refine h.congr_deriv ?_
  have := sqrt_one_add_sq_pos t
  field_simp
  ring

theorem hasDerivAt_exp_mul_arsinh (θ t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (θ * Real.arsinh t))
      (θ / √(1 + t ^ 2) * Real.exp (θ * Real.arsinh t)) t := by
  have h := ((Real.hasDerivAt_arsinh t).const_mul θ).exp
  refine h.congr_deriv ?_
  rw [div_eq_mul_inv]
  ring

theorem hasDerivAt_expProfile (θ t : ℝ) :
    HasDerivAt (expProfile θ) (expProfile' θ t) t := by
  have h := (hasDerivAt_sqrt_one_add_sq t).mul (hasDerivAt_exp_mul_arsinh θ t)
  refine h.congr_deriv ?_
  have := sqrt_one_add_sq_pos t
  simp only [expProfile']
  field_simp

theorem hasDerivAt_expProfile' (θ t : ℝ) :
    HasDerivAt (expProfile' θ) (expProfile'' θ t) t := by
  have hs := sqrt_one_add_sq_pos t
  have hd : HasDerivAt (fun t : ℝ => t / √(1 + t ^ 2))
      (1 / √(1 + t ^ 2) ^ 3) t := by
    have h := (hasDerivAt_id t).div (hasDerivAt_sqrt_one_add_sq t) hs.ne'
    refine h.congr_deriv ?_
    have h2 := sq_sqrt_one_add_sq t
    simp only [id]
    field_simp
    rw [h2]
    ring
  have h := (hd.add_const θ).mul (hasDerivAt_exp_mul_arsinh θ t)
  refine h.congr_deriv ?_
  have h2 := sq_sqrt_one_add_sq t
  simp only [expProfile'']
  set s := √(1 + t ^ 2) with hs_def
  rw [← h2]
  field_simp
  ring

theorem deriv_expProfile (θ : ℝ) : deriv (expProfile θ) = expProfile' θ :=
  funext fun t => (hasDerivAt_expProfile θ t).deriv

theorem contDiff_expProfile (θ : ℝ) : ContDiff ℝ 3 (expProfile θ) := by
  have h1 : ContDiff ℝ 3 (fun t : ℝ => √(1 + t ^ 2)) :=
    (contDiff_const.add (contDiff_id.pow 2)).sqrt fun t => (one_add_sq_pos t).ne'
  have h2 : ContDiff ℝ 3 (fun t : ℝ => Real.exp (θ * Real.arsinh t)) :=
    Real.contDiff_exp.comp (contDiff_const.mul Real.contDiff_arsinh)
  exact h1.mul h2

/-- **The profile ODE.** `4(1+t²) g'' − 4 t g' + (−4θ² + 4(t²−1)/(1+t²)) g = 0`. -/
theorem expProfile_ode (θ t : ℝ) :
    4 * (1 + t ^ 2) * expProfile'' θ t - 4 * t * expProfile' θ t +
      (-4 * θ ^ 2 + 4 * (t ^ 2 - 1) / (1 + t ^ 2)) * expProfile θ t = 0 := by
  have hs := sqrt_one_add_sq_pos t
  have h2 := sq_sqrt_one_add_sq t
  simp only [expProfile, expProfile', expProfile'']
  set s := √(1 + t ^ 2) with hs_def
  rw [← h2]
  field_simp
  ring

/-! ### The test function on the state space -/

/-- The exponential test function `e^{2L} Y^{-2θ²} g_θ(X / Y) = Φ² cosh J e^{θ J - 2 θ² log Y}` on the
state space `(Z, L) ∈ ℂ × ℝ`, `Z = X + iY`. -/
def expTest (θ : ℝ) (x : ℂ × ℝ) : ℝ :=
  Real.exp (2 * x.2) * x.1.im ^ (-2 * θ ^ 2) * expProfile θ (x.1.re / x.1.im)

theorem expTest_line (θ : ℝ) (x v : ℂ × ℝ) (s : ℝ) :
    expTest θ (x + s • v) = Real.exp (2 * (x.2 + s * v.2)) *
      (x.1.im + s * v.1.im) ^ (-2 * θ ^ 2) *
      expProfile θ ((x.1.re + s * v.1.re) / (x.1.im + s * v.1.im)) := by
  simp only [expTest, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]

theorem expProfile_pos (θ t : ℝ) : 0 < expProfile θ t :=
  mul_pos (sqrt_one_add_sq_pos t) (Real.exp_pos _)

theorem expTest_pos (θ : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) : 0 < expTest θ x := by
  unfold expTest
  have := Real.rpow_pos_of_pos hx (-2 * θ ^ 2)
  have := expProfile_pos θ (x.1.re / x.1.im)
  positivity

theorem contDiffOn_expTest (θ : ℝ) : ContDiffOn ℝ 3 (expTest θ) rsDom := by
  have him : ContDiff ℝ 3 (fun x : ℂ × ℝ => x.1.im) :=
    Complex.imCLM.contDiff.comp (contDiff_fst (𝕜 := ℝ) (E := ℂ) (F := ℝ) (n := 3))
  have hre : ContDiff ℝ 3 (fun x : ℂ × ℝ => x.1.re) :=
    Complex.reCLM.contDiff.comp (contDiff_fst (𝕜 := ℝ) (E := ℂ) (F := ℝ) (n := 3))
  have h1 : ContDiff ℝ 3 (fun x : ℂ × ℝ => Real.exp (2 * x.2)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_snd)
  have h2 : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => x.1.im ^ (-2 * θ ^ 2)) rsDom :=
    him.contDiffOn.rpow_const_of_ne fun x hx => ne_of_gt hx
  have h3 : ContDiffOn ℝ 3 (fun x : ℂ × ℝ => expProfile θ (x.1.re / x.1.im)) rsDom :=
    (contDiff_expProfile θ).comp_contDiffOn
      (hre.contDiffOn.div him.contDiffOn fun x hx => ne_of_gt hx)
  exact (h1.contDiffOn.mul h2).mul h3

/-- First derivative of the test function along a line, in real coordinates. -/
theorem hasDerivAt_expTestAux1 (θ L X Y m a c : ℝ) (hY : 0 < Y) :
    HasDerivAt (fun s : ℝ => Real.exp (2 * (L + s * m)) * (Y + s * c) ^ (-2 * θ ^ 2) *
        expProfile θ ((X + s * a) / (Y + s * c)))
      (Real.exp (2 * L) * Y ^ (-2 * θ ^ 2) *
        (expProfile θ (X / Y) * (2 * m + (-2 * θ ^ 2) * c / Y) +
          expProfile' θ (X / Y) * ((a * Y - X * c) / Y ^ 2))) 0 := by
  have h1 := ((((hasDerivAt_id' (0 : ℝ)).mul_const m).const_add L).const_mul 2).exp
  have h2 := (((hasDerivAt_id' (0 : ℝ)).mul_const c).const_add Y).rpow_const
    (p := -2 * θ ^ 2) (Or.inl (by simpa using hY.ne'))
  have hq : HasDerivAt (fun s : ℝ => (X + s * a) / (Y + s * c)) ((a * Y - X * c) / Y ^ 2) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add X).div
      (((hasDerivAt_id' (0 : ℝ)).mul_const c).const_add Y) (by simpa using hY.ne')
    refine this.congr_deriv ?_
    simp
  have h3 : HasDerivAt (fun s : ℝ => expProfile θ ((X + s * a) / (Y + s * c)))
      (expProfile' θ (X / Y) * ((a * Y - X * c) / Y ^ 2)) 0 := by
    have hpt : (X + 0 * a) / (Y + 0 * c) = X / Y := by simp
    have := (hasDerivAt_expProfile θ ((X + 0 * a) / (Y + 0 * c))).comp (0 : ℝ) hq
    rw [hpt] at this
    exact this
  refine ((h1.fun_mul h2).fun_mul h3 : HasDerivAt (fun s : ℝ => Real.exp (2 * (L + s * m)) *
    (Y + s * c) ^ (-2 * θ ^ 2) * expProfile θ ((X + s * a) / (Y + s * c))) _ 0).congr_deriv ?_
  simp only [zero_mul, add_zero, one_mul]
  rw [Real.rpow_sub_one hY.ne']
  field_simp

/-- Second derivative of the test function along a horizontal line. -/
theorem deriv_deriv_expTestAux2 (θ A X Y a : ℝ) :
    deriv (deriv (fun s : ℝ => A * expProfile θ ((X + s * a) / Y))) 0 =
      A * expProfile'' θ (X / Y) * (a / Y) ^ 2 := by
  have hq : ∀ s : ℝ, HasDerivAt (fun s : ℝ => (X + s * a) / Y) (a / Y) s := fun s => by
    have := (((hasDerivAt_id' s).mul_const a).const_add X).div_const Y
    simpa using this
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => A * expProfile θ ((X + s * a) / Y))
      (A * (expProfile' θ ((X + s * a) / Y) * (a / Y))) s := fun s =>
    ((hasDerivAt_expProfile θ _).comp s (hq s)).const_mul A
  have hderiv : deriv (fun s : ℝ => A * expProfile θ ((X + s * a) / Y)) =
      fun s => A * (expProfile' θ ((X + s * a) / Y) * (a / Y)) :=
    funext fun s => (hd s).deriv
  rw [hderiv]
  have h2 : HasDerivAt (fun s : ℝ => A * (expProfile' θ ((X + s * a) / Y) * (a / Y)))
      (A * (expProfile'' θ ((X + 0 * a) / Y) * (a / Y) * (a / Y))) 0 :=
    (((hasDerivAt_expProfile' θ _).comp (0 : ℝ) (hq 0)).mul_const (a / Y)).const_mul A
  rw [h2.deriv]
  simp only [zero_mul, add_zero]
  ring

/-- **The exponential test function has zero Dynkin generator** for the reverse flow driven by `√8 B`,
where the taming of the drift is inactive. -/
theorem dynkinGen_expTest (θ : ℝ) {y₀ : ℝ} {x : ℂ × ℝ} (hx : 0 < x.1.im) (hy : y₀ ≤ x.1.im) :
    dynkinGen (rsDrift y₀) (rsNoise 8) (expTest θ) x = 0 := by
  have hF : ContDiffAt ℝ 3 (expTest θ) x :=
    (contDiffOn_expTest θ).contDiffAt (isOpen_rsDom.mem_nhds hx)
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line (hF.of_le (by norm_num))]
  have e1 : (fun s : ℝ => expTest θ (x + s • rsDrift y₀ x)) = fun s =>
      Real.exp (2 * (x.2 + s * (rsDrift y₀ x).2)) *
      (x.1.im + s * (rsDrift y₀ x).1.im) ^ (-2 * θ ^ 2) *
      expProfile θ ((x.1.re + s * (rsDrift y₀ x).1.re) / (x.1.im + s * (rsDrift y₀ x).1.im)) :=
    funext fun s => expTest_line θ x _ s
  have e2 : (fun s : ℝ => expTest θ (x + s • rsNoise 8)) = fun s =>
      (Real.exp (2 * x.2) * x.1.im ^ (-2 * θ ^ 2)) *
      expProfile θ ((x.1.re + s * (-Real.sqrt 8)) / x.1.im) := by
    funext s
    rw [expTest_line]
    simp [rsNoise]
  rw [e1, e2, (hasDerivAt_expTestAux1 θ _ _ _ _ _ _ hx).deriv, deriv_deriv_expTestAux2]
  simp only [rsDrift, proj_of_le hy]
  rw [re_two_div_sq]
  simp only [Complex.neg_re, Complex.neg_im, re_two_div, im_two_div]
  have hode := expProfile_ode θ (x.1.re / x.1.im)
  have h8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  set X := x.1.re
  set Y := x.1.im
  set g0 := expProfile θ (X / Y)
  set g1 := expProfile' θ (X / Y)
  set g2 := expProfile'' θ (X / Y)
  have hN : 0 < X ^ 2 + Y ^ 2 := by positivity
  have key : Real.exp (2 * x.2) * Y ^ (-2 * θ ^ 2) *
      (g0 * (2 * (2 * (X ^ 2 - Y ^ 2) / (X ^ 2 + Y ^ 2) ^ 2) +
        -2 * θ ^ 2 * -(-(2 * Y) / (X ^ 2 + Y ^ 2)) / Y) +
        g1 * ((-(2 * X / (X ^ 2 + Y ^ 2)) * Y - X * -(-(2 * Y) / (X ^ 2 + Y ^ 2))) / Y ^ 2)) +
      1 / 2 * (Real.exp (2 * x.2) * Y ^ (-2 * θ ^ 2) * g2 * (-Real.sqrt 8 / Y) ^ 2) =
      Real.exp (2 * x.2) * Y ^ (-2 * θ ^ 2) / (X ^ 2 + Y ^ 2) *
        (4 * (1 + (X / Y) ^ 2) * g2 - 4 * (X / Y) * g1 +
          (-4 * θ ^ 2 + 4 * ((X / Y) ^ 2 - 1) / (1 + (X / Y) ^ 2)) * g0) := by
    rw [div_pow, neg_sq, h8]
    field_simp
    ring
  rw [key, hode, mul_zero]

theorem measurable_expTest (θ : ℝ) : Measurable (expTest θ) := by
  unfold expTest expProfile
  have : Measurable Real.arsinh := Real.continuous_arsinh.measurable
  fun_prop

/-- `expTest θ (Z, L) = cosh J · e^{2L − 2θ² log Y + θ J}` with `J = arsinh (X / Y)`. -/
theorem expTest_eq_exp (θ : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) :
    expTest θ x = √(1 + (x.1.re / x.1.im) ^ 2) *
      Real.exp (2 * x.2 + Real.log x.1.im * (-2 * θ ^ 2) + θ * Real.arsinh (x.1.re / x.1.im)) := by
  simp only [expTest, expProfile]
  rw [Real.rpow_def_of_pos hx, Real.exp_add, Real.exp_add]
  ring

/-! ### Domination by a Rohde–Schramm test function -/

theorem abs_arsinh_le (t : ℝ) : |Real.arsinh t| ≤ Real.log 2 + Real.log (1 + t ^ 2) / 2 := by
  have hs := sqrt_one_add_sq_pos t
  have hle : ∀ u : ℝ, Real.arsinh u ≤ Real.log 2 + Real.log (1 + u ^ 2) / 2 := by
    intro u
    have hsu := sqrt_one_add_sq_pos u
    have h1 : u + √(1 + u ^ 2) ≤ 2 * √(1 + u ^ 2) := by
      have : u ≤ √(1 + u ^ 2) := by
        refine Real.le_sqrt_of_sq_le ?_
        linarith
      linarith
    have h0 : 0 < u + √(1 + u ^ 2) := by
      have := Real.exp_pos (Real.arsinh u)
      rwa [Real.exp_arsinh] at this
    have h2 : Real.arsinh u = Real.log (u + √(1 + u ^ 2)) := by
      rw [← Real.exp_arsinh, Real.log_exp]
    rw [h2, show Real.log (1 + u ^ 2) / 2 = Real.log (√(1 + u ^ 2)) by
      rw [Real.log_sqrt (one_add_sq_pos u).le]]
    rw [← Real.log_mul (by norm_num) hsu.ne']
    exact Real.log_le_log h0 h1
  rw [abs_le]
  refine ⟨?_, hle t⟩
  have := hle (-t)
  rw [Real.arsinh_neg, neg_sq] at this
  linarith

/-- The exponent `p = 2 + 2|θ| + 4θ²` of the domination constant. -/
def domExpP (θ : ℝ) : ℝ := 2 + 2 * |θ| + 4 * θ ^ 2

/-- The exponent `k = 2 + 6|θ|` of the domination constant. -/
def domExpK (θ : ℝ) : ℝ := 2 + 6 * |θ|

/-- The domination constant `4^{|θ|} √5^{p+k} / y^p`. -/
def domConst (θ y : ℝ) : ℝ :=
  Real.exp (|θ| * Real.log 4 + (domExpP θ + domExpK θ) * Real.log (√5) -
    domExpP θ * Real.log y)

theorem domConst_pos (θ y : ℝ) : 0 < domConst θ y := Real.exp_pos _

/-- **Domination.** On `{y ≤ Y ≤ √5, Φ = e^L ≤ Y / y}`,
`expTest θ ² ≤ domConst θ y · rsTest 8 (1 + |θ|)`. -/
theorem expTest_sq_le (θ : ℝ) {y : ℝ} (hy : 0 < y) {x : ℂ × ℝ} (hxy : y ≤ x.1.im)
    (hx5 : x.1.im ≤ √5) (hL : Real.exp x.2 ≤ x.1.im / y) :
    expTest θ x ^ 2 ≤ domConst θ y * rsTest 8 (1 + |θ|) x := by
  obtain ⟨⟨X, Y⟩, L⟩ := x
  simp only at hxy hx5 hL
  have hY : 0 < Y := hy.trans_le hxy
  have hq0 : 0 ≤ |θ| := abs_nonneg θ
  have h1t := one_add_sq_pos (X / Y)
  have hN : X ^ 2 + Y ^ 2 = Y ^ 2 * (1 + (X / Y) ^ 2) := by
    rw [div_pow]
    field_simp
    ring
  have hlogN : Real.log (X ^ 2 + Y ^ 2) = 2 * Real.log Y + Real.log (1 + (X / Y) ^ 2) := by
    rw [hN, Real.log_mul (by positivity) h1t.ne', Real.log_pow]
    push_cast
    ring
  -- logarithmic forms
  have e1 : expTest θ (⟨X, Y⟩, L) = Real.exp (2 * L + Real.log Y * (-2 * θ ^ 2) +
      (Real.log (1 + (X / Y) ^ 2) / 2 + θ * Real.arsinh (X / Y))) := by
    simp only [expTest, expProfile]
    rw [Real.rpow_def_of_pos hY,
      show √(1 + (X / Y) ^ 2) = Real.exp (Real.log (1 + (X / Y) ^ 2) / 2) by
        rw [← Real.log_sqrt h1t.le, Real.exp_log (sqrt_one_add_sq_pos _)]]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  have e2 : rsTest 8 (1 + |θ|) (⟨X, Y⟩, L) = Real.exp (rsLam 8 (1 + |θ|) * L +
      Real.log Y * (rsZeta 8 (1 + |θ|) - 2 * (1 + |θ|)) +
      (2 * Real.log Y + Real.log (1 + (X / Y) ^ 2)) * (1 + |θ|)) := by
    simp only [rsTest]
    rw [Real.rpow_def_of_pos hY, Real.rpow_def_of_pos (by positivity : (0 : ℝ) < X ^ 2 + Y ^ 2),
      hlogN, ← Real.exp_add, ← Real.exp_add]
  rw [e1, e2, domConst, ← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  -- the linear inequality
  have hB : θ * Real.arsinh (X / Y) ≤ |θ| * (Real.log 2 + Real.log (1 + (X / Y) ^ 2) / 2) := by
    calc θ * Real.arsinh (X / Y) ≤ |θ * Real.arsinh (X / Y)| := le_abs_self _
      _ = |θ| * |Real.arsinh (X / Y)| := by rw [abs_mul]
      _ ≤ |θ| * (Real.log 2 + Real.log (1 + (X / Y) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (abs_arsinh_le _) hq0
  have hL' : L + Real.log y ≤ Real.log Y := by
    have := Real.log_le_log (Real.exp_pos L) hL
    rw [Real.log_exp, Real.log_div hY.ne' hy.ne'] at this
    linarith
  have hw5 : Real.log Y ≤ Real.log (√5) := Real.log_le_log hY hx5
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hp0 : 0 ≤ domExpP θ := by unfold domExpP; positivity
  have hk0 : 0 ≤ domExpK θ := by unfold domExpK; positivity
  have h1 : domExpP θ * (L + Real.log y) ≤ domExpP θ * Real.log (√5) :=
    mul_le_mul_of_nonneg_left (hL'.trans hw5) hp0
  have h2 : domExpK θ * Real.log Y ≤ domExpK θ * Real.log (√5) :=
    mul_le_mul_of_nonneg_left hw5 hk0
  have hθ2 : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
  simp only [rsLam, rsZeta, domExpP, domExpK] at h1 h2 ⊢
  rw [hlog4]
  rw [hθ2] at h1 ⊢
  push_cast
  nlinarith [hB]

end InteractingSLE.SLE8.ChangeOfMeasure
