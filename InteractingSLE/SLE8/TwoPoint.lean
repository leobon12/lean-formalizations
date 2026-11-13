import QuantumZipper.Proofs.RS.MartingaleBound
import QuantumZipper.Proofs.Probability.Girsanov.Generator
import QuantumZipper.Proofs.RS.TransienceCanon
import InteractingSLE.SLE8.TimeGrid

/-!
# Two-point derivatives (SLE₈ note, Lemma 3.2)

SLE₈ note `source/sle8-continuity.pdf`, §3.2, p. 6 (transcription `source/sle8/sle8-continuity.md`,
anchors `lem-3.2`, `lem-3.2-proof`).

## Main result

* `exists_measure_twoPoint_deriv_le` — **Lemma 3.2**, (3.11): for every `M` and `c₀ > 0` there is a
  deterministic `C_{M,c₀}` (independent of the probability space and of the Brownian motion) such that
  for deterministic `t ∈ [0,1]`, `a ∈ (0,1)`, `y ∈ (0,1]`, `v ∈ (0, y/2]`, `m ∈ ℤ` with `|m| v ≤ 1`,
  `P[Ω_M ∩ {y|F_t'(iy)| ≥ a, v|F_t'((m+i)v)| ≥ c₀ a}] ≤ C a^{-26/9} y² (v/y)^{16/9} (1+m²)^{1/3}`.
  The note fixes `M ∈ ℕ`; the statement holds for every real `M`.
* `measure_twoPoint_deriv_le` — the same bound with the explicit constant
  `TwoPointDeriv.twoPointConst M c₀`, for a given Brownian motion.
* `TwoPointDeriv.lintegral_tpForm_le` — `E 𝒩_T ≤ 𝒩_0` for the two-point process (3.16) of the
  reverse flow driven by `√8 B`, for every deterministic `T ≥ 0` and distinct `z₁, z₂ ∈ ℍ`.

## Carriers

`W = √8 B` is `drive 8 B ω`, `F_t = fwdMapInv W t`, and `Ω_M` is `DriverBound M W` (file `TimeGrid`).
The reverse flow from two points `z₁ ≠ z₂` is the state `((u₁, L₁), (u₂, L₂)) ∈ (ℂ × ℝ) × (ℂ × ℝ)`
(`TwoPointDeriv.TPState`, `TwoPointDeriv.tpProc`), with `u_j = Z_s(z_j)` (`revMap`) and
`L_j = log Φ_j`; each coordinate is QuantumZipper's one-point state `RS.rsProc`. QuantumZipper's
`RS.rsTest 8 b (u, L) = e^{ρ(b) L} Y^{λ(b) - ρ(b) - 2b} (X² + Y²)^b` is the one-point factor (3.13)
(`RS.rsLam 8 b = 6b - 4b² = ρ(b)`, `RS.rsZeta 8 b = 2b - 4b² = λ(b) - ρ(b)`), and
`TwoPointDeriv.tpTest = rsTest 8 (1/6) · rsTest 8 (1/3) · crossFactor`, with
`crossFactor u w = (|u - w|² |u - w̄|²)^{-2/9}`, is the two-point process (3.16) as a function of
the state; `TwoPointDeriv.tpForm` is the same quantity written with `Φ_j = |h_T'(z_j)|`, and
`TwoPointDeriv.tpForm_eq` rewrites it in exactly the printed form of (3.16).

## Proof (the note's, with QuantumZipper's Itô-free Dynkin formula in place of Itô's formula)

1. `TwoPointDeriv.dynkinGen_tpTest` (the drift computation (3.14)–(3.16)): by the product rule for
   the generator (`Girsanov.dynkinGen_mul`), `L(G₁ G₂ H) = G₁ G₂ L H + H (DG₁·e)(DG₂·e)`, because
   `L G_j = 0` is the one-point computation (3.14) (`RS.dynkinGen_rsTest`) and `H` is constant along
   the common noise `e` (the Brownian terms cancel in `Z₁ - Z₂` and `Z₁ - Z̄₂`). The drift of
   `log(|Z₁ - Z₂|² |Z₁ - Z̄₂|²)` is `8 X₁X₂/(|Z₁|²|Z₂|²)` ((3.15)), and the cross term of the one-point
   factors is `32 b₁ b₂ X₁X₂/(|Z₁|²|Z₂|²)`; with `8 b₁ b₂ = 4/9` they cancel (`TwoPointDeriv.tp_alg`).
2. `TwoPointDeriv.tp_core`, `TwoPointDeriv.lintegral_tpForm_le` (`E 𝒩_T ≤ 𝒩_0`): the local Dynkin
   formula with stopping (`FrozenMart.martingale_localDynkin_stopped`) on the compact regions
   `TwoPointDeriv.tpRegion`, which the state does not leave before it exits a large ball: heights
   `Y_j ≥ Im z_j` ((2.8)), separation `|Z₁ - Z₂|² Y₁ Y₂ ≥ |z₁ - z₂|² Im z₁ Im z₂`
   (`TwoPoint.twoPoint_lower_sq`; the denominators of (3.16) never vanish), `|L_j| ≤ 2T/(Im z_j)²`.
   Then `E 𝒩_{T ∧ τ_n} = 𝒩_0`, and Fatou's lemma as `n → ∞` gives `E 𝒩_T ≤ 𝒩_0`. This replaces the
   note's "positive local martingale, hence `E 𝒩_t ≤ 𝒩_0`" by the same localization argument.
3. (3.17): `TwoPointDeriv.tpTest_init_le`.
4. (3.18): `TwoPointDeriv.tpLower_le_tpForm`. The note's reverse flow `V_s = W_{t-s} - W_t` is driven
   by the reversed Brownian motion `UnzipInvariance.revBM B t` (a Brownian motion,
   `UnzipInvariance.isBrownianReal_revBM`; same reverse map at time `t`,
   `UnzipInvariance.revMap_timeRev_eq_drive_revBM`). On `Ω_M`, `|V_s| ≤ 2M`, so Lemma 2.2
   (`abs_re_revMap_le`, `TwoPoint.im_revMap_sq_le`, `TwoPoint.norm_deriv_revMap_le`) bounds
   `|X_t(z_j)| ≤ max 1 (2M) + 2M`, `Y_t(z_j)² ≤ 5`, and gives `Y₁ ≥ a`, `Y₂ ≥ c₀ a` on the event; the
   derivative identity (2.7) at `s = t` is `norm_deriv_fwdMapInv_eq_norm_deriv_revFlow`.
5. Markov's inequality (`TwoPointDeriv.measure_le_ofReal_div_of_subset`) and the exponent bookkeeping
   (`TwoPointDeriv.final_identity`). The constant is `TwoPointDeriv.twoPointConst M c₀ =
   4^{2/9} ((4ξ² + 20)²)^{2/9} / c₀^{16/9}`, `ξ = max 1 (2M) + 2M`.
-/
noncomputable section

open Set Filter Topology

universe u

namespace InteractingSLE.SLE8

namespace TwoPointDeriv

open QuantumZipper RS FwdHolo FrozenMart

/-- Line derivative of a function of the first coordinate. -/
theorem lineDeriv_comp_fst {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (F : E₁ → ℝ) (x v : E₁ × E₂) :
    (fun s : ℝ => F (x + s • v).1) = fun s => F (x.1 + s • v.1) := by
  funext s; simp only [Prod.fst_add, Prod.smul_fst]

theorem lineDeriv_comp_snd {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (F : E₂ → ℝ) (x v : E₁ × E₂) :
    (fun s : ℝ => F (x + s • v).2) = fun s => F (x.2 + s • v.2) := by
  funext s; simp only [Prod.snd_add, Prod.smul_snd]

theorem fderiv_comp_fst_apply {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {F : E₁ → ℝ} {x : E₁ × E₂}
    (hF : DifferentiableAt ℝ F x.1) (v : E₁ × E₂) :
    fderiv ℝ (fun y : E₁ × E₂ => F y.1) x v = fderiv ℝ F x.1 v.1 := by
  have hc : DifferentiableAt ℝ (fun y : E₁ × E₂ => F y.1) x := hF.comp x differentiableAt_fst
  rw [fderiv_apply_eq_deriv_line hc, fderiv_apply_eq_deriv_line hF]
  exact congrArg (fun f => deriv f 0) (lineDeriv_comp_fst F x v)

theorem fderiv_comp_snd_apply {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {F : E₂ → ℝ} {x : E₁ × E₂}
    (hF : DifferentiableAt ℝ F x.2) (v : E₁ × E₂) :
    fderiv ℝ (fun y : E₁ × E₂ => F y.2) x v = fderiv ℝ F x.2 v.2 := by
  have hc : DifferentiableAt ℝ (fun y : E₁ × E₂ => F y.2) x := hF.comp x differentiableAt_snd
  rw [fderiv_apply_eq_deriv_line hc, fderiv_apply_eq_deriv_line hF]
  exact congrArg (fun f => deriv f 0) (lineDeriv_comp_snd F x v)

theorem dynkinGen_comp_fst {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {F : E₁ → ℝ} {x : E₁ × E₂}
    (hF : ContDiffAt ℝ 2 F x.1) (b : E₁ × E₂ → E₁ × E₂) (b₁ : E₁ → E₁) (hb : (b x).1 = b₁ x.1)
    (e : E₁ × E₂) :
    dynkinGen b e (fun y : E₁ × E₂ => F y.1) x = dynkinGen b₁ e.1 F x.1 := by
  have hc : ContDiffAt ℝ 2 (fun y : E₁ × E₂ => F y.1) x := hF.comp x contDiffAt_fst
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hc.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line hc, fderiv_apply_eq_deriv_line
    (hF.differentiableAt (by norm_num)), iteratedFDeriv_two_eq_deriv_deriv_line hF,
    lineDeriv_comp_fst, lineDeriv_comp_fst, hb]

theorem dynkinGen_comp_snd {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] {F : E₂ → ℝ} {x : E₁ × E₂}
    (hF : ContDiffAt ℝ 2 F x.2) (b : E₁ × E₂ → E₁ × E₂) (b₂ : E₂ → E₂) (hb : (b x).2 = b₂ x.2)
    (e : E₁ × E₂) :
    dynkinGen b e (fun y : E₁ × E₂ => F y.2) x = dynkinGen b₂ e.2 F x.2 := by
  have hc : ContDiffAt ℝ 2 (fun y : E₁ × E₂ => F y.2) x := hF.comp x contDiffAt_snd
  unfold dynkinGen
  rw [fderiv_apply_eq_deriv_line (hc.differentiableAt (by norm_num)),
    iteratedFDeriv_two_eq_deriv_deriv_line hc, fderiv_apply_eq_deriv_line
    (hF.differentiableAt (by norm_num)), iteratedFDeriv_two_eq_deriv_deriv_line hF,
    lineDeriv_comp_snd, lineDeriv_comp_snd, hb]

/-- The directional derivative of the Rohde–Schramm test function. -/
theorem fderiv_rsTest_apply (κ r : ℝ) {x : ℂ × ℝ} (hx : 0 < x.1.im) (v : ℂ × ℝ) :
    fderiv ℝ (rsTest κ r) x v = rsTest κ r x * (rsLam κ r * v.2 +
      (rsZeta κ r - 2 * r) * v.1.im / x.1.im +
      r * (2 * x.1.re * v.1.re + 2 * x.1.im * v.1.im) / (x.1.re ^ 2 + x.1.im ^ 2)) := by
  have hF : ContDiffAt ℝ 3 (rsTest κ r) x :=
    (contDiffOn_rsTest κ r).contDiffAt (isOpen_rsDom.mem_nhds hx)
  rw [fderiv_apply_eq_deriv_line (hF.differentiableAt (by norm_num))]
  have e1 : (fun s : ℝ => rsTest κ r (x + s • v)) = fun s =>
      Real.exp (rsLam κ r * (x.2 + s * v.2)) * (x.1.im + s * v.1.im) ^ (rsZeta κ r - 2 * r) *
      ((x.1.re + s * v.1.re) ^ 2 + (x.1.im + s * v.1.im) ^ 2) ^ r :=
    funext fun s => rsTest_line κ r x v s
  rw [e1, (hasDerivAt_rsAux1 _ _ _ _ _ _ _ _ _ hx).deriv]
  rfl


/-! ## The cross factor -/

/-- `(|u - w|² |u - w̄|²)^{-2/9}` in real coordinates. -/
def crossFactor (u w : ℂ) : ℝ :=
  (((u.re - w.re) ^ 2 + (u.im - w.im) ^ 2) * ((u.re - w.re) ^ 2 + (u.im + w.im) ^ 2)) ^ (-(2 / 9 : ℝ))

theorem hasDerivAt_crossAux (A B C a b c p : ℝ) (h1 : 0 < A ^ 2 + B ^ 2) (h2 : 0 < A ^ 2 + C ^ 2) :
    HasDerivAt (fun s : ℝ => (((A + s * a) ^ 2 + (B + s * b) ^ 2) *
        ((A + s * a) ^ 2 + (C + s * c) ^ 2)) ^ p)
      (((A ^ 2 + B ^ 2) * (A ^ 2 + C ^ 2)) ^ p * p *
        ((2 * A * a + 2 * B * b) / (A ^ 2 + B ^ 2) + (2 * A * a + 2 * C * c) / (A ^ 2 + C ^ 2))) 0 := by
  have hA := ((hasDerivAt_id' (0 : ℝ)).mul_const a).const_add A
  have hB := ((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add B
  have hC := ((hasDerivAt_id' (0 : ℝ)).mul_const c).const_add C
  have hP := ((hA.fun_pow 2).fun_add (hB.fun_pow 2)).fun_mul ((hA.fun_pow 2).fun_add (hC.fun_pow 2))
  have hpos : (A + 0 * a) ^ 2 + (B + 0 * b) ^ 2 ≠ 0 ∧ (A + 0 * a) ^ 2 + (C + 0 * c) ^ 2 ≠ 0 := by
    simp only [zero_mul, add_zero]; exact ⟨h1.ne', h2.ne'⟩
  have h := hP.rpow_const (p := p) (Or.inl (mul_ne_zero hpos.1 hpos.2))
  refine (h : HasDerivAt (fun s : ℝ => (((A + s * a) ^ 2 + (B + s * b) ^ 2) *
        ((A + s * a) ^ 2 + (C + s * c) ^ 2)) ^ p) _ 0).congr_deriv ?_
  simp only [zero_mul, add_zero, one_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [Real.rpow_sub_one (mul_ne_zero h1.ne' h2.ne')]
  field_simp

theorem crossFactor_line (u w p q : ℂ) (s : ℝ) :
    crossFactor (u + s • p) (w + s • q) =
      ((((u.re - w.re) + s * (p.re - q.re)) ^ 2 + ((u.im - w.im) + s * (p.im - q.im)) ^ 2) *
        (((u.re - w.re) + s * (p.re - q.re)) ^ 2 + ((u.im + w.im) + s * (p.im + q.im)) ^ 2)) ^
        (-(2 / 9 : ℝ)) := by
  simp only [crossFactor, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul]
  ring_nf


/-! ## The two-point state, drift, noise and test function -/

/-- The two-point state `((u₁, L₁), (u₂, L₂))`, with `u_j` the reverse flow from `z_j` and
`L_j = log |h_s'(z_j)|`. -/
abbrev TPState := (ℂ × ℝ) × (ℂ × ℝ)

/-- The (tamed) two-point drift: the one-point drift in each coordinate. -/
def tpDrift (y₁ y₂ : ℝ) (x : TPState) : TPState := (rsDrift y₁ x.1, rsDrift y₂ x.2)

/-- The two-point noise vector: both points are driven by the same Brownian motion, `W = √8 B`. -/
def tpNoise : TPState := (rsNoise 8, rsNoise 8)

/-- The two-point test function (3.16): the product of the one-point factors (3.13) for
`b₁ = 1/6`, `b₂ = 1/3` and the cross factor `(|Z₁ - Z₂| |Z₁ - Z̄₂|)^{-4/9}`. -/
def tpTest (x : TPState) : ℝ := rsTest 8 (1 / 6) x.1 * rsTest 8 (1 / 3) x.2 * crossFactor x.1.1 x.2.1

/-- The open set where the two-point test function is smooth. -/
def tpDom : Set TPState := {x | 0 < x.1.1.im ∧ 0 < x.2.1.im ∧ x.1.1 ≠ x.2.1}

theorem sq_add_sq_sub_pos {u w : ℂ} (h : u ≠ w) : 0 < (u.re - w.re) ^ 2 + (u.im - w.im) ^ 2 := by
  have := Complex.normSq_pos.2 (sub_ne_zero.2 h)
  rw [Complex.normSq_apply] at this
  simp only [Complex.sub_re, Complex.sub_im] at this
  nlinarith

theorem sq_add_sq_add_pos {u w : ℂ} (hu : 0 < u.im) (hw : 0 < w.im) :
    0 < (u.re - w.re) ^ 2 + (u.im + w.im) ^ 2 := by positivity

theorem isOpen_tpDom : IsOpen tpDom := by
  have h1 : Continuous fun x : TPState => x.1.1 := continuous_fst.comp continuous_fst
  have h2 : Continuous fun x : TPState => x.2.1 := continuous_fst.comp continuous_snd
  refine (isOpen_lt continuous_const (Complex.continuous_im.comp h1)).inter
    ((isOpen_lt continuous_const (Complex.continuous_im.comp h2)).inter ?_)
  exact isOpen_ne_fun h1 h2

theorem contDiff_coord : ContDiff ℝ 3 (fun x : TPState => x.1.1.re) ∧
    ContDiff ℝ 3 (fun x : TPState => x.1.1.im) ∧ ContDiff ℝ 3 (fun x : TPState => x.2.1.re) ∧
    ContDiff ℝ 3 (fun x : TPState => x.2.1.im) :=
  ⟨Complex.reCLM.contDiff.comp (contDiff_fst.comp contDiff_fst),
    Complex.imCLM.contDiff.comp (contDiff_fst.comp contDiff_fst),
    Complex.reCLM.contDiff.comp (contDiff_fst.comp contDiff_snd),
    Complex.imCLM.contDiff.comp (contDiff_fst.comp contDiff_snd)⟩

theorem contDiffOn_crossFactor :
    ContDiffOn ℝ 3 (fun x : TPState => crossFactor x.1.1 x.2.1) tpDom := by
  obtain ⟨h1, h2, h3, h4⟩ := contDiff_coord
  have hP : ContDiff ℝ 3 (fun x : TPState =>
      ((x.1.1.re - x.2.1.re) ^ 2 + (x.1.1.im - x.2.1.im) ^ 2) *
        ((x.1.1.re - x.2.1.re) ^ 2 + (x.1.1.im + x.2.1.im) ^ 2)) :=
    ((((h1.sub h3).pow 2).add ((h2.sub h4).pow 2)).mul (((h1.sub h3).pow 2).add ((h2.add h4).pow 2)))
  exact hP.contDiffOn.rpow_const_of_ne fun x hx =>
    (mul_pos (sq_add_sq_sub_pos hx.2.2) (sq_add_sq_add_pos hx.1 hx.2.1)).ne'

theorem contDiffOn_rsTest_fst (r : ℝ) :
    ContDiffOn ℝ 3 (fun x : TPState => rsTest 8 r x.1) tpDom :=
  (contDiffOn_rsTest 8 r).comp contDiff_fst.contDiffOn fun _ hx => hx.1

theorem contDiffOn_rsTest_snd (r : ℝ) :
    ContDiffOn ℝ 3 (fun x : TPState => rsTest 8 r x.2) tpDom :=
  (contDiffOn_rsTest 8 r).comp contDiff_snd.contDiffOn fun _ hx => hx.2.1

theorem contDiffOn_tpTest : ContDiffOn ℝ 3 tpTest tpDom :=
  ((contDiffOn_rsTest_fst _).mul (contDiffOn_rsTest_snd _)).mul contDiffOn_crossFactor


theorem fderiv_crossFactor_apply {x : TPState} (hx : x ∈ tpDom) (v : TPState) :
    fderiv ℝ (fun y : TPState => crossFactor y.1.1 y.2.1) x v = crossFactor x.1.1 x.2.1 *
      (-(2 / 9 : ℝ)) *
      ((2 * (x.1.1.re - x.2.1.re) * (v.1.1.re - v.2.1.re) +
          2 * (x.1.1.im - x.2.1.im) * (v.1.1.im - v.2.1.im)) /
          ((x.1.1.re - x.2.1.re) ^ 2 + (x.1.1.im - x.2.1.im) ^ 2) +
        (2 * (x.1.1.re - x.2.1.re) * (v.1.1.re - v.2.1.re) +
          2 * (x.1.1.im + x.2.1.im) * (v.1.1.im + v.2.1.im)) /
          ((x.1.1.re - x.2.1.re) ^ 2 + (x.1.1.im + x.2.1.im) ^ 2)) := by
  have hd : DifferentiableAt ℝ (fun y : TPState => crossFactor y.1.1 y.2.1) x :=
    ((contDiffOn_crossFactor.contDiffAt (isOpen_tpDom.mem_nhds hx)).differentiableAt (by norm_num))
  rw [fderiv_apply_eq_deriv_line hd]
  have e1 : (fun s : ℝ => crossFactor (x + s • v).1.1 (x + s • v).2.1) = fun s =>
      ((((x.1.1.re - x.2.1.re) + s * (v.1.1.re - v.2.1.re)) ^ 2 +
          ((x.1.1.im - x.2.1.im) + s * (v.1.1.im - v.2.1.im)) ^ 2) *
        (((x.1.1.re - x.2.1.re) + s * (v.1.1.re - v.2.1.re)) ^ 2 +
          ((x.1.1.im + x.2.1.im) + s * (v.1.1.im + v.2.1.im)) ^ 2)) ^ (-(2 / 9 : ℝ)) :=
    funext fun s => crossFactor_line x.1.1 x.2.1 v.1.1 v.2.1 s
  rw [e1, (hasDerivAt_crossAux _ _ _ _ _ _ _ (sq_add_sq_sub_pos hx.2.2)
    (sq_add_sq_add_pos hx.1 hx.2.1)).deriv]
  rfl

theorem crossFactor_line_tpNoise (x : TPState) (r : ℝ) :
    crossFactor (x + r • tpNoise).1.1 (x + r • tpNoise).2.1 = crossFactor x.1.1 x.2.1 := by
  simp only [crossFactor, tpNoise, rsNoise, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul]
  congr 1
  ring


/-- The algebra of the cross-drift cancellation (3.15): with `N_j = X_j² + Y_j²`, the drift of
`log(|Z₁ - Z₂|² |Z₁ - Z̄₂|²)` is `8 X₁ X₂ / (N₁ N₂)`, and `-(2/9)` of it cancels the cross term
`(1/6)(1/3) (2 X₁ k)(2 X₂ k) / (N₁ N₂)` of the one-point factors when `k² = 8`. -/
theorem tp_alg (X₁ Y₁ X₂ Y₂ k : ℝ) (hk : k ^ 2 = 8) (hN₁ : 0 < X₁ ^ 2 + Y₁ ^ 2)
    (hN₂ : 0 < X₂ ^ 2 + Y₂ ^ 2) (hD₁ : 0 < (X₁ - X₂) ^ 2 + (Y₁ - Y₂) ^ 2)
    (hD₂ : 0 < (X₁ - X₂) ^ 2 + (Y₁ + Y₂) ^ 2) :
    -(2 / 9) * ((2 * (X₁ - X₂) * (-(2 * X₁ / (X₁ ^ 2 + Y₁ ^ 2)) - -(2 * X₂ / (X₂ ^ 2 + Y₂ ^ 2))) +
          2 * (Y₁ - Y₂) * (-(-(2 * Y₁) / (X₁ ^ 2 + Y₁ ^ 2)) - -(-(2 * Y₂) / (X₂ ^ 2 + Y₂ ^ 2)))) /
          ((X₁ - X₂) ^ 2 + (Y₁ - Y₂) ^ 2) +
        (2 * (X₁ - X₂) * (-(2 * X₁ / (X₁ ^ 2 + Y₁ ^ 2)) - -(2 * X₂ / (X₂ ^ 2 + Y₂ ^ 2))) +
          2 * (Y₁ + Y₂) * (-(-(2 * Y₁) / (X₁ ^ 2 + Y₁ ^ 2)) + -(-(2 * Y₂) / (X₂ ^ 2 + Y₂ ^ 2)))) /
          ((X₁ - X₂) ^ 2 + (Y₁ + Y₂) ^ 2)) +
      1 / 6 * (2 * X₁ * -k) / (X₁ ^ 2 + Y₁ ^ 2) * (1 / 3 * (2 * X₂ * -k) / (X₂ ^ 2 + Y₂ ^ 2)) = 0 := by
  have e1 : (2 * (X₁ - X₂) * (-(2 * X₁ / (X₁ ^ 2 + Y₁ ^ 2)) - -(2 * X₂ / (X₂ ^ 2 + Y₂ ^ 2))) +
      2 * (Y₁ - Y₂) * (-(-(2 * Y₁) / (X₁ ^ 2 + Y₁ ^ 2)) - -(-(2 * Y₂) / (X₂ ^ 2 + Y₂ ^ 2)))) /
      ((X₁ - X₂) ^ 2 + (Y₁ - Y₂) ^ 2) =
      4 * (X₁ * X₂ - Y₁ * Y₂) / ((X₁ ^ 2 + Y₁ ^ 2) * (X₂ ^ 2 + Y₂ ^ 2)) := by
    field_simp
    ring
  have e2 : (2 * (X₁ - X₂) * (-(2 * X₁ / (X₁ ^ 2 + Y₁ ^ 2)) - -(2 * X₂ / (X₂ ^ 2 + Y₂ ^ 2))) +
      2 * (Y₁ + Y₂) * (-(-(2 * Y₁) / (X₁ ^ 2 + Y₁ ^ 2)) + -(-(2 * Y₂) / (X₂ ^ 2 + Y₂ ^ 2)))) /
      ((X₁ - X₂) ^ 2 + (Y₁ + Y₂) ^ 2) =
      4 * (X₁ * X₂ + Y₁ * Y₂) / ((X₁ ^ 2 + Y₁ ^ 2) * (X₂ ^ 2 + Y₂ ^ 2)) := by
    field_simp
    ring
  rw [e1, e2, show 1 / 6 * (2 * X₁ * -k) / (X₁ ^ 2 + Y₁ ^ 2) * (1 / 3 * (2 * X₂ * -k) /
    (X₂ ^ 2 + Y₂ ^ 2)) = 2 / 9 * X₁ * X₂ * k ^ 2 / ((X₁ ^ 2 + Y₁ ^ 2) * (X₂ ^ 2 + Y₂ ^ 2)) by
    field_simp; ring, hk]
  field_simp
  ring

/-- **The two-point test function has zero Dynkin generator** (the cross-drift cancellation
(3.15), `8 b₁ b₂ = 4/9`), where the taming of the drift is inactive. -/
theorem dynkinGen_tpTest {y₁ y₂ : ℝ} {x : TPState} (hx : x ∈ tpDom) (h1 : y₁ ≤ x.1.1.im)
    (h2 : y₂ ≤ x.2.1.im) : dynkinGen (tpDrift y₁ y₂) tpNoise tpTest x = 0 := by
  set G₁ : TPState → ℝ := fun y => rsTest 8 (1 / 6) y.1 with hG₁
  set G₂ : TPState → ℝ := fun y => rsTest 8 (1 / 3) y.2 with hG₂
  set H : TPState → ℝ := fun y => crossFactor y.1.1 y.2.1 with hH
  have htp : tpTest = G₁ * G₂ * H := rfl
  have hO : tpDom ∈ 𝓝 x := isOpen_tpDom.mem_nhds hx
  have hc₁ : ContDiffAt ℝ 2 G₁ x := ((contDiffOn_rsTest_fst _).contDiffAt hO).of_le (by norm_num)
  have hc₂ : ContDiffAt ℝ 2 G₂ x := ((contDiffOn_rsTest_snd _).contDiffAt hO).of_le (by norm_num)
  have hc₁₂ : ContDiffAt ℝ 2 (G₁ * G₂) x := hc₁.mul hc₂
  have hcH : ContDiffAt ℝ 2 H x := (contDiffOn_crossFactor.contDiffAt hO).of_le (by norm_num)
  have hr₁ : ContDiffAt ℝ 2 (rsTest 8 (1 / 6)) x.1 :=
    ((contDiffOn_rsTest 8 _).contDiffAt (isOpen_rsDom.mem_nhds hx.1)).of_le (by norm_num)
  have hr₂ : ContDiffAt ℝ 2 (rsTest 8 (1 / 3)) x.2 :=
    ((contDiffOn_rsTest 8 _).contDiffAt (isOpen_rsDom.mem_nhds hx.2.1)).of_le (by norm_num)
  have hgen₁ : dynkinGen (tpDrift y₁ y₂) tpNoise G₁ x = 0 := by
    rw [hG₁, dynkinGen_comp_fst hr₁ (tpDrift y₁ y₂) (rsDrift y₁) rfl tpNoise]
    exact dynkinGen_rsTest (by norm_num) _ hx.1 h1
  have hgen₂ : dynkinGen (tpDrift y₁ y₂) tpNoise G₂ x = 0 := by
    rw [hG₂, dynkinGen_comp_snd hr₂ (tpDrift y₁ y₂) (rsDrift y₂) rfl tpNoise]
    exact dynkinGen_rsTest (by norm_num) _ hx.2.1 h2
  have hline : (fun s : ℝ => H (x + s • tpNoise)) = fun _ => H x :=
    funext fun s => crossFactor_line_tpNoise x s
  have hHe : fderiv ℝ H x tpNoise = 0 := by
    rw [fderiv_apply_eq_deriv_line (hcH.differentiableAt (by norm_num)), hline, deriv_const]
  have hHee : iteratedFDeriv ℝ 2 H x ![tpNoise, tpNoise] = 0 := by
    rw [iteratedFDeriv_two_eq_deriv_deriv_line hcH, hline]
    simp
  have hgenH : dynkinGen (tpDrift y₁ y₂) tpNoise H x = fderiv ℝ H x (tpDrift y₁ y₂ x) := by
    unfold dynkinGen; rw [hHee]; ring
  rw [htp, Girsanov.dynkinGen_mul hc₁₂ hcH, Girsanov.dynkinGen_mul hc₁ hc₂, hgen₁, hgen₂, hHe,
    hgenH, hG₁, hG₂, hH, fderiv_comp_fst_apply (hr₁.differentiableAt (by norm_num)),
    fderiv_comp_snd_apply (hr₂.differentiableAt (by norm_num)), fderiv_rsTest_apply 8 _ hx.1,
    fderiv_rsTest_apply 8 _ hx.2.1, fderiv_crossFactor_apply hx]
  simp only [tpDrift, tpNoise, rsNoise, rsDrift, proj_of_le h1, proj_of_le h2, Pi.mul_apply,
    Complex.neg_re, Complex.neg_im, re_two_div, im_two_div, Complex.ofReal_re, Complex.ofReal_im]
  have key := tp_alg (x.1.1.re) (x.1.1.im) (x.2.1.re) (x.2.1.im) (Real.sqrt 8)
    (Real.sq_sqrt (by norm_num)) (by have := hx.1; positivity) (by have := hx.2.1; positivity)
    (sq_add_sq_sub_pos hx.2.2) (sq_add_sq_add_pos hx.1 hx.2.1)
  linear_combination (rsTest 8 (1 / 6) x.1 * rsTest 8 (1 / 3) x.2 * crossFactor x.1.1 x.2.1) * key

/-! ## The two-point supermartingale bound -/

section Stochastic

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal NNReal

theorem lipschitz_tpDrift {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    ∃ K, LipschitzWith K (tpDrift y₁ y₂) :=
  ⟨_, ((lipschitz_rsDrift hy₁).comp LipschitzWith.prod_fst).prodMk
    ((lipschitz_rsDrift hy₂).comp LipschitzWith.prod_snd)⟩

theorem norm_tpDrift_le {y₁ y₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (x : TPState) :
    ‖tpDrift y₁ y₂ x‖ ≤ 2 / y₁ + 2 / y₁ ^ 2 + (2 / y₂ + 2 / y₂ ^ 2) := by
  have h1 := norm_rsDrift_le hy₁ x.1
  have h2 := norm_rsDrift_le hy₂ x.2
  have p1 : 0 ≤ 2 / y₁ + 2 / y₁ ^ 2 := by positivity
  have p2 : 0 ≤ 2 / y₂ + 2 / y₂ ^ 2 := by positivity
  refine norm_prod_le_iff.2 ⟨?_, ?_⟩
  · exact h1.trans (by linarith)
  · exact h2.trans (by linarith)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The two-point state process `((u₁, L₁), (u₂, L₂))` of the reverse flow driven by `√8 B`. -/
def tpProc (B : ℝ≥0 → Ω → ℝ) (z₁ z₂ : ℂ) (t : ℝ≥0) (ω : Ω) : TPState :=
  (rsProc 8 B z₁ t ω, rsProc 8 B z₂ t ω)

theorem tpProc_integralEq (hBc : ∀ ω, Continuous (B · ω)) {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im)
    (hz₂ : 0 < z₂.im) (ω : Ω) (t : ℝ≥0) :
    tpProc B z₁ z₂ t ω = ((z₁, 0), (z₂, 0)) +
      (∫ r in (0 : ℝ)..t, tpDrift z₁.im z₂.im (tpProc B z₁ z₂ r.toNNReal ω)) + B t ω • tpNoise := by
  have hU₁ := rsProc_integralEq hBc 8 hz₁
  have hU₂ := rsProc_integralEq hBc 8 hz₂
  have hc₁ : Continuous fun s : ℝ≥0 => rsProc 8 B z₁ s ω :=
    Dynkin.continuous_of_integralEq hBc (lipschitz_rsDrift hz₁).continuous (norm_rsDrift_le hz₁)
      hU₁ ω
  have hc₂ : Continuous fun s : ℝ≥0 => rsProc 8 B z₂ s ω :=
    Dynkin.continuous_of_integralEq hBc (lipschitz_rsDrift hz₂).continuous (norm_rsDrift_le hz₂)
      hU₂ ω
  have hcont : Continuous fun r : ℝ => tpDrift z₁.im z₂.im (tpProc B z₁ z₂ r.toNNReal ω) :=
    (((lipschitz_rsDrift hz₁).continuous.comp (hc₁.comp continuous_real_toNNReal)).prodMk
      ((lipschitz_rsDrift hz₂).continuous.comp (hc₂.comp continuous_real_toNNReal)))
  have hint := hcont.intervalIntegrable (μ := volume) 0 (t : ℝ)
  have h1 := (ContinuousLinearMap.fst ℝ (ℂ × ℝ) (ℂ × ℝ)).intervalIntegral_comp_comm hint
  have h2 := (ContinuousLinearMap.snd ℝ (ℂ × ℝ) (ℂ × ℝ)).intervalIntegral_comp_comm hint
  simp only [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at h1 h2
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, ← h1]
    exact hU₁ ω t
  · simp only [Prod.snd_add, Prod.smul_snd, ← h2]
    exact hU₂ ω t

theorem measurable_rsTest (κ r : ℝ) : Measurable (rsTest κ r) := by
  unfold rsTest
  fun_prop

theorem measurable_tpTest : Measurable tpTest := by
  have h1 : Measurable fun x : TPState => rsTest 8 (1 / 6) x.1 :=
    (measurable_rsTest 8 _).comp measurable_fst
  have h2 : Measurable fun x : TPState => rsTest 8 (1 / 3) x.2 :=
    (measurable_rsTest 8 _).comp measurable_snd
  have h3 : Measurable fun x : TPState => crossFactor x.1.1 x.2.1 := by
    unfold crossFactor; fun_prop
  exact (h1.mul h2).mul h3


/-! ### Localization regions -/

/-- The region visited by the two-point state before its first coordinates leave a ball:
heights at least `y₁, y₂`, two-point separation `δ ≤ |u₁ - u₂|² Y₁ Y₂`, `|u₁| + |u₂| ≤ R`,
and log-derivatives bounded by `L₁, L₂`. -/
def tpRegion (y₁ y₂ δ R L₁ L₂ : ℝ) : Set TPState :=
  {x | y₁ ≤ x.1.1.im ∧ y₂ ≤ x.2.1.im ∧ δ ≤ ‖x.1.1 - x.2.1‖ ^ 2 * (x.1.1.im * x.2.1.im) ∧
    ‖x.1.1‖ + ‖x.2.1‖ ≤ R ∧ |x.1.2| ≤ L₁ ∧ |x.2.2| ≤ L₂}

theorem isClosed_tpRegion (y₁ y₂ δ R L₁ L₂ : ℝ) : IsClosed (tpRegion y₁ y₂ δ R L₁ L₂) := by
  have c1 : Continuous fun x : TPState => x.1.1 := continuous_fst.comp continuous_fst
  have c2 : Continuous fun x : TPState => x.2.1 := continuous_fst.comp continuous_snd
  have c3 : Continuous fun x : TPState => x.1.2 := continuous_snd.comp continuous_fst
  have c4 : Continuous fun x : TPState => x.2.2 := continuous_snd.comp continuous_snd
  refine (isClosed_le continuous_const (Complex.continuous_im.comp c1)).inter
    ((isClosed_le continuous_const (Complex.continuous_im.comp c2)).inter
    ((isClosed_le continuous_const (((continuous_norm.comp (c1.sub c2)).pow 2).mul
      ((Complex.continuous_im.comp c1).mul (Complex.continuous_im.comp c2)))).inter
    ((isClosed_le ((continuous_norm.comp c1).add (continuous_norm.comp c2)) continuous_const).inter
    ((isClosed_le (continuous_abs.comp c3) continuous_const).inter
      (isClosed_le (continuous_abs.comp c4) continuous_const)))))

theorem tpRegion_subset_tpDom {y₁ y₂ δ R L₁ L₂ : ℝ} (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) (hδ : 0 < δ) :
    tpRegion y₁ y₂ δ R L₁ L₂ ⊆ tpDom := by
  rintro x ⟨h1, h2, h3, -⟩
  refine ⟨hy₁.trans_le h1, hy₂.trans_le h2, fun h => ?_⟩
  rw [h, sub_self, norm_zero] at h3
  linarith [show (0 : ℝ) ^ 2 * (x.2.1.im * x.2.1.im) = 0 by ring]

theorem isCompact_tpRegion (y₁ y₂ δ R L₁ L₂ : ℝ) : IsCompact (tpRegion y₁ y₂ δ R L₁ L₂) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_tpRegion _ _ _ _ _ _) ?_
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨|R| + |L₁| + |L₂|, fun x hx => ?_⟩
  obtain ⟨-, -, -, h4, h5, h6⟩ := hx
  rw [mem_closedBall, dist_zero_right]
  have n1 : ‖x.1.1‖ ≤ |R| := by
    have := norm_nonneg x.2.1; linarith [le_abs_self R]
  have n2 : ‖x.2.1‖ ≤ |R| := by
    have := norm_nonneg x.1.1; linarith [le_abs_self R]
  have a1 : 0 ≤ |L₁| := abs_nonneg _
  have a2 : 0 ≤ |L₂| := abs_nonneg _
  have aR : 0 ≤ |R| := abs_nonneg _
  refine norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨by linarith, ?_⟩,
    norm_prod_le_iff.2 ⟨by linarith, ?_⟩⟩
  · rw [Real.norm_eq_abs]; linarith [le_abs_self L₁]
  · rw [Real.norm_eq_abs]; linarith [le_abs_self L₂]

/-! ### Fatou along a localizing sequence -/

theorem lintegral_ofReal_le_of_eventually_eq {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {c : ℝ}
    (hfint : ∀ n, Integrable (f n) P) (hfnn : ∀ n ω, 0 ≤ f n ω) (hexp : ∀ n, ∫ ω, f n ω ∂P = c)
    (hev : ∀ ω, ∀ᶠ n in atTop, f n ω = g ω) :
    ∫⁻ ω, ENNReal.ofReal (g ω) ∂P ≤ ENNReal.ofReal c := by
  have hflin : ∀ n, ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P = ENNReal.ofReal c := by
    intro n
    rw [← hexp n, ofReal_integral_eq_lintegral_ofReal (hfint n) (ae_of_all _ (hfnn n))]
  have hlim : ∀ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop = ENNReal.ofReal (g ω) := by
    intro ω
    refine Tendsto.liminf_eq (tendsto_const_nhds.congr' ?_)
    filter_upwards [hev ω] with n hn
    rw [hn]
  calc ∫⁻ ω, ENNReal.ofReal (g ω) ∂P
      = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂P :=
        lintegral_congr fun ω => (hlim ω).symm
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop :=
        lintegral_liminf_le' fun n => (hfint n).aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal c :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun n => (hflin n).le)


/-! ### Pathwise bounds on the state -/

theorem abs_re_integral_two_div_sq_le {W : ℝ → ℝ} (hW : Continuous W) {z : ℂ} (hz : 0 < z.im)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |(∫ s in (0 : ℝ)..t, 2 / (revMap W s z) ^ 2).re| ≤ 2 * T / z.im ^ 2 := by
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 / z.im ^ 2)
    fun s hs => ?_).trans ?_
  · rw [uIoc_of_le ht] at hs
    have h1 : z.im ≤ ‖revMap W s z‖ :=
      (im_le_im_revMap _ hW z hz hs.1.le).trans (Complex.im_le_norm _)
    rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by gcongr)
  · rw [sub_zero, abs_of_nonneg ht]
    have h0 : 0 ≤ 2 / z.im ^ 2 := by positivity
    calc 2 / z.im ^ 2 * t ≤ 2 / z.im ^ 2 * T := mul_le_mul_of_nonneg_left htT h0
      _ = 2 * T / z.im ^ 2 := by ring

theorem tpProc_mem_tpRegion (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {z₁ z₂ : ℂ} (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (T : ℝ≥0) (R : ℝ)
    (hR : ‖z₁‖ + ‖z₂‖ ≤ R) (ω : Ω) (t : ℝ≥0) (htT : t ≤ T)
    (hs : ∀ s < t, tpProc B z₁ z₂ s ω ∉ {x : TPState | R ≤ ‖x.1.1‖ + ‖x.2.1‖}) :
    tpProc B z₁ z₂ t ω ∈ tpRegion z₁.im z₂.im (‖z₁ - z₂‖ ^ 2 * (z₁.im * z₂.im)) R
      (2 * T / z₁.im ^ 2) (2 * T / z₂.im ^ 2) := by
  have hW : Continuous (drive 8 B ω) := NonSwallow.continuous_drive_ns hBc 8 ω
  have hU := tpProc_integralEq (B := B) hBc hz₁ hz₂
  obtain ⟨Lb, hb⟩ := lipschitz_tpDrift hz₁ hz₂
  have hUc : Continuous fun s => tpProc B z₁ z₂ s ω :=
    Dynkin.continuous_of_integralEq hBc hb.continuous (norm_tpDrift_le hz₁ hz₂) hU ω
  have htT' : (t : ℝ) ≤ T := htT
  refine ⟨im_le_im_revMap _ hW z₁ hz₁ t.coe_nonneg, im_le_im_revMap _ hW z₂ hz₂ t.coe_nonneg,
    TwoPoint.twoPoint_lower_sq hW hz₁ hz₂ t.coe_nonneg, ?_,
    abs_re_integral_two_div_sq_le hW hz₁ t.coe_nonneg htT',
    abs_re_integral_two_div_sq_le hW hz₂ t.coe_nonneg htT'⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
  · rw [← h0, hU ω 0, hB0 ω]
    simpa using hR
  · have hcl : IsClosed {s : ℝ≥0 | ‖(tpProc B z₁ z₂ s ω).1.1‖ + ‖(tpProc B z₁ z₂ s ω).2.1‖ ≤ R} :=
      isClosed_le ((continuous_norm.comp (continuous_fst.comp (continuous_fst.comp hUc))).add
        (continuous_norm.comp (continuous_fst.comp (continuous_snd.comp hUc)))) continuous_const
    have hsub : Iio t ⊆
        {s : ℝ≥0 | ‖(tpProc B z₁ z₂ s ω).1.1‖ + ‖(tpProc B z₁ z₂ s ω).2.1‖ ≤ R} :=
      fun s hst => by
        have h := hs s hst
        simp only [mem_ofPred_eq, not_le] at h
        exact h.le
    have := hcl.closure_subset_iff.2 hsub
    rw [closure_Iio' (a := t) ⟨0, hpos⟩] at this
    exact this (le_refl t)


theorem tpTest_nonneg {x : TPState} (h1 : 0 < x.1.1.im) (h2 : 0 < x.2.1.im) : 0 ≤ tpTest x := by
  have hr : ∀ (r : ℝ) (y : ℂ × ℝ), 0 < y.1.im → 0 ≤ rsTest 8 r y := fun r y hy => by
    simp only [rsTest]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ y.1.re ^ 2 + y.1.im ^ 2 by positivity) r
    have := Real.rpow_nonneg hy.le (rsZeta 8 r - 2 * r)
    positivity
  have hc : 0 ≤ crossFactor x.1.1 x.2.1 := Real.rpow_nonneg (by positivity) _
  exact mul_nonneg (mul_nonneg (hr _ _ h1) (hr _ _ h2)) hc

/-- **The two-point supermartingale bound** `E 𝒩_T ≤ 𝒩_0` for the state process, for a version of
the Brownian motion with continuous paths started at `0`. -/
theorem tp_core (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) (T : ℝ≥0) {z₁ z₂ : ℂ}
    (hz₁ : 0 < z₁.im) (hz₂ : 0 < z₂.im) (hne : z₁ ≠ z₂) :
    ∫⁻ ω, ENNReal.ofReal (tpTest (tpProc B z₁ z₂ T ω)) ∂P ≤
      ENNReal.ofReal (tpTest ((z₁, 0), (z₂, 0))) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set U := tpProc B z₁ z₂ with hUdef
  have hU : ∀ ω (t : ℝ≥0), U t ω = ((z₁, 0), (z₂, 0)) +
      (∫ r in (0 : ℝ)..t, tpDrift z₁.im z₂.im (U r.toNNReal ω)) + B t ω • tpNoise :=
    tpProc_integralEq hBc hz₁ hz₂
  obtain ⟨Lb, hb⟩ := lipschitz_tpDrift hz₁ hz₂
  have hbM := norm_tpDrift_le hz₁ hz₂
  have hUc : ∀ ω, Continuous (U · ω) := Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  have hU0 : ∀ ω, U 0 ω = ((z₁, 0), (z₂, 0)) := by
    intro ω; rw [hU ω 0, hB0 ω]; simp
  have hδ : 0 < ‖z₁ - z₂‖ ^ 2 * (z₁.im * z₂.im) := by
    have := norm_pos_iff.2 (sub_ne_zero.2 hne); positivity
  set R : ℕ → ℝ := fun n => ‖z₁‖ + ‖z₂‖ + n + 1 with hR
  set Cl : ℕ → Set TPState := fun n => {x | R n ≤ ‖x.1.1‖ + ‖x.2.1‖} with hCl
  set K : ℕ → Set TPState := fun n => tpRegion z₁.im z₂.im (‖z₁ - z₂‖ ^ 2 * (z₁.im * z₂.im))
    (R n) (2 * T / z₁.im ^ 2) (2 * T / z₂.im ^ 2) with hK
  have hClc : ∀ n, IsClosed (Cl n) := fun n =>
    isClosed_le continuous_const ((continuous_norm.comp (continuous_fst.comp continuous_fst)).add
      (continuous_norm.comp (continuous_fst.comp continuous_snd)))
  have hKO : ∀ n, K n ⊆ tpDom := fun n => tpRegion_subset_tpDom hz₁ hz₂ hδ
  have hUK : ∀ n ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl n) → U t ω ∈ K n := fun n =>
    tpProc_mem_tpRegion hBc hB0 hz₁ hz₂ T (R n) (by simp only [hR]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hFM : ∀ n, ∃ M, ∀ x ∈ K n, |tpTest x| ≤ M := fun n => by
    obtain ⟨M, hM⟩ := (isCompact_tpRegion _ _ _ _ _ _).exists_bound_of_continuousOn
      (contDiffOn_tpTest.continuousOn.mono (hKO n))
    exact ⟨M, fun x hx => (Real.norm_eq_abs _).symm.trans_le (hM x hx)⟩
  have hLF : ∀ n, ∀ x ∈ K n, x ∉ Cl n →
      dynkinGen (tpDrift z₁.im z₂.im) tpNoise tpTest x = 0 :=
    fun n x hx _ => dynkinGen_tpTest (hKO n hx) hx.1 hx.2.1
  set Fl := NonSwallow.bmFilt hBm with hFl
  have hmart : ∀ n, Martingale (fun t ω => tpTest (U (min t (hittingBtwn U (Cl n) 0 T ω)) ω))
      Fl P := fun n =>
    martingale_localDynkin_stopped hB hBc Fl (NonSwallow.bmFilt_adapted hBm)
      (NonSwallow.bmFilt_le_past hBm) hb hbM hU isOpen_tpDom (hClc n)
      (isClosed_tpRegion _ _ _ _ _ _) (hKO n) contDiffOn_tpTest (hLF n) T (hUK n)
      (hFM n).choose_spec
  set f : ℕ → Ω → ℝ := fun n ω => tpTest (U (min T (hittingBtwn U (Cl n) 0 T ω)) ω) with hf
  have hfexp : ∀ n, ∫ ω, f n ω ∂P = tpTest ((z₁, 0), (z₂, 0)) := by
    intro n
    have hce := (hmart n).2 0 T (zero_le : (0 : ℝ≥0) ≤ T)
    have h1 : ∫ ω, f n ω ∂P =
        ∫ ω, tpTest (U (min 0 (hittingBtwn U (Cl n) 0 T ω)) ω) ∂P := by
      rw [← integral_condExp (Fl.le 0)]
      exact integral_congr_ae hce
    rw [h1]
    simp only [zero_le, min_eq_left, hU0, integral_const, probReal_univ, one_smul]
  have hfnn : ∀ n ω, 0 ≤ f n ω := fun n ω => by
    have hW : Continuous (drive 8 B ω) := NonSwallow.continuous_drive_ns hBc 8 ω
    exact tpTest_nonneg (hz₁.trans_le (im_le_im_revMap _ hW z₁ hz₁ (NNReal.coe_nonneg _)))
      (hz₂.trans_le (im_le_im_revMap _ hW z₂ hz₂ (NNReal.coe_nonneg _)))
  have hev : ∀ ω, ∀ᶠ n in atTop, f n ω = tpTest (U T ω) := by
    intro ω
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hUc ω).continuousOn
    filter_upwards [eventually_ge_atTop ⌈2 * C⌉₊] with n hn
    have hnot : ¬ ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl n := by
      rintro ⟨j, hj, hjCl⟩
      have h1 := hC j hj
      have h2 : ‖(U j ω).1.1‖ ≤ ‖U j ω‖ := (norm_fst_le _).trans (norm_fst_le _)
      have h2' : ‖(U j ω).2.1‖ ≤ ‖U j ω‖ := (norm_fst_le _).trans (norm_snd_le _)
      have h3 : 2 * C ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      have h4 : R n ≤ ‖(U j ω).1.1‖ + ‖(U j ω).2.1‖ := hjCl
      simp only [hR] at h4
      have : 0 ≤ ‖z₁‖ := norm_nonneg _
      have : 0 ≤ ‖z₂‖ := norm_nonneg _
      linarith
    have hτ : hittingBtwn U (Cl n) 0 T ω = T := by
      simp only [hittingBtwn, hnot, ↓reduceIte]
    simp only [hf, hτ, min_self]
  exact lintegral_ofReal_le_of_eventually_eq (fun n => (hmart n).integrable T) hfnn hfexp hev

end Stochastic

/-! ## The estimate (3.17)–(3.18) and Markov's inequality -/

section Estimate

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal NNReal

/-- The one-point factor (3.13) in Rohde–Schramm form, `Φ^{ρ(b)} Y^{λ(b)-ρ(b)} (Y/|Z|)^{-2b}`,
for the reverse flow `revMap W T` from `z`. -/
def onePointForm (W : ℝ → ℝ) (T : ℝ) (b : ℝ) (z : ℂ) : ℝ :=
  ‖deriv (revMap W T) z‖ ^ rsLam 8 b * (revMap W T z).im ^ rsZeta 8 b *
    ((revMap W T z).im / ‖revMap W T z‖) ^ (-2 * b)

/-- The two-point process `𝒩_T` of (3.16) at time `T` for the reverse flow `revMap W`: the product of
the one-point factors for `b₁ = 1/6` at `z₁` and `b₂ = 1/3` at `z₂` and the cross factor
`(|Z₁ - Z₂| |Z₁ - Z̄₂|)^{-4/9}`. -/
def tpForm (W : ℝ → ℝ) (T : ℝ) (z₁ z₂ : ℂ) : ℝ :=
  onePointForm W T (1 / 6) z₁ * onePointForm W T (1 / 3) z₂ *
    crossFactor (revMap W T z₁) (revMap W T z₂)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem tpTest_tpProc_eq (hBc : ∀ ω, Continuous (B · ω)) {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ H)
    (hz₂ : z₂ ∈ H) (T : ℝ≥0) (ω : Ω) :
    tpTest (tpProc B z₁ z₂ T ω) = tpForm (drive 8 B ω) T z₁ z₂ := by
  have hW : Continuous (drive 8 B ω) := NonSwallow.continuous_drive_ns hBc 8 ω
  simp only [tpTest, tpProc, rsProc, tpForm, onePointForm]
  rw [rsTest_revMap hW 8 _ T.coe_nonneg hz₁, rsTest_revMap hW 8 _ T.coe_nonneg hz₂]

/-- **The two-point supermartingale bound** `E 𝒩_T ≤ 𝒩_0` (proof of Lemma 3.2), for a Brownian
motion `B`, the driver `√8 B`, deterministic `T ≥ 0` and distinct `z₁, z₂ ∈ ℍ`, together with the
a.e.-measurability of `𝒩_T`. -/
theorem lintegral_tpForm_le (hB : IsBrownianReal B P) {T : ℝ} (hT : 0 ≤ T) {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ H) (hz₂ : z₂ ∈ H) (hne : z₁ ≠ z₂) :
    AEMeasurable (fun ω => tpForm (drive 8 B ω) T z₁ z₂) P ∧
      ∫⁻ ω, ENNReal.ofReal (tpForm (drive 8 B ω) T z₁ z₂) ∂P ≤
        ENNReal.ofReal (tpTest ((z₁, 0), (z₂, 0))) := by
  obtain ⟨B', hB'm, hB'c, hB'0, hB'B, hB'eq⟩ := RS.exists_good_version0 hB
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT
  have hae : ∀ᵐ ω ∂P, tpTest (tpProc B' z₁ z₂ T.toNNReal ω) = tpForm (drive 8 B ω) T z₁ z₂ := by
    filter_upwards [hB'eq] with ω hω
    have hdr : drive 8 B' ω = drive 8 B ω := funext fun t => by simp only [drive, hω]
    rw [tpTest_tpProc_eq hB'c hz₁ hz₂, hTT, hdr]
  have hcore := tp_core hB'B.toIsPreBrownianReal hB'c hB'm hB'0 T.toNNReal hz₁ hz₂ hne
  refine ⟨?_, le_of_eq_of_le (lintegral_congr_ae (hae.mono fun ω h => by rw [h])).symm hcore⟩
  have hU := tpProc_integralEq (B := B') hB'c hz₁ hz₂
  obtain ⟨Lb, hb⟩ := lipschitz_tpDrift hz₁ hz₂
  have hUc := Dynkin.continuous_of_integralEq hB'c hb.continuous (norm_tpDrift_le hz₁ hz₂) hU
  have hUm := Dynkin.measurable_of_integralEq (NonSwallow.bmFilt hB'm)
    (NonSwallow.bmFilt_adapted hB'm) hB'c hb (norm_tpDrift_le hz₁ hz₂) hU hUc T.toNNReal
  exact ⟨_, measurable_tpTest.comp (hUm.mono ((NonSwallow.bmFilt hB'm).le _) le_rfl),
    hae.mono fun ω h => h.symm⟩


/-! ### The lower bound (3.18) on the event -/

theorem le_rpow_mul_rpow_mul_rpow {Φ Y N φ η lam ζ r : ℝ} (hφ : 0 ≤ φ) (hφΦ : φ ≤ Φ) (hη : 0 < η)
    (hηY : η ≤ Y) (hYN : Y ≤ N) (hlam : 0 ≤ lam) (hζ : 0 ≤ ζ) (hr : 0 ≤ r) :
    φ ^ lam * η ^ ζ ≤ Φ ^ lam * Y ^ ζ * (Y / N) ^ (-2 * r) := by
  have hY : 0 < Y := hη.trans_le hηY
  have h1 : φ ^ lam ≤ Φ ^ lam := Real.rpow_le_rpow hφ hφΦ hlam
  have h2 : η ^ ζ ≤ Y ^ ζ := Real.rpow_le_rpow hη.le hηY hζ
  have h3 : 1 ≤ (Y / N) ^ (-2 * r) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos hY (hY.trans_le hYN))
      ((div_le_one (hY.trans_le hYN)).2 hYN) (by linarith)
  have p1 : 0 ≤ Φ ^ lam := Real.rpow_nonneg (hφ.trans hφΦ) _
  have p2 : 0 ≤ Y ^ ζ := Real.rpow_nonneg hY.le _
  calc φ ^ lam * η ^ ζ ≤ Φ ^ lam * Y ^ ζ :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hη.le _) p1
    _ = Φ ^ lam * Y ^ ζ * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (mul_nonneg p1 p2)

/-- The one-point factor is at least `(A/y)^{ρ} A^{λ-ρ}` when `A ≤ y Φ_T(z)`, `y = Im z`. -/
theorem le_onePointForm {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) {b A : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1 / 2) (hA : 0 < A)
    (hAz : A ≤ z.im * ‖deriv (revMap V T) z‖) :
    (A / z.im) ^ rsLam 8 b * A ^ rsZeta 8 b ≤ onePointForm V T b z := by
  have hy : 0 < z.im := hz
  have hΦ : A / z.im ≤ ‖deriv (revMap V T) z‖ := by
    rw [div_le_iff₀ hy]; linarith
  have hΦY := TwoPoint.norm_deriv_revMap_le hV hz hT
  have hAY : A ≤ (revMap V T z).im := by
    rw [le_div_iff₀ hy] at hΦY; nlinarith
  refine le_rpow_mul_rpow_mul_rpow (div_nonneg hA.le hy.le) hΦ hA hAY (Complex.im_le_norm _)
    ?_ ?_ hb
  · simp only [rsLam]; nlinarith
  · simp only [rsZeta]; nlinarith

/-- The cross factor is at least `(4ξ² + 20)^{-4/9}` when `|X_j| ≤ ξ` and `Y_j² ≤ 5`. -/
theorem le_crossFactor {Z₁ Z₂ : ℂ} (h1 : 0 < Z₁.im) (h2 : 0 < Z₂.im) (hne : Z₁ ≠ Z₂) {ξ : ℝ}
    (hX₁ : |Z₁.re| ≤ ξ) (hX₂ : |Z₂.re| ≤ ξ) (hY₁ : Z₁.im ^ 2 ≤ 5) (hY₂ : Z₂.im ^ 2 ≤ 5) :
    ((4 * ξ ^ 2 + 20) ^ 2) ^ (-(2 / 9 : ℝ)) ≤ crossFactor Z₁ Z₂ := by
  have hD₁ := sq_add_sq_sub_pos hne
  have hD₂ := sq_add_sq_add_pos h1 h2
  have hx₁ : Z₁.re ^ 2 ≤ ξ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hX₁ 2
  have hx₂ : Z₂.re ^ 2 ≤ ξ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hX₂ 2
  have e1 : (Z₁.re - Z₂.re) ^ 2 + (Z₁.im - Z₂.im) ^ 2 ≤ 4 * ξ ^ 2 + 20 := by
    nlinarith [sq_nonneg (Z₁.re + Z₂.re), sq_nonneg (Z₁.im + Z₂.im)]
  have e2 : (Z₁.re - Z₂.re) ^ 2 + (Z₁.im + Z₂.im) ^ 2 ≤ 4 * ξ ^ 2 + 20 := by
    nlinarith [sq_nonneg (Z₁.re + Z₂.re), sq_nonneg (Z₁.im - Z₂.im)]
  unfold crossFactor
  refine Real.rpow_le_rpow_of_nonpos (mul_pos hD₁ hD₂) ?_ (by norm_num)
  calc ((Z₁.re - Z₂.re) ^ 2 + (Z₁.im - Z₂.im) ^ 2) * ((Z₁.re - Z₂.re) ^ 2 + (Z₁.im + Z₂.im) ^ 2)
      ≤ (4 * ξ ^ 2 + 20) * (4 * ξ ^ 2 + 20) := mul_le_mul e1 e2 hD₂.le (by positivity)
    _ = (4 * ξ ^ 2 + 20) ^ 2 := (sq _).symm


/-! ### The initial value (3.17) -/

theorem rsZeta_eight_one_sixth : rsZeta 8 (1 / 6) = 2 / 9 := by norm_num [rsZeta]
theorem rsZeta_eight_one_third : rsZeta 8 (1 / 3) = 2 / 9 := by norm_num [rsZeta]
theorem rsLam_eight_one_sixth : rsLam 8 (1 / 6) = 8 / 9 := by norm_num [rsLam]
theorem rsLam_eight_one_third : rsLam 8 (1 / 3) = 14 / 9 := by norm_num [rsLam]

/-- **(3.17)**: `𝒩_0 ≤ 4^{2/9} y^{-4/9} (v/y)^{2/9} (1 + m²)^{1/3}`, in unsimplified form. -/
theorem tpTest_init_le {y v : ℝ} (hy : 0 < y) (hv : 0 < v) (hvy : v ≤ y / 2) (m : ℝ) :
    tpTest (((y : ℂ) * Complex.I, 0), ((((m : ℂ) + Complex.I) * v), 0)) ≤
      y ^ (2 / 9 - 1 / 3 : ℝ) * (y ^ 2) ^ (1 / 6 : ℝ) *
        (v ^ (2 / 9 - 2 / 3 : ℝ) * (v ^ 2 * (1 + m ^ 2)) ^ (1 / 3 : ℝ)) * (y ^ 4 / 4) ^ (-(2 / 9) : ℝ) := by
  simp only [tpTest, rsTest, crossFactor, rsZeta_eight_one_sixth, rsZeta_eight_one_third,
    mul_zero, Real.exp_zero, one_mul, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  norm_num
  rw [show (m * v) ^ 2 + v ^ 2 = v ^ 2 * (1 + m ^ 2) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by norm_num)
  have h1 : (y / 2) ^ 2 ≤ (y - v) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h2 : y ^ 2 ≤ (y + v) ^ 2 := pow_le_pow_left₀ hy.le (by linarith) 2
  calc y ^ 4 / 4 = (y / 2) ^ 2 * y ^ 2 := by ring
    _ ≤ ((m * v) ^ 2 + (y - v) ^ 2) * ((m * v) ^ 2 + (y + v) ^ 2) :=
      mul_le_mul (by nlinarith [sq_nonneg (m * v)]) (by nlinarith [sq_nonneg (m * v)])
        (by positivity) (by positivity)


/-! ### The note's form of (3.16) -/

theorem noteForm_real {Φ₁ Φ₂ Y₁ Y₂ N₁ N₂ D₁ D₂ : ℝ} (hΦ₁ : 0 < Φ₁) (hΦ₂ : 0 < Φ₂) (hY₁ : 0 < Y₁)
    (hY₂ : 0 < Y₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂) :
    Φ₁ ^ (8 / 9 : ℝ) * Y₁ ^ (2 / 9 : ℝ) * (Y₁ / N₁) ^ (-2 * (1 / 6) : ℝ) *
        (Φ₂ ^ (14 / 9 : ℝ) * Y₂ ^ (2 / 9 : ℝ) * (Y₂ / N₂) ^ (-2 * (1 / 3) : ℝ)) *
        (D₁ ^ 2 * D₂ ^ 2) ^ (-(2 / 9) : ℝ) =
      Φ₁ ^ (8 / 9 : ℝ) * Φ₂ ^ (14 / 9 : ℝ) * (Y₁ * Y₂) ^ (2 / 9 : ℝ) *
          (N₁ ^ 2 / Y₁ ^ 2) ^ (1 / 6 : ℝ) * (N₂ ^ 2 / Y₂ ^ 2) ^ (1 / 3 : ℝ) /
        (D₁ * D₂) ^ (4 / 9 : ℝ) := by
  obtain ⟨a, rfl⟩ : ∃ a, Φ₁ = Real.exp a := ⟨_, (Real.exp_log hΦ₁).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, Φ₂ = Real.exp b := ⟨_, (Real.exp_log hΦ₂).symm⟩
  obtain ⟨c, rfl⟩ : ∃ c, Y₁ = Real.exp c := ⟨_, (Real.exp_log hY₁).symm⟩
  obtain ⟨d, rfl⟩ : ∃ d, Y₂ = Real.exp d := ⟨_, (Real.exp_log hY₂).symm⟩
  obtain ⟨e, rfl⟩ : ∃ e, N₁ = Real.exp e := ⟨_, (Real.exp_log hN₁).symm⟩
  obtain ⟨f, rfl⟩ : ∃ f, N₂ = Real.exp f := ⟨_, (Real.exp_log hN₂).symm⟩
  obtain ⟨g, rfl⟩ : ∃ g, D₁ = Real.exp g := ⟨_, (Real.exp_log hD₁).symm⟩
  obtain ⟨h, rfl⟩ : ∃ h, D₂ = Real.exp h := ⟨_, (Real.exp_log hD₂).symm⟩
  simp only [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_mul]
  congr 1
  push_cast
  ring

theorem one_add_sq_div_sq_eq {Z : ℂ} (hZ : 0 < Z.im) :
    1 + Z.re ^ 2 / Z.im ^ 2 = ‖Z‖ ^ 2 / Z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  field_simp
  ring

theorem crossFactor_eq_norm (Z₁ Z₂ : ℂ) :
    crossFactor Z₁ Z₂ =
      (‖Z₁ - Z₂‖ ^ 2 * ‖Z₁ - (starRingEnd ℂ) Z₂‖ ^ 2) ^ (-(2 / 9 : ℝ)) := by
  unfold crossFactor
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
  congr 1
  ring

/-- **The two-point process is the note's (3.16)**: `𝒩_T = Φ₁^{8/9} Φ₂^{14/9} (Y₁Y₂)^{2/9}
(1 + X₁²/Y₁²)^{1/6} (1 + X₂²/Y₂²)^{1/3} / (|Z₁ - Z₂| |Z₁ - Z̄₂|)^{4/9}`. -/
theorem tpForm_eq {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ H) (hz₂ : z₂ ∈ H) (hne : z₁ ≠ z₂) :
    tpForm W T z₁ z₂ =
      ‖deriv (revMap W T) z₁‖ ^ (8 / 9 : ℝ) * ‖deriv (revMap W T) z₂‖ ^ (14 / 9 : ℝ) *
          ((revMap W T z₁).im * (revMap W T z₂).im) ^ (2 / 9 : ℝ) *
          (1 + (revMap W T z₁).re ^ 2 / (revMap W T z₁).im ^ 2) ^ (1 / 6 : ℝ) *
          (1 + (revMap W T z₂).re ^ 2 / (revMap W T z₂).im ^ 2) ^ (1 / 3 : ℝ) /
        (‖revMap W T z₁ - revMap W T z₂‖ *
          ‖revMap W T z₁ - (starRingEnd ℂ) (revMap W T z₂)‖) ^ (4 / 9 : ℝ) := by
  have hY₁ := TwoPoint.im_revMap_pos hW hz₁ hT
  have hY₂ := TwoPoint.im_revMap_pos hW hz₂ hT
  have hZne := (injOn_revMap W hW hT).ne hz₁ hz₂ hne
  have hD₁ : 0 < ‖revMap W T z₁ - revMap W T z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hZne)
  have hD₂ : 0 < ‖revMap W T z₁ - (starRingEnd ℂ) (revMap W T z₂)‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  rw [one_add_sq_div_sq_eq hY₁, one_add_sq_div_sq_eq hY₂]
  unfold tpForm onePointForm
  rw [crossFactor_eq_norm, rsLam_eight_one_sixth, rsZeta_eight_one_sixth, rsLam_eight_one_third,
    rsZeta_eight_one_third]
  exact noteForm_real (norm_pos_iff.2 (deriv_revMap_ne_zero W hW hT hz₁))
    (norm_pos_iff.2 (deriv_revMap_ne_zero W hW hT hz₂)) hY₁ hY₂
    (hY₁.trans_le (Complex.im_le_norm _)) (hY₂.trans_le (Complex.im_le_norm _)) hD₁ hD₂

/-! ### The pathwise lower bound (3.18) -/

/-- The bound `ξ_M = max 1 (2M) + 2M` on `|X_t(z_j)|` on `Ω_M`. -/
def reBound (M : ℝ) : ℝ := max 1 (2 * M) + 2 * M

/-- The lower bound of (3.18), in unsimplified form. -/
def tpLower (M c₀ a y v : ℝ) : ℝ :=
  (a / y) ^ (8 / 9 : ℝ) * a ^ (2 / 9 : ℝ) * ((c₀ * a / v) ^ (14 / 9 : ℝ) * (c₀ * a) ^ (2 / 9 : ℝ)) *
    ((4 * reBound M ^ 2 + 20) ^ 2) ^ (-(2 / 9) : ℝ)

theorem iy_mem_H {y : ℝ} (hy : 0 < y) : (y : ℂ) * Complex.I ∈ H := by
  show 0 < ((y : ℂ) * Complex.I).im; simpa using hy

theorem intCast_add_I_mul_mem_H (m : ℤ) {v : ℝ} (hv : 0 < v) :
    ((m : ℂ) + Complex.I) * v ∈ H := by
  show 0 < (((m : ℂ) + Complex.I) * v).im; simpa using hv

/-- **(3.18)**, pathwise: on `Ω_M` and the event of (3.11), the two-point process of the reverse flow
`V = revDriver W t` at time `t` is at least `c_{M,c₀} a^{26/9} y^{-8/9} v^{-14/9}`. -/
theorem tpLower_le_tpForm {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {M : ℝ}
    (hM : DriverBound M W) {c₀ t a y v : ℝ} (hc₀ : 0 < c₀) (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : 0 < a) (hy : y ∈ Ioc (0 : ℝ) 1) (hv : v ∈ Ioc (0 : ℝ) (y / 2)) {m : ℤ}
    (hmv : |(m : ℝ)| * v ≤ 1)
    (h1 : a ≤ y * ‖deriv (fwdMapInv W t) ((y : ℂ) * Complex.I)‖)
    (h2 : c₀ * a ≤ v * ‖deriv (fwdMapInv W t) (((m : ℂ) + Complex.I) * v)‖) :
    tpLower M c₀ a y v ≤
      tpForm (revDriver W t) t ((y : ℂ) * Complex.I) (((m : ℂ) + Complex.I) * v) := by
  set z₁ : ℂ := (y : ℂ) * Complex.I with hz₁def
  set z₂ : ℂ := ((m : ℂ) + Complex.I) * v with hz₂def
  have hz₁ : z₁ ∈ H := iy_mem_H hy.1
  have hz₂ : z₂ ∈ H := intCast_add_I_mul_mem_H m hv.1
  have hz₁im : z₁.im = y := by simp [hz₁def]
  have hz₂im : z₂.im = v := by simp [hz₂def]
  have hz₁re : z₁.re = 0 := by simp [hz₁def]
  have hz₂re : z₂.re = m * v := by simp [hz₂def]
  have hne : z₁ ≠ z₂ := fun h => by
    have := congrArg Complex.im h
    rw [hz₁im, hz₂im] at this
    linarith [hv.2, hy.1]
  set V := revDriver W t with hVdef
  have hV : Continuous V := continuous_revDriver hW t
  have hVb : ∀ s ∈ Icc (0 : ℝ) t, |V s| ≤ 2 * M := by
    intro s hs
    simp only [hVdef, revDriver_apply]
    have e1 := hM.1 (t - s) ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
    have e2 := hM.1 t ht
    calc |W (t - s) - W t| ≤ |W (t - s)| + |W t| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hderiv : ∀ z ∈ H, ‖deriv (fwdMapInv W t) z‖ = ‖deriv (revMap V t) z‖ := fun z hz => by
    rw [norm_deriv_fwdMapInv_eq_norm_deriv_revFlow hW hW0 ht.1 hz, deriv_revFlow]
  have hX : ∀ z ∈ H, |z.re| ≤ 1 → |(revMap V t z).re| ≤ reBound M := fun z hz hre =>
    (abs_re_revMap_le hV hz ht.1 hVb).trans
      (add_le_add_left (max_le_max hre le_rfl) _ |>.trans_eq (by rw [reBound]))
  have hY : ∀ z ∈ H, z.im ≤ 1 → (revMap V t z).im ^ 2 ≤ 5 := fun z hz him => by
    have := TwoPoint.im_revMap_sq_le hV hz ht.1
    have h0 : 0 < z.im := hz
    nlinarith [ht.2]
  have hX₁ := hX z₁ hz₁ (by rw [hz₁re, abs_zero]; norm_num)
  have hX₂ := hX z₂ hz₂ (by rw [hz₂re, abs_mul, abs_of_pos hv.1]; exact hmv)
  have hY₁ := hY z₁ hz₁ (by rw [hz₁im]; exact hy.2)
  have hY₂ := hY z₂ hz₂ (by rw [hz₂im]; linarith [hv.2, hy.2])
  have hP₁ := le_onePointForm hV ht.1 hz₁ (b := 1 / 6) (by norm_num) (by norm_num) ha
    (by rw [hz₁im, ← hderiv z₁ hz₁]; exact h1)
  have hP₂ := le_onePointForm hV ht.1 hz₂ (b := 1 / 3) (by norm_num) (by norm_num)
    (mul_pos hc₀ ha) (by rw [hz₂im, ← hderiv z₂ hz₂]; exact h2)
  rw [hz₁im, rsLam_eight_one_sixth, rsZeta_eight_one_sixth] at hP₁
  rw [hz₂im, rsLam_eight_one_third, rsZeta_eight_one_third] at hP₂
  have hC := le_crossFactor (TwoPoint.im_revMap_pos hV hz₁ ht.1) (TwoPoint.im_revMap_pos hV hz₂ ht.1)
    ((injOn_revMap V hV ht.1).ne hz₁ hz₂ hne) hX₁ hX₂ hY₁ hY₂
  have p1 : 0 ≤ (a / y) ^ (8 / 9 : ℝ) * a ^ (2 / 9 : ℝ) := by
    have := hy.1; positivity
  have p2 : 0 ≤ (c₀ * a / v) ^ (14 / 9 : ℝ) * (c₀ * a) ^ (2 / 9 : ℝ) := by
    have := hv.1; positivity
  have p3 : 0 ≤ ((4 * reBound M ^ 2 + 20) ^ 2) ^ (-(2 / 9) : ℝ) := by positivity
  unfold tpLower tpForm
  exact mul_le_mul (mul_le_mul hP₁ hP₂ p2 (p1.trans hP₁)) hC p3
    (mul_nonneg (p1.trans hP₁) (p2.trans hP₂))


/-! ### Lemma 3.2 -/

/-- Markov's inequality in the form used for (3.11). -/
theorem measure_le_ofReal_div_of_subset {f : Ω → ℝ} (hf : AEMeasurable f P) {S : Set Ω}
    {c N₀ : ℝ} (hc : 0 < c) (hS : S ⊆ {ω | c ≤ f ω})
    (hN : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ ENNReal.ofReal N₀) :
    P S ≤ ENNReal.ofReal (N₀ / c) := by
  have hsub : S ⊆ {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (f ω)} := fun ω hω =>
    ENNReal.ofReal_le_ofReal (hS hω)
  have hM := mul_meas_ge_le_lintegral₀ (μ := P) hf.ennreal_ofReal (ENNReal.ofReal c)
  have hc0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  rw [ENNReal.ofReal_div_of_pos hc]
  refine (measure_mono hsub).trans ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact hM.trans hN

theorem final_identity {a y v c₀ K μ : ℝ} (ha : 0 < a) (hy : 0 < y) (hv : 0 < v) (hc : 0 < c₀)
    (hK : 0 < K) (hμ : 0 < μ) :
    y ^ (2 / 9 - 1 / 3 : ℝ) * (y ^ 2) ^ (1 / 6 : ℝ) * (v ^ (2 / 9 - 2 / 3 : ℝ) * (v ^ 2 * μ) ^ (1 / 3 : ℝ)) *
        (y ^ 4 / 4) ^ (-(2 / 9) : ℝ) =
      (4 ^ (2 / 9 : ℝ) * K ^ (2 / 9 : ℝ) / c₀ ^ (16 / 9 : ℝ) * a ^ (-(26 / 9) : ℝ) * y ^ 2 *
          (v / y) ^ (16 / 9 : ℝ) * μ ^ (1 / 3 : ℝ)) *
        ((a / y) ^ (8 / 9 : ℝ) * a ^ (2 / 9 : ℝ) * ((c₀ * a / v) ^ (14 / 9 : ℝ) * (c₀ * a) ^ (2 / 9 : ℝ)) *
          K ^ (-(2 / 9) : ℝ)) := by
  obtain ⟨α, rfl⟩ : ∃ α, a = Real.exp α := ⟨Real.log a, (Real.exp_log ha).symm⟩
  obtain ⟨γ, rfl⟩ : ∃ γ, y = Real.exp γ := ⟨Real.log y, (Real.exp_log hy).symm⟩
  obtain ⟨ν, rfl⟩ : ∃ ν, v = Real.exp ν := ⟨Real.log v, (Real.exp_log hv).symm⟩
  obtain ⟨χ, rfl⟩ : ∃ χ, c₀ = Real.exp χ := ⟨Real.log c₀, (Real.exp_log hc).symm⟩
  obtain ⟨κ, rfl⟩ : ∃ κ, K = Real.exp κ := ⟨Real.log K, (Real.exp_log hK).symm⟩
  obtain ⟨θ, rfl⟩ : ∃ θ, μ = Real.exp θ := ⟨Real.log μ, (Real.exp_log hμ).symm⟩
  rw [show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm]
  simp only [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_mul]
  congr 1
  push_cast
  ring

/-- The constant `C_{M,c₀}` of Lemma 3.2. -/
def twoPointConst (M c₀ : ℝ) : ℝ :=
  4 ^ (2 / 9 : ℝ) * ((4 * reBound M ^ 2 + 20) ^ 2) ^ (2 / 9 : ℝ) / c₀ ^ (16 / 9 : ℝ)

end Estimate

end TwoPointDeriv

/-! ## Lemma 3.2 -/

section Lemma32

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open QuantumZipper RS TwoPointDeriv

/-- **Lemma 3.2 with the explicit constant** `C_{M,c₀} = twoPointConst M c₀` (see
`exists_measure_twoPoint_deriv_le` for the statement as printed). -/
theorem measure_twoPoint_deriv_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (M : ℝ) {c₀ : ℝ} (hc₀ : 0 < c₀) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1)
    {v : ℝ} (hv : v ∈ Ioc (0 : ℝ) (y / 2)) {m : ℤ} (hmv : |(m : ℝ)| * v ≤ 1) :
    P {ω | DriverBound M (drive 8 B ω) ∧
        a ≤ y * ‖deriv (fwdMapInv (drive 8 B ω) t) ((y : ℂ) * Complex.I)‖ ∧
        c₀ * a ≤ v * ‖deriv (fwdMapInv (drive 8 B ω) t) (((m : ℂ) + Complex.I) * v)‖} ≤
      ENNReal.ofReal (twoPointConst M c₀ * a ^ (-(26 / 9) : ℝ) * y ^ 2 * (v / y) ^ (16 / 9 : ℝ) *
        (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ)) := by
  set z₁ : ℂ := (y : ℂ) * Complex.I with hz₁def
  set z₂ : ℂ := ((m : ℂ) + Complex.I) * v with hz₂def
  have hz₁ : z₁ ∈ H := iy_mem_H hy.1
  have hz₂ : z₂ ∈ H := intCast_add_I_mul_mem_H m hv.1
  have hne : z₁ ≠ z₂ := fun h => by
    have := congrArg Complex.im h
    simp only [hz₁def, hz₂def, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.intCast_re,
      Complex.intCast_im] at this
    linarith [hv.2, hy.1]
  obtain ⟨B', hB'm, hB'c, hB'0, hB'B, hB'eq⟩ := RS.exists_good_version0 hB
  -- the event for the continuous version
  set S' : Set Ω := {ω | DriverBound M (drive 8 B' ω) ∧
      a ≤ y * ‖deriv (fwdMapInv (drive 8 B' ω) t) z₁‖ ∧
      c₀ * a ≤ v * ‖deriv (fwdMapInv (drive 8 B' ω) t) z₂‖} with hS'
  have hSS' : P {ω | DriverBound M (drive 8 B ω) ∧
      a ≤ y * ‖deriv (fwdMapInv (drive 8 B ω) t) z₁‖ ∧
      c₀ * a ≤ v * ‖deriv (fwdMapInv (drive 8 B ω) t) z₂‖} ≤ P S' := by
    refine measure_mono_ae ?_
    filter_upwards [hB'eq] with ω hω hmem
    have hdr : drive 8 B' ω = drive 8 B ω := funext fun s => by simp only [drive, hω]
    show ω ∈ S'
    simp only [hS', mem_ofPred_eq, hdr]
    exact hmem
  refine hSS'.trans ?_
  -- the reversed Brownian motion
  set B₂ := UnzipInvariance.revBM B' t.toNNReal with hB₂
  have hB₂B : IsBrownianReal B₂ P :=
    UnzipInvariance.isBrownianReal_revBM hB'B.toIsPreBrownianReal hB'c _
  obtain ⟨hmeas, hint⟩ := lintegral_tpForm_le hB₂B ht.1 hz₁ hz₂ hne
  have hsub : S' ⊆ {ω | tpLower M c₀ a y v ≤ tpForm (drive 8 B₂ ω) t z₁ z₂} := by
    intro ω hω
    have hW : Continuous (drive 8 B' ω) := NonSwallow.continuous_drive_ns hB'c 8 ω
    have hW0 : drive 8 B' ω 0 = 0 := drive_zero (hB'0 ω)
    have hrev : revMap (drive 8 B₂ ω) t = revMap (revDriver (drive 8 B' ω) t) t :=
      funext fun z => (UnzipInvariance.revMap_timeRev_eq_drive_revBM 8 B' ht.1 ω z).symm
    show tpLower M c₀ a y v ≤ tpForm (drive 8 B₂ ω) t z₁ z₂
    simp only [tpForm, onePointForm, hrev]
    exact tpLower_le_tpForm hW hW0 hω.1 hc₀ ht ha.1 hy hv hmv hω.2.1 hω.2.2
  have hlow : 0 < tpLower M c₀ a y v := by
    have := ha.1; have := hy.1; have := hv.1
    unfold tpLower; positivity
  refine (measure_le_ofReal_div_of_subset hmeas hlow hsub
    (hint.trans (ENNReal.ofReal_le_ofReal (tpTest_init_le hy.1 hv.1 hv.2 m)))).trans ?_
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [final_identity (K := (4 * reBound M ^ 2 + 20) ^ 2) (μ := 1 + (m : ℝ) ^ 2) ha.1 hy.1 hv.1 hc₀
    (by positivity) (by positivity), twoPointConst]
  exact mul_div_cancel_right₀ _ hlow.ne'

/-- **Lemma 3.2 of the SLE₈ note (two-point derivative estimate, (3.11)).** Let `B` be a standard
Brownian motion, `W = √8 B` (`drive 8 B ω`), and `F_t = fwdMapInv W t` the centred inverse Loewner
maps. For every `M` and `c₀ > 0` there is a deterministic constant `C_{M,c₀} < ∞` such that for every
deterministic `t ∈ [0, 1]`, `a ∈ (0, 1)`, `y ∈ (0, 1]`, `v ∈ (0, y/2]` and `m ∈ ℤ` with `|m| v ≤ 1`,
`P[Ω_M ∩ {y |F_t'(iy)| ≥ a, v |F_t'((m + i)v)| ≥ c₀ a}] ≤ C a^{-26/9} y² (v/y)^{16/9} (1 + m²)^{1/3}`,
where `Ω_M` is the event (2.11) (`DriverBound M W`). The constant does not depend on the
probability space or on the Brownian motion. -/
theorem exists_measure_twoPoint_deriv_le (M : ℝ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ},
      IsBrownianReal B P → ∀ t ∈ Icc (0 : ℝ) 1, ∀ a ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1,
        ∀ v ∈ Ioc (0 : ℝ) (y / 2), ∀ m : ℤ, |(m : ℝ)| * v ≤ 1 →
          P {ω | DriverBound M (drive 8 B ω) ∧
              a ≤ y * ‖deriv (fwdMapInv (drive 8 B ω) t) ((y : ℂ) * Complex.I)‖ ∧
              c₀ * a ≤ v * ‖deriv (fwdMapInv (drive 8 B ω) t) (((m : ℂ) + Complex.I) * v)‖} ≤
            ENNReal.ofReal (C * a ^ (-(26 / 9) : ℝ) * y ^ 2 * (v / y) ^ (16 / 9 : ℝ) *
              (1 + (m : ℝ) ^ 2) ^ (1 / 3 : ℝ)) :=
  ⟨twoPointConst M c₀, fun hB _ ht _ ha _ hy _ hv _ hmv =>
    measure_twoPoint_deriv_le hB M hc₀ ht ha hy hv hmv⟩

end Lemma32

end InteractingSLE.SLE8
