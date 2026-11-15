/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Observable

/-!
# Theorem 2.6, the provider, part 1: the driver as a smooth function of the one-point mean

Packet PROVE-T26-PROVIDER. Specification §2.3, proof of Theorem 2.6 (`source/spec/p001-048.md` L977–L986) and the
semimartingale step of the proof of Theorem 2.4 (L842–L847): for one point `z`, with `f = f_t(z)`, `g = g_t(z) =
f + W_t`, the force points `vʲ = Vʲ_t`, `ℓ = Im log f_t'(z)` and the mean `x = 𝔥_t(z)`,

  `arg f = Θ(g, v, ℓ, x) = c − ½ ∑ⱼ ρⱼ arg (g − vʲ) − (√κ χ/2) ℓ − (√κ/2) x`,   `W = Re g − Im g · cot Θ`,

where `c = (π/2)(1 + ∑ ρ^R)`. So `W = drvF (g, v, ℓ, x)` with `drvF` smooth on the open set `dom` where `Im g > 0` and
`Θ ∈ (0, π)`. This file proves:

* `contDiffOn_drvF`: `drvF` is `C^∞` on `dom` (`dom` open: `isOpen_dom`);
* the partial derivatives of `drvF` along `x` (`partialSnd_drvF`, `partialSndSnd_drvF`) and along a direction of the
  coordinates (`partialFst_drvF`);
* at a state (`ang = arg (g − w)` for a real `w`): the bracket density `(∂ₓ drvF)² · 4 (Im f)²/|f|⁴ = κ`
  (`partialSnd_drvF_sq_mul`), the force-point coefficient `∂_{vʲ} drvF = −½ ρⱼ + (vʲ − w) φⱼ` with
  `φⱼ = ½ ρⱼ ((vʲ − w) − 2 Re f)/|f − (vʲ − w)|²` (`partialFst_single_drvF`), and the vanishing of the remaining time
  density `d₀ + 2 ∑ φⱼ = 0` (`timeDensity_add_eq_zero`), using `2 √κ χ = 4 − κ`.

These are pointwise identities: no division by a gap `vʲ − w` occurs.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex

namespace InteractingSLE.Sec2.T26Pv

open Ito

variable {ι : Type*} [Fintype ι]

/-- The finite-variation coordinates at one point `z`: `g = g_t(z)`, the force points `v`, `ℓ = Im log f_t'(z)`. -/
abbrev St (ι : Type*) := ℂ × (ι → ℝ) × ℝ

/-- The angle `Θ(g, v, ℓ, x) = c − ½ ∑ ρⱼ arg (g − vʲ) − (√κ χ/2) ℓ − (√κ/2) x`; at the state, `= arg f_t(z)`. -/
def ang (κ c : ℝ) (ρ : ι → ℝ) (p : St ι × ℝ) : ℝ :=
  c - 1 / 2 * ∑ j, ρ j * arg (p.1.1 - (p.1.2.1 j : ℂ)) - Real.sqrt κ * QuantumZipper.chiC κ / 2 * p.1.2.2
    - Real.sqrt κ / 2 * p.2

/-- The driver as a function of the coordinates and the mean: `W = Re g − Im g · cot Θ`. -/
def drvF (κ c : ℝ) (ρ : ι → ℝ) (p : St ι × ℝ) : ℝ :=
  p.1.1.re - p.1.1.im * (Real.cos (ang κ c ρ p) / Real.sin (ang κ c ρ p))

/-- The open set where `Im g > 0` and `Θ ∈ (0, π)`. -/
def dom (κ c : ℝ) (ρ : ι → ℝ) : Set (St ι × ℝ) :=
  {p | 0 < p.1.1.im ∧ 0 < ang κ c ρ p ∧ ang κ c ρ p < Real.pi}

/-! ### Smoothness -/

theorem contDiff_gsub {n : WithTop ℕ∞} (j : ι) :
    ContDiff ℝ n fun p : St ι × ℝ => p.1.1 - (p.1.2.1 j : ℂ) :=
  contDiff_fst.fst.sub (ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ j).comp contDiff_fst.snd.fst))

omit [Fintype ι] in
theorem im_gsub (p : St ι × ℝ) (j : ι) : (p.1.1 - (p.1.2.1 j : ℂ)).im = p.1.1.im := by
  simp

theorem contDiffAt_ang (κ c : ℝ) (ρ : ι → ℝ) {n : WithTop ℕ∞} {p : St ι × ℝ} (hp : 0 < p.1.1.im) :
    ContDiffAt ℝ n (ang κ c ρ) p := by
  have harg : ∀ j, ContDiffAt ℝ n (fun q : St ι × ℝ => arg (q.1.1 - (q.1.2.1 j : ℂ))) p := fun j =>
    (contDiffAt_arg (mem_slitPlane_of_im_pos (by rw [im_gsub]; exact hp))).comp p
      (contDiff_gsub j).contDiffAt
  have hsum : ContDiffAt ℝ n (fun q : St ι × ℝ => ∑ j, ρ j * arg (q.1.1 - (q.1.2.1 j : ℂ))) p :=
    ContDiffAt.sum fun j _ => contDiffAt_const.mul (harg j)
  have hℓ : ContDiffAt ℝ n (fun q : St ι × ℝ => q.1.2.2) p := contDiff_fst.snd.snd.contDiffAt
  have hx : ContDiffAt ℝ n (fun q : St ι × ℝ => q.2) p := contDiff_snd.contDiffAt
  exact ((contDiffAt_const.sub (contDiffAt_const.mul hsum)).sub (contDiffAt_const.mul hℓ)).sub
    (contDiffAt_const.mul hx)

theorem continuousAt_ang (κ c : ℝ) (ρ : ι → ℝ) {p : St ι × ℝ} (hp : 0 < p.1.1.im) :
    ContinuousAt (ang κ c ρ) p :=
  (contDiffAt_ang κ c ρ (n := 0) hp).continuousAt

theorem isOpen_dom (κ c : ℝ) (ρ : ι → ℝ) : IsOpen (dom κ c ρ : Set (St ι × ℝ)) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have him : ∀ᶠ q in 𝓝 p, 0 < (q : St ι × ℝ).1.1.im :=
    (continuous_im.comp continuous_fst.fst).continuousAt.eventually (lt_mem_nhds hp.1)
  have hang := continuousAt_ang κ c ρ hp.1
  have h1 : ∀ᶠ q in 𝓝 p, 0 < ang κ c ρ q := hang.eventually (lt_mem_nhds hp.2.1)
  have h2 : ∀ᶠ q in 𝓝 p, ang κ c ρ q < Real.pi := hang.eventually (gt_mem_nhds hp.2.2)
  filter_upwards [him, h1, h2] with q hq1 hq2 hq3 using ⟨hq1, hq2, hq3⟩

theorem sin_ang_pos {κ c : ℝ} {ρ : ι → ℝ} {p : St ι × ℝ} (hp : p ∈ dom κ c ρ) :
    0 < Real.sin (ang κ c ρ p) :=
  Real.sin_pos_of_pos_of_lt_pi hp.2.1 hp.2.2

theorem contDiffAt_drvF (κ c : ℝ) (ρ : ι → ℝ) {n : WithTop ℕ∞} {p : St ι × ℝ} (hp : p ∈ dom κ c ρ) :
    ContDiffAt ℝ n (drvF κ c ρ) p := by
  have ha := contDiffAt_ang κ c ρ (n := n) hp.1
  have hre : ContDiffAt ℝ n (fun q : St ι × ℝ => q.1.1.re) p :=
    (reCLM.contDiff.comp contDiff_fst.fst).contDiffAt
  have him : ContDiffAt ℝ n (fun q : St ι × ℝ => q.1.1.im) p :=
    (imCLM.contDiff.comp contDiff_fst.fst).contDiffAt
  have hcos : ContDiffAt ℝ n (fun q => Real.cos (ang κ c ρ q)) p := Real.contDiff_cos.contDiffAt.comp p ha
  have hsin : ContDiffAt ℝ n (fun q => Real.sin (ang κ c ρ q)) p := Real.contDiff_sin.contDiffAt.comp p ha
  exact hre.sub (him.mul (hcos.div hsin (sin_ang_pos hp).ne'))

theorem contDiffOn_drvF (κ c : ℝ) (ρ : ι → ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (drvF κ c ρ) (dom κ c ρ) := fun _ hp =>
  (contDiffAt_drvF κ c ρ hp).contDiffWithinAt

/-! ### One-variable derivatives -/

/-- `cos/sin` composed with a differentiable real function. -/
theorem hasDerivAt_cot_comp {φ : ℝ → ℝ} {φ' s : ℝ} (hφ : HasDerivAt φ φ' s) (hs : Real.sin (φ s) ≠ 0) :
    HasDerivAt (fun r => Real.cos (φ r) / Real.sin (φ r)) (-φ' / Real.sin (φ s) ^ 2) s := by
  have h := (hφ.cos).div (hφ.sin) hs
  refine h.congr_deriv ?_
  have hsc := Real.sin_sq_add_cos_sq (φ s)
  field_simp
  linear_combination (-φ') * hsc

/-- The angle along a line of the coordinates. -/
theorem hasDerivAt_ang_line (κ c : ℝ) (ρ : ι → ℝ) {p : St ι × ℝ} (hp : 0 < p.1.1.im) (q : St ι) :
    HasDerivAt (fun s : ℝ => ang κ c ρ ((p.1 + s • q, p.2) : St ι × ℝ))
      (-(1 / 2) * ∑ j, ρ j * ((q.1 - (q.2.1 j : ℂ)) / (p.1.1 - (p.1.2.1 j : ℂ))).im
        - Real.sqrt κ * QuantumZipper.chiC κ / 2 * q.2.2) 0 := by
  have hj : ∀ j, HasDerivAt (fun s : ℝ => arg ((p.1 + s • q).1 - ((p.1 + s • q).2.1 j : ℂ)))
      ((q.1 - (q.2.1 j : ℂ)) / (p.1.1 - (p.1.2.1 j : ℂ))).im 0 := by
    intro j
    have hl : HasDerivAt (fun s : ℝ => (p.1 + s • q).1 - ((p.1 + s • q).2.1 j : ℂ))
        (q.1 - (q.2.1 j : ℂ)) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => (p.1.1 - (p.1.2.1 j : ℂ)) + (s : ℂ) * (q.1 - (q.2.1 j : ℂ)))
          (q.1 - (q.2.1 j : ℂ)) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const (q.1 - (q.2.1 j : ℂ))).const_add
          (p.1.1 - (p.1.2.1 j : ℂ))
      refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, Complex.real_smul, ofReal_add, ofReal_mul]
      ring
    have hmem : (p.1 + (0 : ℝ) • q).1 - ((p.1 + (0 : ℝ) • q).2.1 j : ℂ) ∈ slitPlane := by
      refine mem_slitPlane_of_im_pos ?_
      simpa using hp
    have h := hasDerivAt_arg_comp hl hmem
    simpa using h
  have hsum : HasDerivAt (fun s : ℝ => ∑ j, ρ j * arg ((p.1 + s • q).1 - ((p.1 + s • q).2.1 j : ℂ)))
      (∑ j, ρ j * ((q.1 - (q.2.1 j : ℂ)) / (p.1.1 - (p.1.2.1 j : ℂ))).im) 0 :=
    HasDerivAt.fun_sum fun j _ => (hj j).const_mul (ρ j)
  have hℓ : HasDerivAt (fun s : ℝ => (p.1 + s • q).2.2) q.2.2 0 := by
    have h1 : HasDerivAt (fun s : ℝ => p.1.2.2 + s * q.2.2) q.2.2 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const q.2.2).const_add p.1.2.2
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp
  have h := (((hasDerivAt_const (0 : ℝ) c).fun_sub (hsum.const_mul (1 / 2))).fun_sub
    (hℓ.const_mul (Real.sqrt κ * QuantumZipper.chiC κ / 2))).fun_sub
      (hasDerivAt_const (0 : ℝ) (Real.sqrt κ / 2 * p.2))
  refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [ang]

/-- The angle along the `x` direction. -/
theorem hasDerivAt_ang_snd (κ c : ℝ) (ρ : ι → ℝ) (e : St ι) (y : ℝ) :
    HasDerivAt (fun y : ℝ => ang κ c ρ ((e, y) : St ι × ℝ)) (-(Real.sqrt κ / 2)) y := by
  have h := (hasDerivAt_const y (c - 1 / 2 * ∑ j, ρ j * arg (e.1 - (e.2.1 j : ℂ))
    - Real.sqrt κ * QuantumZipper.chiC κ / 2 * e.2.2)).fun_sub ((hasDerivAt_id y).const_mul (Real.sqrt κ / 2))
  simpa [ang] using h

/-! ### The partial derivatives of `drvF` -/

theorem differentiableAt_drvF {κ c : ℝ} {ρ : ι → ℝ} {p : St ι × ℝ} (hp : p ∈ dom κ c ρ) :
    DifferentiableAt ℝ (drvF κ c ρ) p :=
  (contDiffAt_drvF κ c ρ (n := 1) hp).differentiableAt one_ne_zero

/-- `∂ₓ drvF = −(√κ/2) Im g / sin² Θ`. -/
theorem partialSnd_drvF {κ c : ℝ} {ρ : ι → ℝ} {p : St ι × ℝ} (hp : p ∈ dom κ c ρ) :
    partialSnd (drvF κ c ρ) p = -(Real.sqrt κ / 2) * p.1.1.im / Real.sin (ang κ c ρ p) ^ 2 := by
  suffices hd : HasDerivAt (fun y : ℝ => drvF κ c ρ ((p.1, y) : St ι × ℝ))
      (-(Real.sqrt κ / 2) * p.1.1.im / Real.sin (ang κ c ρ p) ^ 2) p.2 from
    @partialSnd_eq_of_hasDerivAt (St ι) _ _ (drvF κ c ρ) p (differentiableAt_drvF hp) _ hd
  set φ : ℝ → ℝ := fun y => ang κ c ρ ((p.1, y) : St ι × ℝ) with hφdef
  have hφp : φ p.2 = ang κ c ρ p := rfl
  have hs : Real.sin (φ p.2) ≠ 0 := (sin_ang_pos hp).ne'
  have hcot : HasDerivAt (fun y => Real.cos (φ y) / Real.sin (φ y)) (-(-(Real.sqrt κ / 2)) /
      Real.sin (φ p.2) ^ 2) p.2 := hasDerivAt_cot_comp (hasDerivAt_ang_snd κ c ρ p.1 p.2) hs
  have h : HasDerivAt (fun y => p.1.1.re - p.1.1.im * (Real.cos (φ y) / Real.sin (φ y)))
      (0 - p.1.1.im * (-(-(Real.sqrt κ / 2)) / Real.sin (φ p.2) ^ 2)) p.2 :=
    (hasDerivAt_const p.2 p.1.1.re).fun_sub (hcot.const_mul p.1.1.im)
  have e : (fun y : ℝ => drvF κ c ρ ((p.1, y) : St ι × ℝ)) =
      fun y => p.1.1.re - p.1.1.im * (Real.cos (φ y) / Real.sin (φ y)) := rfl
  rw [e, ← hφp]
  convert h using 1
  ring

/-- `∂ₓ² drvF = −(√κ)²/2 · Im g · cos Θ / sin³ Θ`. -/
theorem partialSndSnd_drvF {κ c : ℝ} {ρ : ι → ℝ} {p : St ι × ℝ} (hp : p ∈ dom κ c ρ) :
    partialSndSnd (drvF κ c ρ) p = -(Real.sqrt κ ^ 2 / 2) * p.1.1.im * Real.cos (ang κ c ρ p) /
      Real.sin (ang κ c ρ p) ^ 3 := by
  set φ : ℝ → ℝ := fun y => ang κ c ρ ((p.1, y) : St ι × ℝ) with hφdef
  have hφp : φ p.2 = ang κ c ρ p := rfl
  refine @partialSndSnd_eq_of_hasDerivAt (St ι) _ _ (drvF κ c ρ) p (contDiffAt_drvF κ c ρ hp)
    (fun y => -(Real.sqrt κ / 2) * p.1.1.im / Real.sin (φ y) ^ 2) _ ?_ ?_
  · have hc : Continuous fun y : ℝ => ((p.1, y) : St ι × ℝ) := continuous_const.prodMk continuous_id
    have hopen : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : St ι × ℝ) ∈ dom κ c ρ :=
      hc.continuousAt.preimage_mem_nhds ((isOpen_dom κ c ρ).mem_nhds (by simpa using hp))
    exact hopen.mono fun y hy => partialSnd_drvF hy
  · have hφ : HasDerivAt φ (-(Real.sqrt κ / 2)) p.2 := hasDerivAt_ang_snd κ c ρ p.1 p.2
    have hs : Real.sin (φ p.2) ≠ 0 := (sin_ang_pos hp).ne'
    have hsin : HasDerivAt (fun y => Real.sin (φ y)) (Real.cos (φ p.2) * -(Real.sqrt κ / 2)) p.2 := hφ.sin
    have hsq : HasDerivAt (fun y => Real.sin (φ y) ^ 2)
        ((2 : ℕ) * Real.sin (φ p.2) ^ (2 - 1) * (Real.cos (φ p.2) * -(Real.sqrt κ / 2))) p.2 :=
      hsin.fun_pow 2
    have hdiv : HasDerivAt (fun y => -(Real.sqrt κ / 2) * p.1.1.im / Real.sin (φ y) ^ 2)
        ((0 * Real.sin (φ p.2) ^ 2 - -(Real.sqrt κ / 2) * p.1.1.im *
          ((2 : ℕ) * Real.sin (φ p.2) ^ (2 - 1) * (Real.cos (φ p.2) * -(Real.sqrt κ / 2)))) /
          (Real.sin (φ p.2) ^ 2) ^ 2) p.2 :=
      (hasDerivAt_const p.2 (-(Real.sqrt κ / 2) * p.1.1.im)).fun_div hsq (pow_ne_zero 2 hs)
    rw [← hφp]
    convert hdiv using 1
    field_simp
    push_cast
    ring

/-- `∂_q drvF = Re q_g − Im q_g · cot Θ + Im g · DΘ(q) / sin² Θ` for a direction `q` of the coordinates. -/
theorem partialFst_drvF {κ c : ℝ} {ρ : ι → ℝ} {p : St ι × ℝ} (hp : p ∈ dom κ c ρ) (q : St ι) :
    partialFst (drvF κ c ρ) p q = q.1.re - q.1.im * (Real.cos (ang κ c ρ p) / Real.sin (ang κ c ρ p)) +
      p.1.1.im * (-(1 / 2) * ∑ j, ρ j * ((q.1 - (q.2.1 j : ℂ)) / (p.1.1 - (p.1.2.1 j : ℂ))).im
        - Real.sqrt κ * QuantumZipper.chiC κ / 2 * q.2.2) / Real.sin (ang κ c ρ p) ^ 2 := by
  refine @partialFst_eq_of_hasDerivAt (St ι) _ _ (drvF κ c ρ) p (differentiableAt_drvF hp) q _ ?_
  set D : ℝ := -(1 / 2) * ∑ j, ρ j * ((q.1 - (q.2.1 j : ℂ)) / (p.1.1 - (p.1.2.1 j : ℂ))).im
        - Real.sqrt κ * QuantumZipper.chiC κ / 2 * q.2.2 with hD
  set φ : ℝ → ℝ := fun s => ang κ c ρ ((p.1 + s • q, p.2) : St ι × ℝ) with hφdef
  have hφ0 : φ 0 = ang κ c ρ p := by simp [hφdef]
  have hφ : HasDerivAt φ D 0 := hasDerivAt_ang_line κ c ρ hp.1 q
  have hs : Real.sin (φ 0) ≠ 0 := by rw [hφ0]; exact (sin_ang_pos hp).ne'
  have hcot : HasDerivAt (fun s => Real.cos (φ s) / Real.sin (φ s)) (-D / Real.sin (φ 0) ^ 2) 0 :=
    hasDerivAt_cot_comp hφ hs
  have hre : HasDerivAt (fun s : ℝ => p.1.1.re + s * q.1.re) q.1.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const q.1.re).const_add p.1.1.re
  have him : HasDerivAt (fun s : ℝ => p.1.1.im + s * q.1.im) q.1.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const q.1.im).const_add p.1.1.im
  have h : HasDerivAt (fun s => (p.1.1.re + s * q.1.re) - (p.1.1.im + s * q.1.im) *
      (Real.cos (φ s) / Real.sin (φ s)))
      (q.1.re - (q.1.im * (Real.cos (φ 0) / Real.sin (φ 0)) +
        (p.1.1.im + 0 * q.1.im) * (-D / Real.sin (φ 0) ^ 2))) 0 :=
    hre.fun_sub (him.fun_mul hcot)
  have e : (fun s : ℝ => drvF κ c ρ ((p.1 + s • q, p.2) : St ι × ℝ)) =
      fun s => (p.1.1.re + s * q.1.re) - (p.1.1.im + s * q.1.im) *
        (Real.cos (φ s) / Real.sin (φ s)) := by
    funext s
    simp only [drvF, hφdef, Prod.fst_add, Prod.smul_fst, add_re, add_im, Complex.real_smul, mul_re,
      mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero]
  rw [e, ← hφ0]
  convert h using 1
  ring

/-! ### The identities at a state: `Θ = arg (g − w)` -/

section State

variable {κ c : ℝ} {ρ : ι → ℝ} {p : St ι × ℝ} {w : ℝ}

theorem sub_ofReal_ne_zero_of_im_pos {g : ℂ} (hg : 0 < g.im) (w : ℝ) : g - (w : ℂ) ≠ 0 := by
  intro h
  have : (g - (w : ℂ)).im = 0 := by rw [h]; rfl
  simp only [sub_im, ofReal_im, sub_zero] at this
  exact hg.ne' this

theorem normSq_pos_of_im_pos {g : ℂ} (hg : 0 < g.im) (w : ℝ) : 0 < Complex.normSq (g - (w : ℂ)) :=
  Complex.normSq_pos.2 (sub_ofReal_ne_zero_of_im_pos hg w)

theorem cot_ang_of_state (hp : 0 < p.1.1.im) (h : ang κ c ρ p = arg (p.1.1 - (w : ℂ))) :
    Real.cos (ang κ c ρ p) / Real.sin (ang κ c ρ p) = (p.1.1.re - w) / p.1.1.im := by
  have hf := sub_ofReal_ne_zero_of_im_pos hp w
  have hn : 0 < ‖p.1.1 - (w : ℂ)‖ := norm_pos_iff.2 hf
  rw [h, Complex.cos_arg hf, Complex.sin_arg]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  field_simp

theorem sin_sq_ang_of_state (hp : 0 < p.1.1.im) (h : ang κ c ρ p = arg (p.1.1 - (w : ℂ))) :
    Real.sin (ang κ c ρ p) ^ 2 = p.1.1.im ^ 2 / Complex.normSq (p.1.1 - (w : ℂ)) := by
  have hf := sub_ofReal_ne_zero_of_im_pos hp w
  rw [h, Complex.sin_arg, div_pow, Complex.sq_norm]
  simp only [sub_im, ofReal_im, sub_zero]

theorem cos_div_sin_cube_ang_of_state (hp : 0 < p.1.1.im) (h : ang κ c ρ p = arg (p.1.1 - (w : ℂ))) :
    Real.cos (ang κ c ρ p) / Real.sin (ang κ c ρ p) ^ 3 =
      (p.1.1.re - w) * Complex.normSq (p.1.1 - (w : ℂ)) / p.1.1.im ^ 3 := by
  have hf := sub_ofReal_ne_zero_of_im_pos hp w
  have hn : 0 < ‖p.1.1 - (w : ℂ)‖ := norm_pos_iff.2 hf
  rw [h, Complex.cos_arg hf, Complex.sin_arg, ← Complex.sq_norm]
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero]
  field_simp

/-- The time direction of the coordinates: `(dg, dv, dℓ) = (2/f, 0, Im(−2/f²))`. -/
def timeDir (ι : Type*) (f : ℂ) : St ι := ((2 : ℂ) / f, (0 : ι → ℝ), ((-2 : ℂ) / f ^ 2).im)

/-- The direction of the force point `j`. -/
def forceDir [DecidableEq ι] (j : ι) : St ι := (0, Pi.single j 1, 0)

/-- The force-point correction `φⱼ = ½ ρⱼ (Xⱼ − 2 Re f)/|g − vʲ|²`, `f = g − w`, `Xⱼ = vʲ − w`. -/
def phiF (ρ : ι → ℝ) (p : St ι × ℝ) (w : ℝ) (j : ι) : ℝ :=
  1 / 2 * ρ j * ((p.1.2.1 j - w) - 2 * (p.1.1.re - w)) / Complex.normSq (p.1.1 - (p.1.2.1 j : ℂ))

/-- **The bracket density is `κ`**: `(∂ₓ drvF)² · 4 (Im f)²/|f|⁴ = κ` at a state. -/
theorem partialSnd_drvF_sq_mul (hκ : 0 < κ) (hp : p ∈ dom κ c ρ) (h : ang κ c ρ p = arg (p.1.1 - (w : ℂ))) :
    partialSnd (drvF κ c ρ) p ^ 2 * (4 * (p.1.1 - (w : ℂ)).im ^ 2 / ‖p.1.1 - (w : ℂ)‖ ^ 4) = κ := by
  have hb := hp.1
  have hN := normSq_pos_of_im_pos hb w
  rw [partialSnd_drvF hp, sin_sq_ang_of_state hb h,
    show ‖p.1.1 - (w : ℂ)‖ ^ 4 = Complex.normSq (p.1.1 - (w : ℂ)) ^ 2 by rw [← Complex.sq_norm]; ring]
  simp only [sub_im, ofReal_im, sub_zero]
  have hk : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  field_simp
  rw [hk]
  ring

/-- **The force-point coefficient**: `∂_{vʲ} drvF = −½ ρⱼ + (vʲ − w) φⱼ` at a state. -/
theorem partialFst_forceDir_drvF [DecidableEq ι] (hp : p ∈ dom κ c ρ)
    (h : ang κ c ρ p = arg (p.1.1 - (w : ℂ))) (j : ι) :
    partialFst (drvF κ c ρ) p (forceDir j) = -(1 / 2) * ρ j + (p.1.2.1 j - w) * phiF ρ p w j := by
  have hb := hp.1
  have hN := normSq_pos_of_im_pos hb w
  have hNj := normSq_pos_of_im_pos hb (p.1.2.1 j)
  rw [partialFst_drvF hp, sin_sq_ang_of_state hb h]
  have hsum : ∑ i, ρ i * (((forceDir j : St ι).1 - ((forceDir j : St ι).2.1 i : ℂ)) /
      (p.1.1 - (p.1.2.1 i : ℂ))).im = ρ j * (-(1 : ℂ) / (p.1.1 - (p.1.2.1 j : ℂ))).im := by
    rw [Finset.sum_eq_single j]
    · simp [forceDir]
    · intro i _ hij
      simp [forceDir, hij]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [hsum]
  simp only [forceDir, zero_re, zero_im, zero_mul, sub_zero, mul_zero]
  rw [Complex.div_im]
  simp only [neg_re, one_re, neg_im, one_im, neg_zero, zero_mul, zero_div, zero_sub, phiF]
  have e1 : (p.1.1 - (p.1.2.1 j : ℂ)).im = p.1.1.im := by simp
  have e2 : Complex.normSq (p.1.1 - (p.1.2.1 j : ℂ)) =
      (p.1.1.re - p.1.2.1 j) ^ 2 + p.1.1.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  have e3 : Complex.normSq (p.1.1 - (w : ℂ)) = (p.1.1.re - w) ^ 2 + p.1.1.im ^ 2 := by
    rw [Complex.normSq_apply]; simp; ring
  rw [e1, e2, e3]
  rw [e2] at hNj
  have hb' : p.1.1.im ≠ 0 := hb.ne'
  field_simp
  ring

/-- **The remaining time density vanishes**: `d₀ + 2 ∑ φⱼ = 0`, with
`d₀ = ∂_{timeDir} drvF + ½ ∂ₓ² drvF · 4 (Im f)²/|f|⁴` (uses `2 √κ χ = 4 − κ`). -/
theorem timeDensity_add_eq_zero (hκ : 0 < κ) (hp : p ∈ dom κ c ρ) (h : ang κ c ρ p = arg (p.1.1 - (w : ℂ))) :
    partialFst (drvF κ c ρ) p (timeDir ι (p.1.1 - (w : ℂ))) +
      1 / 2 * partialSndSnd (drvF κ c ρ) p * (4 * (p.1.1 - (w : ℂ)).im ^ 2 / ‖p.1.1 - (w : ℂ)‖ ^ 4) +
      2 * ∑ j, phiF ρ p w j = 0 := by
  have hb := hp.1
  have hN := normSq_pos_of_im_pos hb w
  set f : ℂ := p.1.1 - (w : ℂ) with hf
  set a : ℝ := p.1.1.re - w with ha
  set b : ℝ := p.1.1.im with hbdef
  have hfre : f.re = a := by simp [hf, ha]
  have hfim : f.im = b := by simp [hf, hbdef]
  have hNf : Complex.normSq f = a ^ 2 + b ^ 2 := by rw [Complex.normSq_apply, hfre, hfim]; ring
  have hf0 : f ≠ 0 := sub_ofReal_ne_zero_of_im_pos hb w
  have hk : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hchi : Real.sqrt κ * QuantumZipper.chiC κ = 2 - κ / 2 := by
    simp only [QuantumZipper.chiC]
    field_simp
    rw [hk]
  rw [partialFst_drvF hp, partialSndSnd_drvF hp, sin_sq_ang_of_state hb h, cot_ang_of_state hb h,
    mul_div_assoc (-(Real.sqrt κ ^ 2 / 2) * p.1.1.im), cos_div_sin_cube_ang_of_state hb h,
    show ‖f‖ ^ 4 = Complex.normSq f ^ 2 by rw [← Complex.sq_norm]; ring]
  simp only [timeDir]
  have hN2 : 0 < a ^ 2 + b ^ 2 := by rw [← hNf]; exact Complex.normSq_pos.2 hf0
  have e2re : ((2 : ℂ) / f).re = 2 * a / (a ^ 2 + b ^ 2) := by
    rw [Complex.div_re, hNf, hfre, hfim]; simp
  have e2im : ((2 : ℂ) / f).im = -(2 * b) / (a ^ 2 + b ^ 2) := by
    rw [Complex.div_im, hNf, hfre, hfim]; simp; ring
  have esq : ((-2 : ℂ) / f ^ 2).im = 4 * a * b / (a ^ 2 + b ^ 2) ^ 2 := by
    have hf2 : Complex.normSq (f ^ 2) = (a ^ 2 + b ^ 2) ^ 2 := by rw [map_pow, hNf]
    rw [Complex.div_im, hf2]
    simp only [pow_two, mul_re, mul_im, hfre, hfim, neg_re, neg_im, re_ofNat, im_ofNat, neg_zero]
    ring
  set S : ℝ := ∑ j, ρ j * (((2 : ℂ) / f - ((0 : ι → ℝ) j : ℂ)) / (p.1.1 - (p.1.2.1 j : ℂ))).im with hS
  set Φ : ℝ := ∑ j, phiF ρ p w j with hΦ
  have hmerge : -((a ^ 2 + b ^ 2) / (2 * b)) * S + 2 * Φ = 0 := by
    rw [hS, hΦ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    set X : ℝ := p.1.2.1 j - w with hX
    have hgj : p.1.1 - (p.1.2.1 j : ℂ) = f - (X : ℂ) := by
      rw [hf, hX]; push_cast; ring
    have hMj : Complex.normSq (f - (X : ℂ)) = (a - X) ^ 2 + b ^ 2 := by
      rw [Complex.normSq_apply]; simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero, hfre, hfim]
      ring
    have hM0 : 0 < (a - X) ^ 2 + b ^ 2 := by positivity
    have hP : ((2 : ℂ) / f - ((0 : ι → ℝ) j : ℂ)) / (f - (X : ℂ)) = 2 / (f * (f - (X : ℂ))) := by
      simp only [Pi.zero_apply, ofReal_zero, sub_zero]
      have hfX : f - (X : ℂ) ≠ 0 := by
        intro h0; have := congrArg Complex.im h0; simp [hfim] at this; exact hb.ne' this
      field_simp
    have hPn : Complex.normSq (f * (f - (X : ℂ))) = (a ^ 2 + b ^ 2) * ((a - X) ^ 2 + b ^ 2) := by
      rw [map_mul, hNf, hMj]
    have hPim : (f * (f - (X : ℂ))).im = b * (2 * a - X) := by
      simp only [mul_im, sub_re, ofReal_re, sub_im, ofReal_im, sub_zero, hfre, hfim]; ring
    have hIm : ((2 : ℂ) / (f * (f - (X : ℂ)))).im = -(2 * b * (2 * a - X)) /
        ((a ^ 2 + b ^ 2) * ((a - X) ^ 2 + b ^ 2)) := by
      rw [Complex.div_im, hPn, hPim]; simp; ring
    rw [hgj, hP, hIm]
    simp only [phiF]
    rw [hgj, hMj, ← ha, ← hX]
    field_simp
    ring
  have hmain : ((2 : ℂ) / f).re - ((2 : ℂ) / f).im * (a / b) +
      b * (-(1 / 2) * S - Real.sqrt κ * QuantumZipper.chiC κ / 2 * ((-2 : ℂ) / f ^ 2).im) /
        (b ^ 2 / Complex.normSq f) +
      1 / 2 * (-(Real.sqrt κ ^ 2 / 2) * b * (a * Complex.normSq f / b ^ 3)) *
        (4 * b ^ 2 / Complex.normSq f ^ 2) + 2 * Φ = 0 := by
    rw [e2re, e2im, esq, hNf, hk, hchi]
    have hb0 : b ≠ 0 := hb.ne'
    have hN0 : a ^ 2 + b ^ 2 ≠ 0 := hN2.ne'
    have hrest : 2 * Φ = (a ^ 2 + b ^ 2) / (2 * b) * S := by linarith
    rw [hrest]
    field_simp
    ring
  rw [← ha, ← hbdef, ← hf, hfim]
  exact hmain

end State

end InteractingSLE.Sec2.T26Pv
