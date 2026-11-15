/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.Complex.BasicsReflection
import QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# The shared-side phase anchor: the analytic core of Lemma R.6

Packet PROVE-R16. Supplement §5.6, **Lemma R.6** (`source/spec/p433-480.md` L1024–L1031, pp. 475–476):

> *Proof.* The current chart of `U` composed with the inverse current chart of `C` is conformal on the
> indicated Jordan subdomain. It extends by Schwarz reflection across the connected open interval
> `J`; its derivative is positive there because the domain is locally on the upper side in both
> charts. Its inherited logarithmic derivative therefore has imaginary part one constant `2πn` on
> this whole interval.
>
> On the shared unvisited flow-side collar both initial pocket branches have the same exact height
> … The composed transition logarithm consequently has imaginary part zero on that collar. Thus
> `n = 0` on all of `J` …

R41 keeps this argument unchanged (`ig1_ztip_elimination.txt` L349–L351: "R.6 … compares the inherited
germs at a selected rational interior pocket visit … Its shared-side reflection and constant lattice
phase do not use the deleted all-contact assertions").

This file proves the two analytic steps, for a transition map `φ` given near each point of `J`
(`IsRealBoundaryConformal φ x r`: holomorphic and injective on the upper half-disc `ℍ ∩ B(x, r)`,
continuous up to its real diameter, real there, and mapping the half-disc into `ℍ` — "the domain is
locally on the upper side in both charts"). The reflected map is `QuantumZipper.CA.schwarzReflect φ`.

## Main results

* `IsRealBoundaryConformal.differentiableOn_schwarzReflect`: the reflection is holomorphic on
  `B(x, r)` (QuantumZipper's Schwarz reflection principle);
* `IsRealBoundaryConformal.deriv_schwarzReflect_pos`: **its derivative at every real point of
  `B(x, r)` is a positive real number**;
* `exists_int_im_eq_of_exp_pos`: a logarithm of a positive real number has imaginary part in `2πℤ`;
* `r6_phase_const`: **Lemma R.6, analytic core.** If `J ⊆ ℝ` is preconnected, `φ` is
  real-boundary-conformal near each point of `J`, and `L` is a continuous logarithm of the boundary
  derivative along `J` (`exp (L y) = (schwarzReflect φ)'(y)`), then `Im L ≡ 2πn` on `J` for one
  integer `n`; and if `Im L` vanishes at one point of `J` (the shared collar), it vanishes on all of `J`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate
open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE

namespace R16

/-- `φ` is **conformal on the upper half-disc `ℍ ∩ B(x, r)` with real boundary values**: holomorphic and
injective there, mapping it into `ℍ`, continuous on `ℍ̄ ∩ B(x, r)` and real on its real diameter. -/
def IsRealBoundaryConformal (φ : ℂ → ℂ) (x r : ℝ) : Prop :=
  DifferentiableOn ℂ φ (H ∩ ball (x : ℂ) r) ∧ ContinuousOn φ (Hbar ∩ ball (x : ℂ) r) ∧
    (∀ z ∈ ball (x : ℂ) r, z.im = 0 → (φ z).im = 0) ∧ MapsTo φ (H ∩ ball (x : ℂ) r) H ∧
    InjOn φ (H ∩ ball (x : ℂ) r)

variable {φ : ℂ → ℂ} {x r : ℝ}

/-- The reflection is the unique holomorphic extension: it agrees on `B(x, r)` with the extension
given by the Schwarz reflection principle, hence is holomorphic there. -/
theorem IsRealBoundaryConformal.differentiableOn_schwarzReflect (h : IsRealBoundaryConformal φ x r) :
    DifferentiableOn ℂ (schwarzReflect φ) (ball (x : ℂ) r) := by
  obtain ⟨G, hG, hGφ, hGc⟩ := QuantumZipper.CA.exists_reflection_extension h.1 h.2.1 h.2.2.1
  refine hG.congr fun z hz => ?_
  unfold schwarzReflect
  split_ifs with him
  · exact (hGφ ⟨him, hz⟩).symm
  · have hcz : conj z ∈ ball (x : ℂ) r := QuantumZipper.CA.conj_mem_ball_ofReal hz
    have hcz' : conj z ∈ Hbar := by
      show 0 ≤ (conj z).im
      rw [conj_im]; linarith [not_le.1 him]
    rw [← hGφ ⟨hcz', hcz⟩, hGc z hz, RCLike.conj_conj]

/-- Signs of the imaginary part of the reflected map follow the sign of the imaginary part. -/
theorem IsRealBoundaryConformal.im_schwarzReflect (h : IsRealBoundaryConformal φ x r) {z : ℂ}
    (hz : z ∈ ball (x : ℂ) r) :
    (0 < z.im → 0 < (schwarzReflect φ z).im) ∧ (z.im = 0 → (schwarzReflect φ z).im = 0) ∧
      (z.im < 0 → (schwarzReflect φ z).im < 0) := by
  refine ⟨fun hpos => ?_, fun h0 => ?_, fun hneg => ?_⟩
  · simp only [schwarzReflect, hpos.le, ↓reduceIte]; exact h.2.2.2.1 ⟨hpos, hz⟩
  · simp only [schwarzReflect, h0.ge, ↓reduceIte]; exact h.2.2.1 z hz h0
  · simp only [schwarzReflect, not_le.2 hneg, ↓reduceIte, conj_im, neg_lt_zero]
    have hcz : conj z ∈ ball (x : ℂ) r := QuantumZipper.CA.conj_mem_ball_ofReal hz
    have hczH : conj z ∈ H := by
      show 0 < (conj z).im
      rw [conj_im]; linarith
    exact h.2.2.2.1 ⟨hczH, hcz⟩

/-- At a real point of the disc the derivative of the reflection is real. -/
theorem IsRealBoundaryConformal.im_deriv_schwarzReflect (h : IsRealBoundaryConformal φ x r) {y : ℝ}
    (hy : (y : ℂ) ∈ ball (x : ℂ) r) : (deriv (schwarzReflect φ) y).im = 0 := by
  have hd := ((h.differentiableOn_schwarzReflect).differentiableAt
    (isOpen_ball.mem_nhds hy)).hasDerivAt
  have h1 : HasDerivAt (fun z => -I * schwarzReflect φ z) (-I * deriv (schwarzReflect φ) y) y :=
    hd.const_mul (-I)
  have h2 := h1.real_of_complex
  have hzero : (fun t : ℝ => (-I * schwarzReflect φ (t : ℂ)).re) =ᶠ[𝓝 y] fun _ => 0 := by
    have hopen : ∀ᶠ t : ℝ in 𝓝 y, (t : ℂ) ∈ ball (x : ℂ) r :=
      (continuous_ofReal.tendsto y).eventually (isOpen_ball.mem_nhds hy)
    filter_upwards [hopen] with t ht
    have := (h.im_schwarzReflect ht).2.1 (by simp)
    simp [this]
  have h3 := h2.congr_of_eventuallyEq hzero.symm
  have h4 := h3.unique (hasDerivAt_const y (0 : ℝ))
  simpa using h4

/-- At a real point of the disc the derivative of the reflection has nonnegative real part ("the
domain is locally on the upper side in both charts"). -/
theorem IsRealBoundaryConformal.re_deriv_schwarzReflect_nonneg (h : IsRealBoundaryConformal φ x r)
    {y : ℝ} (hy : (y : ℂ) ∈ ball (x : ℂ) r) : 0 ≤ (deriv (schwarzReflect φ) y).re := by
  have hd := ((h.differentiableOn_schwarzReflect).differentiableAt
    (isOpen_ball.mem_nhds hy)).hasDerivAt
  -- `t ↦ Im (φ̂ (y + t i))` has derivative `Re φ̂'(y)` at `0`
  have hpath : HasDerivAt (fun z : ℂ => (y : ℂ) + z * I) I 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const I).const_add (y : ℂ)
  have hcomp : HasDerivAt (fun z : ℂ => schwarzReflect φ ((y : ℂ) + z * I))
      (deriv (schwarzReflect φ) y * I) 0 := by
    have hd' : HasDerivAt (schwarzReflect φ) (deriv (schwarzReflect φ) y) ((y : ℂ) + 0 * I) := by
      simpa using hd
    exact hd'.comp (0 : ℂ) hpath
  have h1 := (hcomp.const_mul (-I)).real_of_complex
  have hval : (-I * (deriv (schwarzReflect φ) y * I)).re = (deriv (schwarzReflect φ) y).re := by
    have : -I * (deriv (schwarzReflect φ) y * I) = deriv (schwarzReflect φ) y := by
      rw [mul_comm (deriv _ _) I, ← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
    rw [this]
  rw [hval] at h1
  have hslope := h1.tendsto_slope_zero_right
  refine ge_of_tendsto hslope ?_
  have hopen : ∀ᶠ t : ℝ in 𝓝 0, ((y : ℂ) + ((0 + t : ℝ) : ℂ) * I) ∈ ball (x : ℂ) r := by
    have hc : Continuous fun t : ℝ => (y : ℂ) + ((0 + t : ℝ) : ℂ) * I := by fun_prop
    exact (hc.tendsto 0).eventually (isOpen_ball.mem_nhds (by simpa using hy))
  filter_upwards [nhdsWithin_le_nhds hopen, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  have him0 : (-I * schwarzReflect φ ((y : ℂ) + ((0 : ℝ) : ℂ) * I)).re = 0 := by
    have := (h.im_schwarzReflect (z := (y : ℂ)) hy).2.1 (by simp)
    simp [this]
  have himt : 0 < (-I * schwarzReflect φ ((y : ℂ) + ((0 + t : ℝ) : ℂ) * I)).re := by
    have := (h.im_schwarzReflect ht).1 (by simp [htpos'])
    simpa using this
  rw [him0, sub_zero, smul_eq_mul]
  exact (mul_pos (inv_pos.2 htpos') himt).le

/-- The reflection is injective on the real diameter: it is nondecreasing there (nonnegative
derivative) and not constant on any real interval (identity theorem, injectivity on the half-disc). -/
theorem IsRealBoundaryConformal.injOn_real (h : IsRealBoundaryConformal φ x r) :
    InjOn (fun t : ℝ => (schwarzReflect φ (t : ℂ)).re) {t : ℝ | (t : ℂ) ∈ ball (x : ℂ) r} := by
  set g : ℝ → ℝ := fun t => (schwarzReflect φ (t : ℂ)).re with hg
  set D : Set ℝ := {t : ℝ | (t : ℂ) ∈ ball (x : ℂ) r} with hD
  have hDeq : D = Ioo (x - r) (x + r) := by
    ext t
    simp only [hD, mem_ofPred_eq, mem_ball, dist_eq, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      mem_Ioo, abs_lt]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hDo : IsOpen D := by rw [hDeq]; exact isOpen_Ioo
  have hderiv : ∀ t ∈ D, HasDerivAt g (deriv (schwarzReflect φ) t).re t := fun t ht =>
    (((h.differentiableOn_schwarzReflect).differentiableAt
      (isOpen_ball.mem_nhds ht)).hasDerivAt).real_of_complex
  have hmono : MonotoneOn g D := by
    refine monotoneOn_of_deriv_nonneg (by rw [hDeq]; exact convex_Ioo _ _)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => ?_)
    rw [(hderiv t (interior_subset ht)).deriv]
    exact h.re_deriv_schwarzReflect_nonneg (interior_subset ht : t ∈ D)
  have hGreal : ∀ t ∈ D, schwarzReflect φ (t : ℂ) = ((g t : ℝ) : ℂ) := fun t ht => by
    apply Complex.ext
    · simp [hg]
    · rw [ofReal_im]; exact (h.im_schwarzReflect ht).2.1 (by simp)
  have hGφ : ∀ t ∈ D, schwarzReflect φ (t : ℂ) = φ t := fun t _ => by
    simp [schwarzReflect]
  -- strict monotonicity
  intro t₁ ht₁ t₂ ht₂ heq
  by_contra hne
  wlog hlt : t₁ < t₂ generalizing t₁ t₂
  · exact this ht₂ ht₁ heq.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have hconst : ∀ t ∈ Ioo t₁ t₂, (t : ℂ) ∈ ball (x : ℂ) r ∧ φ t = ((g t₁ : ℝ) : ℂ) := by
    intro t ht
    have htD : t ∈ D := by
      rw [hDeq] at ht₁ ht₂ ⊢; exact ⟨ht₁.1.trans ht.1, ht.2.trans ht₂.2⟩
    refine ⟨htD, ?_⟩
    have h1 : g t₁ ≤ g t := hmono ht₁ htD ht.1.le
    have h2 : g t ≤ g t₂ := hmono htD ht₂ ht.2.le
    have heq' : g t = g t₁ := le_antisymm (heq ▸ h2) h1
    rw [← hGφ t htD, hGreal t htD, heq']
  have hall := QuantumZipper.CA.eqOn_const_of_eq_const_on_Ioo h.1 h.2.1 h.2.2.1 hlt hconst
  -- two distinct points of the upper half-disc have the same image
  have hr : 0 < r := by
    have : dist (t₁ : ℂ) (x : ℂ) < r := ht₁
    exact (dist_nonneg).trans_lt this
  set z₁ : ℂ := (x : ℂ) + ((r / 4 : ℝ) : ℂ) * I
  set z₂ : ℂ := (x : ℂ) + ((r / 2 : ℝ) : ℂ) * I
  have hmem : ∀ c : ℝ, 0 < c → c < r → (x : ℂ) + (c : ℂ) * I ∈ H ∩ ball (x : ℂ) r := by
    intro c hc hcr
    refine ⟨?_, ?_⟩
    · show 0 < ((x : ℂ) + (c : ℂ) * I).im
      simp [hc]
    · rw [mem_ball, dist_eq, add_sub_cancel_left, norm_mul, norm_real, norm_I, mul_one,
        Real.norm_eq_abs, abs_of_pos hc]
      exact hcr
  have hz₁ := hmem (r / 4) (by positivity) (by linarith)
  have hz₂ := hmem (r / 2) (by positivity) (by linarith)
  have hHb : ∀ z : ℂ, z ∈ H → z ∈ Hbar := fun z hz => show (0 : ℝ) ≤ z.im from le_of_lt hz
  have himg : φ z₁ = φ z₂ := by
    rw [hall z₁ ⟨hHb _ hz₁.1, hz₁.2⟩, hall z₂ ⟨hHb _ hz₂.1, hz₂.2⟩]
  have := h.2.2.2.2 hz₁ hz₂ himg
  have him := congrArg Complex.im this
  simp at him
  linarith

/-- The reflection is injective on the whole disc. -/
theorem IsRealBoundaryConformal.injOn_schwarzReflect (h : IsRealBoundaryConformal φ x r) :
    InjOn (schwarzReflect φ) (ball (x : ℂ) r) := by
  intro z hz w hw heq
  have hs := h.im_schwarzReflect hz
  have ht := h.im_schwarzReflect hw
  rcases lt_trichotomy z.im 0 with hzi | hzi | hzi <;>
    rcases lt_trichotomy w.im 0 with hwi | hwi | hwi
  · -- both below: reflect
    have hcz : conj z ∈ H ∩ ball (x : ℂ) r :=
      ⟨show 0 < (conj z).im by rw [conj_im]; linarith, QuantumZipper.CA.conj_mem_ball_ofReal hz⟩
    have hcw : conj w ∈ H ∩ ball (x : ℂ) r :=
      ⟨show 0 < (conj w).im by rw [conj_im]; linarith, QuantumZipper.CA.conj_mem_ball_ofReal hw⟩
    have h1 : φ (conj z) = φ (conj w) := by
      have e := congrArg conj heq
      simp only [schwarzReflect, not_le.2 hzi, not_le.2 hwi, ↓reduceIte, RCLike.conj_conj] at e
      exact e
    have := h.2.2.2.2 hcz hcw h1
    simpa using congrArg conj this
  all_goals first
    | (have a := hs.2.2 hzi; have b := ht.2.1 hwi; rw [heq] at a; linarith)
    | (have a := hs.2.2 hzi; have b := ht.1 hwi; rw [heq] at a; linarith)
    | (have a := hs.2.1 hzi; have b := ht.2.2 hwi; rw [heq] at a; linarith)
    | (have a := hs.2.1 hzi; have b := ht.1 hwi; rw [heq] at a; linarith)
    | (have a := hs.1 hzi; have b := ht.2.2 hwi; rw [heq] at a; linarith)
    | (have a := hs.1 hzi; have b := ht.2.1 hwi; rw [heq] at a; linarith)
    | skip
  · -- both real
    have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzi])
    have hwr : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hwi])
    have hzD : ((z.re : ℝ) : ℂ) ∈ ball (x : ℂ) r := hzr ▸ hz
    have hwD : ((w.re : ℝ) : ℂ) ∈ ball (x : ℂ) r := hwr ▸ hw
    have := h.injOn_real hzD hwD (by
      show (schwarzReflect φ _).re = (schwarzReflect φ _).re
      rw [← hzr, ← hwr, heq])
    rw [hzr, hwr, this]
  · -- both above
    have h1 : φ z = φ w := by
      simpa only [schwarzReflect, hzi.le, hwi.le, ↓reduceIte] using heq
    exact h.2.2.2.2 ⟨hzi, hz⟩ ⟨hwi, hw⟩ h1

/-- **The transition map has positive derivative on the shared interval** (Lemma R.6 proof: "It
extends by Schwarz reflection across the connected open interval `J`; its derivative is positive
there because the domain is locally on the upper side in both charts"). -/
theorem IsRealBoundaryConformal.deriv_schwarzReflect_pos (h : IsRealBoundaryConformal φ x r)
    {y : ℝ} (hy : (y : ℂ) ∈ ball (x : ℂ) r) :
    (deriv (schwarzReflect φ) y).im = 0 ∧ 0 < (deriv (schwarzReflect φ) y).re := by
  have him := h.im_deriv_schwarzReflect hy
  refine ⟨him, lt_of_le_of_ne (h.re_deriv_schwarzReflect_nonneg hy) fun hre => ?_⟩
  exact QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball h.differentiableOn_schwarzReflect
    h.injOn_schwarzReflect hy (Complex.ext hre.symm him)

/-! ### The constant lattice phase -/

/-- A logarithm of a positive real number has imaginary part in `2πℤ`. -/
theorem exists_int_im_eq_of_exp_pos {w : ℂ} (hre : 0 < (exp w).re) (him : (exp w).im = 0) :
    ∃ n : ℤ, w.im = 2 * Real.pi * n := by
  rw [Complex.exp_re] at hre
  rw [Complex.exp_im] at him
  have hsin : Real.sin w.im = 0 :=
    (mul_eq_zero.1 him).resolve_left (Real.exp_pos _).ne'
  have hcos : 0 < Real.cos w.im := pos_of_mul_pos_right hre (Real.exp_pos _).le
  have hcos1 : Real.cos w.im = 1 := by
    have := Real.sin_sq_add_cos_sq w.im
    rw [hsin] at this
    nlinarith
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hcos1
  exact ⟨n, by rw [← hn]; ring⟩

/-- A continuous function on a preconnected set with values in `2πℤ` is constant. -/
theorem im_eq_of_exp_pos {J : Set ℝ} (hJ : IsPreconnected J) {L : ℝ → ℂ} (hLc : ContinuousOn L J)
    (hpos : ∀ y ∈ J, 0 < (exp (L y)).re ∧ (exp (L y)).im = 0) {y₁ y₂ : ℝ} (h₁ : y₁ ∈ J)
    (h₂ : y₂ ∈ J) : (L y₁).im = (L y₂).im := by
  have hS : IsPreconnected ((fun y => (L y).im) '' J) :=
    hJ.image _ (Complex.continuous_im.comp_continuousOn hLc)
  have key : ∀ a ∈ J, ∀ b ∈ J, (L a).im < (L b).im → False := by
    intro a ha b hb hab
    obtain ⟨n, hn⟩ := exists_int_im_eq_of_exp_pos (hpos a ha).1 (hpos a ha).2
    obtain ⟨m, hm⟩ := exists_int_im_eq_of_exp_pos (hpos b hb).1 (hpos b hb).2
    have hnm : n < m := by
      rw [hn, hm] at hab
      exact_mod_cast lt_of_mul_lt_mul_left hab (by positivity)
    have hnm' : (n : ℝ) + 1 ≤ m := by exact_mod_cast hnm
    have hmid : 2 * Real.pi * n + Real.pi ∈ (fun y => (L y).im) '' J := by
      refine hS.Icc_subset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb) ⟨?_, ?_⟩
      · rw [hn]; linarith [Real.pi_pos]
      · rw [hm]; nlinarith [Real.pi_pos]
    obtain ⟨c, hc, hce⟩ := hmid
    obtain ⟨k, hk⟩ := exists_int_im_eq_of_exp_pos (hpos c hc).1 (hpos c hc).2
    simp only at hce
    rw [hk] at hce
    have h2 : (2 * (k - n) : ℝ) = 1 := by
      have := Real.pi_pos
      field_simp at hce ⊢
      nlinarith
    have h3 : (2 * (k - n) : ℤ) = 1 := by exact_mod_cast h2
    omega
  rcases lt_trichotomy (L y₁).im (L y₂).im with h | h | h
  · exact (key y₁ h₁ y₂ h₂ h).elim
  · exact h
  · exact (key y₂ h₂ y₁ h₁ h).elim

/-- **Lemma R.6, analytic core** (`source/spec/p433-480.md` L1029–L1031). Let `J ⊆ ℝ` be preconnected
(the shared real interval), let the transition map `φ` be conformal with real boundary values on an
upper half-disc about each point of `J`, and let `L` be a continuous logarithm along `J` of its
boundary derivative (the inherited logarithmic derivative, `exp (L y) = (schwarzReflect φ)'(y)`).
Then `Im L` is one constant `2πn` on `J`; and if `Im L` vanishes at one point of `J` (the shared
unvisited collar, where both initial branches carry the same exact height), then `Im L = 0` on all
of `J`. -/
theorem r6_phase_const {J : Set ℝ} (hJ : IsPreconnected J)
    (hloc : ∀ y ∈ J, ∃ r > 0, IsRealBoundaryConformal φ y r) {L : ℝ → ℂ} (hLc : ContinuousOn L J)
    (hexp : ∀ y ∈ J, exp (L y) = deriv (schwarzReflect φ) y) :
    (∃ n : ℤ, ∀ y ∈ J, (L y).im = 2 * Real.pi * n) ∧
      ∀ y₀ ∈ J, (L y₀).im = 0 → ∀ y ∈ J, (L y).im = 0 := by
  have hpos : ∀ y ∈ J, 0 < (exp (L y)).re ∧ (exp (L y)).im = 0 := by
    intro y hy
    obtain ⟨r, hr, hφ⟩ := hloc y hy
    have hyb : (y : ℂ) ∈ ball (y : ℂ) r := mem_ball_self hr
    obtain ⟨h1, h2⟩ := hφ.deriv_schwarzReflect_pos hyb
    rw [hexp y hy]
    exact ⟨h2, h1⟩
  refine ⟨?_, fun y₀ hy₀ h0 y hy => (im_eq_of_exp_pos hJ hLc hpos hy hy₀).trans h0⟩
  rcases J.eq_empty_or_nonempty with hJe | ⟨y₀, hy₀⟩
  · exact ⟨0, fun y hy => by rw [hJe] at hy; exact hy.elim⟩
  obtain ⟨n, hn⟩ := exists_int_im_eq_of_exp_pos (hpos y₀ hy₀).1 (hpos y₀ hy₀).2
  exact ⟨n, fun y hy => (im_eq_of_exp_pos hJ hLc hpos hy hy₀).trans hn⟩

end R16

end InteractingSLE
