/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.HullDetGenMob
import InteractingSLE.Spec.Sec5.CrossRestartMobius
import InteractingSLE.Foundations.Complex.DerivLog
import QuantumZipper.Proofs.RS.GenerationCor

/-!
# Coupling means through a real Möbius conjugation (deterministic)

Packet PROVE-HULLDET, the deterministic core of BR4a's relative chain (`HullDetGen.BR4aRelChainStatement`, its mean
identity). Let `w`, `U` be continuous drivers from `0` whose Loewner maps are conjugated by the target change:
`g̃_q ∘ mob v = N ∘ g_t` on `ℍ ∖ K_t`, with `N = nf α κN P` a real Möbius map (`κN > 0`; the conjugation of
`Sec5.CrossRestart.exists_loewner_mobius_image`). Then the two coupling means differ, through the chart `brChart v`, by
a bounded harmonic function of `ζ = g_t(z)` alone:

* **`exists_const_im_logDeriv`** (the analytic chain-rule lift): `Im L̃(mob z) − Im L(z) + lift(z) + 2 arg(g_t z − P)`
  is constant on `ℍ ∖ K_t` (`L`, `L̃` the canonical branches `logDerivFwd`; `lift` the lift of `brChart v`): its complex
  version `Λ` has `exp Λ ≡ κN`, so it is `2πi`-integer valued up to a constant, and continuous on a connected set;
* **`exists_const_couplingMean_mob`**: hence `𝔥̃_q ∘ mob v − 𝔥_t − χ · lift = Δ ∘ g_t` with `Δ` a bounded harmonic
  function on `ℍ`; if the boundary step data `β̃(N x − U_q) − β(x − w_t) + 2χ arg(x − P)` is a constant off a
  finite set, `Δ` is constant (uniqueness of bounded harmonic extensions);
* **`couplingMean_mob_eq`**: with one boundary limit `0`, the mean identity `𝔥̃_q (mob v z) = 𝔥_t z + χ · lift z`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Complex
open QuantumZipper (H fwdHull fwdMap logDerivFwd)

namespace InteractingSLE.Supp8.HullDetGen

open Theorem14.BR4aPath ConformalImage Sec5.CrossRestart

/-! ### The analytic chain-rule lift of the conjugation -/

section ChainRule

variable {w U : ℝ → ℝ} {t q : ℝ} {v α κN P : ℝ}

theorem gmap_mem_H (hw : Continuous w) (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H \ fwdHull w t) : gmap w t z ∈ H := by
  have h := QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht hz
  change 0 < (fwdMap w t z + (w t : ℂ)).im
  rw [Complex.add_im, Complex.ofReal_im, add_zero]
  exact h

theorem sub_ofReal_mem_H {ζ : ℂ} (hζ : ζ ∈ H) (P : ℝ) : ζ - P ∈ H := by
  change 0 < (ζ - P).im
  rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact hζ

/-- Points off the hull stay off the image hull. -/
theorem mob_mem_compl (hK : mob v '' fwdHull w t = fwdHull U q) {z : ℂ} (hz : z ∈ H \ fwdHull w t) :
    mob v z ∈ H \ fwdHull U q := by
  refine ⟨mob_mem_H v hz.1, fun hm => ?_⟩
  rw [← hK] at hm
  obtain ⟨z', hz', he⟩ := hm
  have hz'H : z' ∈ H := (QuantumZipper.fwdHull_mono).2 _ hz'
  have := (QuantumZipper.CA.bijOn_realMobius_H (by norm_num : (0 : ℝ) < 1 * 1 - 0 * v)).injOn hz'H hz.1 he
  exact hz.2 (this ▸ hz')

/-- The derivative of `mob v` is `1/(v z + 1)²`. -/
theorem hasDerivAt_mob {z : ℂ} (hz : (v : ℂ) * z + 1 ≠ 0) : HasDerivAt (mob v) (1 / ((v : ℂ) * z + 1) ^ 2) z := by
  have he : mob v = fun z : ℂ => z / ((v : ℂ) * z + 1) := funext fun z => mob_apply v z
  rw [he]
  have h1 : HasDerivAt (fun z : ℂ => (v : ℂ) * z + 1) v z := by
    simpa using ((hasDerivAt_id z).const_mul (v : ℂ)).add_const (1 : ℂ)
  have h2 := (hasDerivAt_id' z).div h1 hz
  refine h2.congr_deriv ?_
  ring

theorem mob_den_ne_zero {z : ℂ} (hz : z ∈ H) : (v : ℂ) * z + 1 ≠ 0 := by
  intro h0
  have h := mob_apply v z
  rw [h0, div_zero] at h
  exact ne_zero_of_mem_H' (mob_mem_H v hz) h

/-- The derivative of the real Möbius map `nf α κ P` is `κ/(ζ − P)²`. -/
theorem hasDerivAt_nf {ζ : ℂ} (hζ : ζ - P ≠ 0) :
    HasDerivAt (nf α κN P) ((κN : ℂ) / (ζ - P) ^ 2) ζ := by
  have h1 : HasDerivAt (fun ζ : ℂ => ζ - (P : ℂ)) 1 ζ := (hasDerivAt_id' ζ).sub_const _
  have h2 := (h1.inv hζ).const_mul (κN : ℂ)
  have h3 := h2.const_sub (α : ℂ)
  have he : nf α κN P = fun ζ : ℂ => (α : ℂ) - (κN : ℂ) * (ζ - (P : ℂ))⁻¹ := by
    funext ζ
    simp only [nf, div_eq_mul_inv]
  rw [he]
  refine h3.congr_deriv ?_
  field_simp

/-- `exp (k log x) = x ^ k` for `k = 2` and `x ≠ 0`. -/
theorem exp_two_mul_log {x : ℂ} (hx : x ≠ 0) : Complex.exp (2 * Complex.log x) = x ^ 2 := by
  rw [show (2 : ℂ) * Complex.log x = Complex.log x + Complex.log x by ring, Complex.exp_add, Complex.exp_log hx, sq]

/-- **The analytic chain-rule lift of the conjugation**: `Im L̃(mob z) − Im L(z) + lift(z) + 2 arg(g_t z − P)` is
constant on `ℍ ∖ K_t`. Its complex version `Λ = L̃ ∘ mob − L + (−2 log(−1/mob) + 2 log(−1/·)) + 2 log(g_t − P)` has
`exp Λ = (g̃_q ∘ mob)' / g_t' · (mob/·)² · (g_t − P)² = N'(g_t) (v z + 1)⁻² · (v z + 1)² (g_t − P)² = κN`; so its
imaginary part is `2π`-integer valued up to a constant, and continuous on the connected set `ℍ ∖ K_t`. -/
theorem exists_const_im_logDeriv (hw : Continuous w) (hw0 : w 0 = 0) (hU : Continuous U) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hK : mob v '' fwdHull w t = fwdHull U q)
    (hconj : ∀ z ∈ H \ fwdHull w t, gmap U q (mob v z) = nf α κN P (gmap w t z)) :
    ∃ c : ℝ, ∀ z ∈ H \ fwdHull w t,
      (logDerivFwd U q (mob v z)).im - (logDerivFwd w t z).im + (brChart v).2.2 z +
        2 * Complex.arg (gmap w t z - P) = c := by
  set S : Set ℂ := H \ fwdHull w t with hS
  have hSo : IsOpen S := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht
  have hSc : IsPreconnected S := QuantumZipper.RS.isPreconnected_compl_fwdHull hw hw0 ht
  set Λ : ℂ → ℂ := fun z => logDerivFwd U q (mob v z) - logDerivFwd w t z +
    (-2 * Complex.log (-(mob v z)⁻¹) - -2 * Complex.log (-z⁻¹)) + 2 * Complex.log (gmap w t z - P) with hΛ
  have hΛim : ∀ z, (Λ z).im = (logDerivFwd U q (mob v z)).im - (logDerivFwd w t z).im + (brChart v).2.2 z +
      2 * Complex.arg (gmap w t z - P) := by
    intro z
    simp only [hΛ, Complex.add_im, Complex.sub_im]
    have h2 : (2 * Complex.log (gmap w t z - P)).im = 2 * Complex.arg (gmap w t z - P) := by
      rw [Complex.mul_im, Complex.log_im]
      simp
    rw [h2]
    rfl
  -- `exp Λ = κN` on `S`
  have hexp : ∀ z ∈ S, Complex.exp (Λ z) = κN := by
    intro z hz
    have hzH : z ∈ H := hz.1
    have hz0 := ne_zero_of_mem_H' hzH
    have hmz := mob_mem_compl hK hz
    have hden := mob_den_ne_zero (v := v) hzH
    have hζ := gmap_mem_H hw ht hz
    have hζP0 : gmap w t z - P ≠ 0 := ne_zero_of_mem_H' (sub_ofReal_mem_H hζ P)
    have hmob0 : mob v z ≠ 0 := ne_zero_of_mem_H' (mob_mem_H v hzH)
    have hd1 : HasDerivAt (fun z => gmap U q (mob v z))
        (Complex.exp (logDerivFwd U q (mob v z)) * (1 / ((v : ℂ) * z + 1) ^ 2)) z :=
      ((QuantumZipper.FwdHolo.hasDerivAt_fwdMap hU hq hmz).add_const (U q : ℂ)).comp z (hasDerivAt_mob hden)
    have hd2 : HasDerivAt (fun z => nf α κN P (gmap w t z))
        ((κN : ℂ) / (gmap w t z - P) ^ 2 * Complex.exp (logDerivFwd w t z)) z :=
      (hasDerivAt_nf hζP0).comp z ((QuantumZipper.FwdHolo.hasDerivAt_fwdMap hw ht hz).add_const (w t : ℂ))
    have heq : (fun z => gmap U q (mob v z)) =ᶠ[𝓝 z] fun z => nf α κN P (gmap w t z) := by
      filter_upwards [hSo.mem_nhds hz] with y hy using hconj y hy
    have hid := (hd1.congr_of_eventuallyEq heq.symm).unique hd2
    have hmob : mob v z = z / ((v : ℂ) * z + 1) := mob_apply v z
    have hE1 : Complex.exp (-2 * Complex.log (-(mob v z)⁻¹)) = ((mob v z) ^ 2) := by
      rw [show (-2 : ℂ) * Complex.log (-(mob v z)⁻¹) = -(2 * Complex.log (-(mob v z)⁻¹)) by ring, Complex.exp_neg,
        exp_two_mul_log (neg_ne_zero.2 (inv_ne_zero hmob0))]
      field_simp
    have hE2 : Complex.exp (-2 * Complex.log (-z⁻¹)) = z ^ 2 := by
      rw [show (-2 : ℂ) * Complex.log (-z⁻¹) = -(2 * Complex.log (-z⁻¹)) by ring, Complex.exp_neg,
        exp_two_mul_log (neg_ne_zero.2 (inv_ne_zero hz0))]
      field_simp
    have hE3 := exp_two_mul_log hζP0
    simp only [hΛ]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_sub, Complex.exp_sub, hE1, hE2, hE3]
    have hL0 : Complex.exp (logDerivFwd w t z) ≠ 0 := Complex.exp_ne_zero _
    have hL : Complex.exp (logDerivFwd U q (mob v z)) =
        (κN : ℂ) / (gmap w t z - P) ^ 2 * Complex.exp (logDerivFwd w t z) * ((v : ℂ) * z + 1) ^ 2 := by
      rw [← hid]
      field_simp
    have hrat : (mob v z) ^ 2 / z ^ 2 = 1 / ((v : ℂ) * z + 1) ^ 2 := by
      rw [hmob]
      field_simp
    rw [hL, hrat]
    field_simp
  -- `Λ` is continuous on `S`
  have hslit : ∀ {y : ℂ}, y ∈ H → y ∈ Complex.slitPlane := fun hy => Or.inr (ne_of_gt hy)
  have hΛc : ContinuousOn Λ S := by
    intro z hz
    have hzH : z ∈ H := hz.1
    have hz0 := ne_zero_of_mem_H' hzH
    have hmz := mob_mem_compl hK hz
    have hden := mob_den_ne_zero (v := v) hzH
    have hmob0 : mob v z ≠ 0 := ne_zero_of_mem_H' (mob_mem_H v hzH)
    have hζ := gmap_mem_H hw ht hz
    have hmc : ContinuousAt (mob v) z := (hasDerivAt_mob hden).continuousAt
    have h1 : ContinuousAt (fun z => logDerivFwd U q (mob v z)) z :=
      (continuousAt_logDerivFwd hU hq hmz).comp hmc
    have h2 : ContinuousAt (logDerivFwd w t) z := continuousAt_logDerivFwd hw ht hz
    have h3 : ContinuousAt (fun z => Complex.log (-(mob v z)⁻¹)) z :=
      (hmc.inv₀ hmob0).neg.clog (hslit (Chart.isConformal_infinitySourceChart.2.1 (mob_mem_H v hzH)))
    have h4 : ContinuousAt (fun z : ℂ => Complex.log (-z⁻¹)) z :=
      (continuousAt_id.inv₀ hz0).neg.clog (hslit (Chart.isConformal_infinitySourceChart.2.1 hzH))
    have hg : ContinuousAt (gmap w t) z :=
      (QuantumZipper.FwdHolo.hasDerivAt_fwdMap hw ht hz).continuousAt.add continuousAt_const
    have h5 : ContinuousAt (fun z => Complex.log (gmap w t z - P)) z :=
      (hg.sub continuousAt_const).clog (hslit (sub_ofReal_mem_H hζ P))
    exact ((((h1.sub h2).add ((continuousAt_const.mul h3).sub (continuousAt_const.mul h4))).add
      (continuousAt_const.mul h5))).continuousWithinAt
  -- constancy of the imaginary part
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · exact ⟨0, fun z hz => by
      have : z ∈ S := hz
      rw [hSe] at this
      exact this.elim⟩
  refine ⟨(Λ z₀).im, fun z hz => ?_⟩
  rw [← hΛim z]
  have hn : ∀ y ∈ S, ∃ n : ℤ, Λ y = Λ z₀ + n * (2 * Real.pi * Complex.I) := fun y hy =>
    Complex.exp_eq_exp_iff_exists_int.1 ((hexp y hy).trans (hexp z₀ hz₀).symm)
  set f : ℂ → ℝ := fun y => (Λ y - Λ z₀).im / (2 * Real.pi) with hf_def
  have hfn : ∀ y ∈ S, ∀ n : ℤ, Λ y = Λ z₀ + n * (2 * Real.pi * Complex.I) → f y = n := by
    intro y _ n hyn
    simp only [hf_def, hyn, add_sub_cancel_left, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]
    field_simp
    ring
  have hfc : ContinuousOn f S :=
    (Complex.continuous_im.comp_continuousOn (hΛc.sub continuousOn_const)).div_const _
  have hmaps : MapsTo f S (range ((↑) : ℤ → ℝ)) := by
    intro y hy
    obtain ⟨n, hyn⟩ := hn y hy
    exact ⟨n, (hfn y hy n hyn).symm⟩
  have hdisc : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
  have hconst := hSc.constant_of_mapsTo hdisc hfc hmaps hz hz₀
  have hf0 : f z₀ = 0 := by simp only [hf_def, sub_self, Complex.zero_im, zero_div]
  obtain ⟨n, hzn⟩ := hn z hz
  have hfz : f z = 0 := hconst.trans hf0
  rw [hfn z hz n hzn] at hfz
  have hn0 : n = 0 := by exact_mod_cast hfz
  rw [hzn, hn0]
  simp

end ChainRule

/-! ### Uniqueness: the mean difference is constant when its boundary data is -/

section Unique

variable {w U : ℝ → ℝ} {t q : ℝ} {v α κN P : ℝ}

/-- A real Möbius map `α − κ/(ζ − P)` with `κ > 0` maps `ℍ` into `ℍ`. -/
theorem nf_mem_H (hκN : 0 < κN) {ζ : ℂ} (hζ : ζ ∈ H) : nf α κN P ζ ∈ H := by
  have hd : ζ - P ∈ H := sub_ofReal_mem_H hζ P
  have hd0 : ζ - P ≠ 0 := ne_zero_of_mem_H' hd
  change 0 < ((α : ℂ) - (κN : ℂ) / (ζ - P)).im
  rw [Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.div_im, Complex.ofReal_im, Complex.ofReal_re,
    zero_mul, zero_div, zero_sub, neg_neg]
  have hns : 0 < Complex.normSq (ζ - P) := Complex.normSq_pos.2 hd0
  have him : 0 < (ζ - P).im := hd
  positivity

theorem sub_real_mem_H {ζ : ℂ} (hζ : ζ ∈ H) (a : ℝ) : ζ - a ∈ H := sub_ofReal_mem_H hζ a

/-- `ζ ↦ arg (ζ − P)` is harmonic on `ℍ`. -/
theorem harmonicOnNhd_arg_sub (P : ℝ) : InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => Complex.arg (ζ - P)) H := by
  intro ζ hζ
  have hslit : ζ - P ∈ Complex.slitPlane := Or.inr (ne_of_gt (sub_ofReal_mem_H hζ P))
  have hA : AnalyticAt ℂ (fun ζ : ℂ => Complex.log (ζ - P)) ζ :=
    (analyticAt_id.sub analyticAt_const).clog hslit
  have := hA.harmonicAt_im
  simpa only [Complex.log_im] using this

/-- The boundary limit of `arg (ζ − P)` at a real point `x ≠ P`: `0` right of `P`, `π` left of it. -/
theorem tendsto_arg_sub {x : ℝ} (hx : x ≠ P) :
    Tendsto (fun ζ : ℂ => Complex.arg (ζ - P)) (𝓝[H] (x : ℂ)) (𝓝 (if x < P then Real.pi else 0)) := by
  have hcont : Tendsto (fun ζ : ℂ => ζ - P) (𝓝[H] (x : ℂ)) (𝓝[{z : ℂ | 0 ≤ z.im}] ((x : ℂ) - P)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ζ hζ
      exact (sub_ofReal_mem_H hζ P).le
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · simp only [hlt, ↓reduceIte]
    have hre : ((x : ℂ) - P).re < 0 := by simp [hlt]
    have him : ((x : ℂ) - P).im = 0 := by simp
    exact (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero hre him).comp hcont
  · simp only [not_lt.2 hgt.le, ↓reduceIte]
    have hpos : (0 : ℝ) < x - P := sub_pos.2 hgt
    have hslit : ((x : ℂ) - P) ∈ Complex.slitPlane := by
      left
      simp [hpos]
    have h0 : Complex.arg ((x : ℂ) - P) = 0 := by
      rw [show ((x : ℂ) - P) = ((x - P : ℝ) : ℂ) by push_cast; ring]
      exact Complex.arg_ofReal_of_nonneg hpos.le
    rw [← h0]
    exact ((Complex.continuousAt_arg hslit).tendsto.comp
      (((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds))

/-- The real Möbius map on the real line (Lean's `x / 0 = 0` at the pole) is injective. -/
theorem injective_nfR (hκN : 0 < κN) (a : ℝ) : Function.Injective fun x : ℝ => α - κN / (x - P) - a := by
  intro x x' hxx'
  simp only [sub_left_inj, sub_right_inj] at hxx'
  by_cases hx : x - P = 0
  · by_cases hx' : x' - P = 0
    · linarith
    · rw [hx, div_zero] at hxx'
      exact absurd hxx'.symm (div_ne_zero hκN.ne' hx')
  · by_cases hx' : x' - P = 0
    · rw [hx', div_zero] at hxx'
      exact absurd hxx' (div_ne_zero hκN.ne' hx)
    · have := (div_eq_div_iff hx hx').1 hxx'
      have h2 : κN * (x' - P) = κN * (x - P) := by linarith
      have h3 := mul_left_cancel₀ hκN.ne' h2
      linarith

/-- **The mean difference through the conjugation is constant when its boundary data is.** With the conjugation
`g̃_q ∘ mob v = nf α κN P ∘ g_t` and bounded harmonic extensions `u`, `ũ` of finite step data `β`, `β̃`: if, off a
finite set of real points `x`, `β̃(N x − U_q) − β(x − w_t) + χ · 2 arg(x − P)` is a constant `d` (`arg` of a real
number read from `ℍ`: `π` left of `P`, `0` right of it), then `𝔥̃_q ∘ mob v − 𝔥_t − χ · lift` is constant on `ℍ ∖ K_t`
(`𝔥 = couplingMean`). Proof: by the chain-rule lift the difference is `Δ(g_t z)` with
`Δ(ζ) = ũ(N ζ − U_q) − u(ζ − w_t) + 2χ arg(ζ − P) + const`, a bounded harmonic function on `ℍ` with constant boundary
values off a finite set, hence constant (`PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension`). -/
theorem exists_const_couplingMean_mob (hw : Continuous w) (hw0 : w 0 = 0) (hU : Continuous U) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hκN : 0 < κN) (hK : mob v '' fwdHull w t = fwdHull U q)
    (hconj : ∀ z ∈ H \ fwdHull w t, gmap U q (mob v z) = nf α κN P (gmap w t z)) {κ : ℝ} {β β' : ℝ → ℝ}
    {S S' : Set ℝ} (hS : S.Finite) (hS' : S'.Finite) {u u' : ℂ → ℝ} (hu : IsBoundedHarmonicExtension β S u)
    (hu' : IsBoundedHarmonicExtension β' S' u') {E : Set ℝ} (hE : E.Finite) (d : ℝ)
    (hbd : ∀ x : ℝ, x ∉ E → x ≠ P → α - κN / (x - P) - U q ∉ S' → x - w t ∉ S →
      β' (α - κN / (x - P) - U q) - β (x - w t) + QuantumZipper.chiC κ * (2 * (if x < P then Real.pi else 0)) = d) :
    ∃ C : ℝ, ∀ z ∈ H \ fwdHull w t,
      couplingMean κ (fun s => U s) q u' (mob v z) - couplingMean κ (fun s => w s) t u z -
        QuantumZipper.chiC κ * (brChart v).2.2 z = C := by
  obtain ⟨c, hc⟩ := exists_const_im_logDeriv hw hw0 hU ht hq hK hconj
  set χ := QuantumZipper.chiC κ with hχ
  set Δ : ℂ → ℝ := fun ζ => u' (nf α κN P ζ - U q) - u (ζ - w t) + χ * (2 * Complex.arg (ζ - P)) - d with hΔ
  set Bad : Set ℝ := E ∪ {P} ∪ ((fun x : ℝ => α - κN / (x - P) - U q) ⁻¹' S') ∪ ((fun x : ℝ => x - w t) ⁻¹' S)
    with hBad
  have hBadf : Bad.Finite := by
    refine ((hE.union (Set.finite_singleton P)).union (hS'.preimage (injective_nfR hκN _).injOn)).union
      (hS.preimage (sub_left_injective).injOn)
  -- `Δ` is a bounded harmonic extension of `0`
  have hmapN : MapsTo (fun ζ : ℂ => nf α κN P ζ - U q) H H := fun ζ hζ => sub_ofReal_mem_H (nf_mem_H hκN hζ) _
  have hmapT : MapsTo (fun ζ : ℂ => ζ - w t) H H := fun ζ hζ => sub_ofReal_mem_H hζ _
  have hdN : DifferentiableOn ℂ (fun ζ : ℂ => nf α κN P ζ - U q) H := fun ζ hζ =>
    ((hasDerivAt_nf (α := α) (κN := κN) (ne_zero_of_mem_H' (sub_ofReal_mem_H hζ P))).differentiableAt.sub
      (differentiableAt_const _)).differentiableWithinAt
  have hdT : DifferentiableOn ℂ (fun ζ : ℂ => ζ - w t) H := fun ζ _ =>
    (differentiableAt_id.sub (differentiableAt_const _)).differentiableWithinAt
  have hH1 := LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H hu'.1 hdN hmapN
  have hH2 := LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H hu.1 hdT hmapT
  have hharm : InnerProductSpace.HarmonicOnNhd Δ H := by
    have h3 := (harmonicOnNhd_arg_sub P).const_smul (c := (2 * χ : ℝ))
    intro ζ hζ
    have := ((hH1 ζ hζ).sub (hH2 ζ hζ)).add (h3 ζ hζ)
    have h4 := this.sub (InnerProductSpace.harmonicAt_const (d : ℝ))
    refine (InnerProductSpace.harmonicAt_congr_nhds (Eventually.of_forall fun y => ?_)).1 h4
    simp only [hΔ, Function.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨C₁, hC₁⟩ := hu'.2.1
  obtain ⟨C₂, hC₂⟩ := hu.2.1
  have hbdd : ∃ M : ℝ, ∀ ζ ∈ H, |Δ ζ| ≤ M := by
    refine ⟨C₁ + C₂ + |χ| * (2 * Real.pi) + |d|, fun ζ hζ => ?_⟩
    have h1 := hC₁ _ (hmapN hζ)
    have h2 := hC₂ _ (hmapT hζ)
    have h3 : |χ * (2 * Complex.arg (ζ - P))| ≤ |χ| * (2 * Real.pi) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_mul, abs_two]
      have := Complex.abs_arg_le_pi (ζ - P)
      linarith
    simp only [hΔ]
    calc |u' (nf α κN P ζ - ↑(U q)) - u (ζ - ↑(w t)) + χ * (2 * Complex.arg (ζ - ↑P)) - d|
        ≤ |u' (nf α κN P ζ - ↑(U q))| + |u (ζ - ↑(w t))| + |χ * (2 * Complex.arg (ζ - ↑P))| + |d| := by
          have := abs_sub (u' (nf α κN P ζ - ↑(U q)) - u (ζ - ↑(w t)) + χ * (2 * Complex.arg (ζ - ↑P))) d
          have := abs_add_le (u' (nf α κN P ζ - ↑(U q)) - u (ζ - ↑(w t))) (χ * (2 * Complex.arg (ζ - ↑P)))
          have := abs_sub (u' (nf α κN P ζ - ↑(U q))) (u (ζ - ↑(w t)))
          linarith
      _ ≤ C₁ + C₂ + |χ| * (2 * Real.pi) + |d| := by linarith
  -- boundary limits
  have hlim : ∀ x : ℝ, x ∉ Bad → Tendsto Δ (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x hx
    simp only [hBad, mem_union, mem_singleton_iff, mem_preimage, not_or] at hx
    obtain ⟨⟨⟨hxE, hxP⟩, hxS'⟩, hxS⟩ := hx
    have hxP' : (x : ℂ) - P ≠ 0 := by
      intro h0
      apply hxP
      have := congrArg Complex.re h0
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at this
      linarith
    have hnfx : nf α κN P (x : ℂ) - U q = ((α - κN / (x - P) - U q : ℝ) : ℂ) := by
      simp only [nf]
      push_cast
      ring
    have hT1 : Tendsto (fun ζ : ℂ => nf α κN P ζ - U q) (𝓝[H] (x : ℂ))
        (𝓝[H] ((α - κN / (x - P) - U q : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · rw [← hnfx]
        exact ((hasDerivAt_nf (α := α) (κN := κN) hxP').continuousAt.sub continuousAt_const).tendsto.mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ζ hζ using hmapN hζ
    have hT2 : Tendsto (fun ζ : ℂ => ζ - w t) (𝓝[H] (x : ℂ)) (𝓝[H] ((x - w t : ℝ) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ((x - w t : ℝ) : ℂ) = (x : ℂ) - w t := by push_cast; ring
        rw [this]
        exact ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ζ hζ using hmapT hζ
    have h1 := (hu'.2.2 _ hxS').comp hT1
    have h2 := (hu.2.2 _ hxS).comp hT2
    have h3 := tendsto_arg_sub (P := P) hxP
    have h4 := ((h1.sub h2).add ((h3.const_mul (2 : ℝ)).const_mul χ)).sub_const d
    have hval := hbd x hxE hxP hxS' hxS
    rw [hval, sub_self] at h4
    exact h4
  have hΔ0 : IsBoundedHarmonicExtension (fun _ => (0 : ℝ)) Bad Δ := ⟨hharm, hbdd, hlim⟩
  have hzero : IsBoundedHarmonicExtension (fun _ => (0 : ℝ)) Bad (fun _ => (0 : ℝ)) :=
    ⟨fun _ _ => InnerProductSpace.harmonicAt_const _, ⟨0, fun _ _ => by simp⟩, fun _ _ => tendsto_const_nhds⟩
  have heq := PiecewiseConstant.eqOn_of_isBoundedHarmonicExtension hBadf hzero hΔ0
  refine ⟨d - χ * c, fun z hz => ?_⟩
  have hζ := gmap_mem_H hw ht hz
  have hΔz : Δ (gmap w t z) = 0 := heq hζ
  have hcz := hc z hz
  have e1 : fwdMap U q (mob v z) = nf α κN P (gmap w t z) - U q := by
    rw [← hconj z hz]
    simp only [gmap]
    ring
  have e2 : fwdMap w t z = gmap w t z - w t := by
    simp only [gmap]
    ring
  simp only [hΔ] at hΔz
  simp only [couplingMean]
  rw [e1, e2]
  rw [← hχ]
  linear_combination hΔz - χ * hcz

/-- **The mean identity through the conjugation** (deterministic). Under the hypotheses of
`exists_const_couplingMean_mob`, if moreover the difference `𝔥̃_q ∘ mob v − 𝔥_t − χ · lift` tends to `0` at one point
of the closure of `ℍ ∖ K_t` (in practice an untouched real point on the tip side), then
`𝔥̃_q (mob v z) = 𝔥_t z + χ · lift z` on `ℍ ∖ K_t`. -/
theorem couplingMean_mob_eq (hw : Continuous w) (hw0 : w 0 = 0) (hU : Continuous U) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hκN : 0 < κN) (hK : mob v '' fwdHull w t = fwdHull U q)
    (hconj : ∀ z ∈ H \ fwdHull w t, gmap U q (mob v z) = nf α κN P (gmap w t z)) {κ : ℝ} {β β' : ℝ → ℝ}
    {S S' : Set ℝ} (hS : S.Finite) (hS' : S'.Finite) {u u' : ℂ → ℝ} (hu : IsBoundedHarmonicExtension β S u)
    (hu' : IsBoundedHarmonicExtension β' S' u') {E : Set ℝ} (hE : E.Finite) (d : ℝ)
    (hbd : ∀ x : ℝ, x ∉ E → x ≠ P → α - κN / (x - P) - U q ∉ S' → x - w t ∉ S →
      β' (α - κN / (x - P) - U q) - β (x - w t) + QuantumZipper.chiC κ * (2 * (if x < P then Real.pi else 0)) = d)
    {y₀ : ℂ} (hy₀ : (𝓝[H \ fwdHull w t] y₀).NeBot)
    (hlim : Tendsto (fun z => couplingMean κ (fun s => U s) q u' (mob v z) - couplingMean κ (fun s => w s) t u z -
      QuantumZipper.chiC κ * (brChart v).2.2 z) (𝓝[H \ fwdHull w t] y₀) (𝓝 0)) :
    ∀ z ∈ H \ fwdHull w t,
      couplingMean κ (fun s => U s) q u' (mob v z) =
        couplingMean κ (fun s => w s) t u z + QuantumZipper.chiC κ * (brChart v).2.2 z := by
  obtain ⟨C, hC⟩ := exists_const_couplingMean_mob hw hw0 hU ht hq hκN hK hconj hS hS' hu hu' hE d hbd
  have hconst : Tendsto (fun z => couplingMean κ (fun s => U s) q u' (mob v z) - couplingMean κ (fun s => w s) t u z -
      QuantumZipper.chiC κ * (brChart v).2.2 z) (𝓝[H \ fwdHull w t] y₀) (𝓝 C) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z hz => (hC z hz).symm)
  have hC0 : C = 0 := tendsto_nhds_unique hconst hlim
  intro z hz
  have := hC z hz
  rw [hC0] at this
  linarith

end Unique

end InteractingSLE.Supp8.HullDetGen
