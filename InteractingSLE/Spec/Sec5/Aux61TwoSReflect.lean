/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Analysis.SchwarzHarmonic
import InteractingSLE.Spec.Supplement.R6RefPhase
import InteractingSLE.Spec.Sec7.Aux119Reflect

/-!
# Aux. 61, the two new sides: Schwarz reflection from vanishing imaginary boundary values

Packet PROVE-AUX61-TWOSIDES (Theorem 1.2's Prop 5.1 (E1); Astra's follow-up 4 §1.1, L113–L123: "The chain rule,
with the branch fixed at the initial seed, gives the same phase on the connected new slit"). The transition maps
between the restart chart and the physical flow chart are only known to send the relevant real boundary arcs to
the real line in the weak sense `Im → 0`. This file turns that into a holomorphic reflection with a positive
real boundary derivative, and records the consequences used by the slit-side calculation.

* `exists_real_eqOn_of_im_eq_zero` : a holomorphic function with zero imaginary part on a preconnected open set
  is a real constant (open mapping theorem);
* **`exists_isPosReflect`** : if `Ξ` is holomorphic and injective on the upper half-ball `ℍ ∩ B(v, ε)`, maps it
  into `ℍ`, and `Im Ξ → 0` at every real point of the ball, then `Ξ` has a reflection `G` across the real
  diameter (holomorphic on the ball, commuting with conjugation, real-boundary-conformal); the proof is the
  harmonic odd reflection of `Im Ξ` (`SchwarzHarmonic.harmonicOnNhd_oddExtension`), a harmonic conjugate on the
  ball, and QuantumZipper's holomorphic reflection;
* `IsPosReflect.deriv_pos`, `IsPosReflect.tendsto`, `IsPosReflect.tendsto_deriv` : `Ξ → G(y) ∈ ℝ` and
  `Ξ′ → G′(y) > 0` at every real point `y` of the ball;
* **`IsPosReflect.exists_int_tendsto_im`** : a continuous logarithm of `Ξ′` has imaginary part tending to `2πn`;
* **`IsPosReflect.tendsto_leftInv`** : a left inverse `Θ` of `Ξ` on the half-ball tends to `v` at `G(v)` (from `ℍ`).

Deterministic; no source statement is replaced. R48/R77: nothing here uses Theorem 1.2/1.3 or the post-contact
kernel.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate Real
open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Sec5.Aux61TwoS

/-! ### Holomorphic functions with real values -/

/-- A holomorphic function with zero imaginary part on a nonempty preconnected open set is a real constant there. -/
theorem exists_real_eqOn_of_im_eq_zero {h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hh : DifferentiableOn ℂ h U) (him : ∀ z ∈ U, (h z).im = 0) :
    ∃ c : ℝ, ∀ z ∈ U, h z = c := by
  obtain ⟨z₀, hz₀⟩ := hUne
  rcases (hh.analyticOnNhd hU).is_constant_or_isOpen hUc with ⟨w, hw⟩ | hopen
  · refine ⟨w.re, fun z hz => ?_⟩
    have hwim : w.im = 0 := by rw [← hw z₀ hz₀]; exact him z₀ hz₀
    rw [hw z hz]
    exact Complex.ext (by simp) (by simp [hwim])
  · exfalso
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hopen U subset_rfl hU) (h z₀) ⟨z₀, hz₀, rfl⟩
    have hmem : h z₀ + ((ε / 2 : ℝ) : ℂ) * I ∈ ball (h z₀) ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    obtain ⟨z, hz, hzeq⟩ := hball hmem
    have h1 := him z hz
    rw [hzeq, add_im, him z₀ hz₀, zero_add, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, zero_mul,
      add_zero] at h1
    linarith

/-! ### The positive reflection -/

/-- `G` is a **positive real reflection** of `Ξ` across the real diameter of `B(v, r)`: holomorphic on the ball,
equal to `Ξ` on the upper half-ball, commuting with conjugation, and real-boundary-conformal (holomorphic and
injective on the upper half-ball with values in `ℍ`, real on the diameter). -/
structure IsPosReflect (Ξ G : ℂ → ℂ) (v r : ℝ) : Prop where
  pos : 0 < r
  diff : DifferentiableOn ℂ G (ball (v : ℂ) r)
  eqOn : EqOn G Ξ (H ∩ ball (v : ℂ) r)
  conj_eq : ∀ z ∈ ball (v : ℂ) r, G (conj z) = conj (G z)
  conf : R16.IsRealBoundaryConformal G v r

/-- **Schwarz reflection from vanishing imaginary boundary values.** If `Ξ` is holomorphic and injective on
`ℍ ∩ B(v, ε)`, maps it into `ℍ`, and `Im Ξ(y) → 0` as `y → x` from `ℍ` at every real point `x` of the ball, then `Ξ`
has a positive real reflection on `B(v, ε)`. -/
theorem exists_isPosReflect {Ξ : ℂ → ℂ} {v ε : ℝ} (hε : 0 < ε)
    (hd : DifferentiableOn ℂ Ξ (H ∩ ball (v : ℂ) ε)) (hmaps : MapsTo Ξ (H ∩ ball (v : ℂ) ε) H)
    (hinj : InjOn Ξ (H ∩ ball (v : ℂ) ε))
    (him : ∀ x : ℝ, (x : ℂ) ∈ ball (v : ℂ) ε → Tendsto (fun y => (Ξ y).im) (𝓝[H] (x : ℂ)) (𝓝 0)) :
    ∃ G, IsPosReflect Ξ G v ε := by
  set U := ball (v : ℂ) ε with hUdef
  set u : ℂ → ℝ := fun z => (Ξ z).im with hudef
  have hUo : IsOpen U := isOpen_ball
  have hconj : ∀ z ∈ U, conj z ∈ U := fun z hz => QuantumZipper.CA.conj_mem_ball_ofReal hz
  have hHU : IsOpen (H ∩ U) := QuantumZipper.isOpen_H.inter isOpen_ball
  have hu : InnerProductSpace.HarmonicOnNhd u (U ∩ H) := fun z hz =>
    (hd.analyticAt (hHU.mem_nhds ⟨hz.2, hz.1⟩)).harmonicAt_im
  have hv := Analysis.SchwarzHarmonic.harmonicOnNhd_oddExtension hUo hconj hu
    (fun x hx => (him x hx).mono_left (nhdsWithin_mono _ inter_subset_right))
  obtain ⟨F, hF, hFre⟩ := hv.exists_analyticOnNhd_ball_re_eq
  set G₀ : ℂ → ℂ := fun z => I * F z with hG₀def
  have hG₀im : ∀ z ∈ U, (G₀ z).im = Analysis.SchwarzHarmonic.oddExtension u z := fun z hz => by
    simp only [hG₀def, mul_im, I_re, zero_mul, I_im, one_mul, zero_add]
    exact hFre hz
  have hG₀d : DifferentiableOn ℂ G₀ U := (analyticOnNhd_const.mul hF).differentiableOn
  -- `G₀ − Ξ` is a real constant on the upper half-ball
  have hpre : IsPreconnected (H ∩ U) :=
    ((convex_halfSpace_im_gt (r := 0)).inter (convex_ball _ _)).isPreconnected
  have hne : (H ∩ U).Nonempty := by
    refine ⟨(v : ℂ) + ((ε / 2 : ℝ) : ℂ) * I, ?_, ?_⟩
    · show (0 : ℝ) < ((v : ℂ) + ((ε / 2 : ℝ) : ℂ) * I).im
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_one, mul_zero, zero_add]
      linarith
    · rw [hUdef, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
  obtain ⟨c, hc⟩ := exists_real_eqOn_of_im_eq_zero hHU hpre hne
    ((hG₀d.mono inter_subset_right).sub hd) fun z hz => by
      rw [Pi.sub_apply, sub_im, hG₀im z hz.2, Analysis.SchwarzHarmonic.oddExtension_of_pos hz.1]
      exact sub_self _
  set G₁ : ℂ → ℂ := fun z => G₀ z - c with hG₁def
  have hG₁d : DifferentiableOn ℂ G₁ U := hG₀d.sub_const _
  have hG₁Ξ : EqOn G₁ Ξ (H ∩ U) := fun z hz => by
    have := hc z hz
    rw [Pi.sub_apply] at this
    simp only [hG₁def]
    rw [← this]; ring
  have hG₁re : ∀ z ∈ U, z.im = 0 → (G₁ z).im = 0 := fun z hz hz0 => by
    simp only [hG₁def, sub_im, ofReal_im, sub_zero]
    rw [hG₀im z hz, Analysis.SchwarzHarmonic.oddExtension_of_im_eq_zero hz0]
  obtain ⟨G, hGd, hGeq, hGc⟩ := QuantumZipper.CA.exists_reflection_extension (hG₁d.mono inter_subset_right)
    (hG₁d.continuousOn.mono inter_subset_right) hG₁re
  have hGΞ : EqOn G Ξ (H ∩ U) := fun z hz =>
    (hGeq ⟨show (0 : ℝ) ≤ z.im from hz.1.le, hz.2⟩).trans (hG₁Ξ hz)
  refine ⟨G, ⟨hε, hGd, hGΞ, hGc, ?_⟩⟩
  refine ⟨hGd.mono inter_subset_right, hGd.continuousOn.mono inter_subset_right, fun z hz hz0 => ?_,
    fun z hz => ?_, fun z hz w hw hzw => hinj hz hw ?_⟩
  · rw [hGeq ⟨show (0 : ℝ) ≤ z.im from hz0.ge, hz⟩]; exact hG₁re z hz hz0
  · rw [hGΞ hz]; exact hmaps hz
  · rwa [← hGΞ hz, ← hGΞ hw]

variable {Ξ G : ℂ → ℂ} {v r : ℝ}

/-- The Schwarz reflection of `G` is `G` itself on the ball. -/
theorem IsPosReflect.schwarzReflect_eqOn (h : IsPosReflect Ξ G v r) :
    EqOn (schwarzReflect G) G (ball (v : ℂ) r) := by
  intro z hz
  by_cases hz0 : 0 ≤ z.im
  · simp only [schwarzReflect, hz0, ↓reduceIte]
  · simp only [schwarzReflect, hz0, ↓reduceIte]
    rw [h.conj_eq z hz, conj_conj]

/-- `G` is real on the real diameter. -/
theorem IsPosReflect.im_eq_zero (h : IsPosReflect Ξ G v r) {y : ℝ} (hy : (y : ℂ) ∈ ball (v : ℂ) r) :
    (G y).im = 0 :=
  h.conf.2.2.1 y hy (by simp)

/-- **The boundary derivative is a positive real** at every real point of the ball. -/
theorem IsPosReflect.deriv_pos (h : IsPosReflect Ξ G v r) {y : ℝ} (hy : (y : ℂ) ∈ ball (v : ℂ) r) :
    (deriv G y).im = 0 ∧ 0 < (deriv G y).re := by
  have he : deriv (schwarzReflect G) y = deriv G y :=
    Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hy) h.schwarzReflect_eqOn)
  rw [← he]
  exact h.conf.deriv_schwarzReflect_pos hy

/-- `Ξ → G(y)` at a real point `y` of the ball, from `ℍ`. -/
theorem IsPosReflect.tendsto (h : IsPosReflect Ξ G v r) {y : ℝ} (hy : (y : ℂ) ∈ ball (v : ℂ) r) :
    Tendsto Ξ (𝓝[H] (y : ℂ)) (𝓝 (G y)) := by
  have hc : ContinuousAt G y := (h.diff.differentiableAt (isOpen_ball.mem_nhds hy)).continuousAt
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hy)] with z hz
  exact h.eqOn hz

/-- `Ξ → G(y)` within `ℍ`'s closure: the limit is a real point and `Ξ` stays in `ℍ`. -/
theorem IsPosReflect.tendsto_nhdsWithin (h : IsPosReflect Ξ G v r) {y : ℝ} (hy : (y : ℂ) ∈ ball (v : ℂ) r) :
    Tendsto Ξ (𝓝[H] (y : ℂ)) (𝓝[H] (G y)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨h.tendsto hy, ?_⟩
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hy)] with z hz
  rw [← h.eqOn hz]
  exact h.conf.2.2.2.1 hz

/-- `Ξ′ → G′(y)` at a real point `y` of the ball, from `ℍ`. -/
theorem IsPosReflect.tendsto_deriv (h : IsPosReflect Ξ G v r) {y : ℝ} (hy : (y : ℂ) ∈ ball (v : ℂ) r) :
    Tendsto (deriv Ξ) (𝓝[H] (y : ℂ)) (𝓝 (deriv G y)) := by
  have hc : ContinuousAt (deriv G) y :=
    ((h.diff.deriv isOpen_ball).differentiableAt (isOpen_ball.mem_nhds hy)).continuousAt
  refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hHo : IsOpen (H ∩ ball (v : ℂ) r) := QuantumZipper.isOpen_H.inter isOpen_ball
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hy)] with z hz
  exact Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hHo.mem_nhds hz) h.eqOn)

/-- **The integer branch.** A continuous logarithm `L` of `Ξ′` on the upper half-ball has `Im L → 2πn` at the
centre, for one integer `n`. -/
theorem IsPosReflect.exists_int_tendsto_im (h : IsPosReflect Ξ G v r) {L : ℂ → ℂ}
    (hLc : ContinuousOn L (H ∩ ball (v : ℂ) r)) (hLe : ∀ z ∈ H ∩ ball (v : ℂ) r, exp (L z) = deriv Ξ z) :
    ∃ n : ℤ, Tendsto (fun z => (L z).im) (𝓝[H] (v : ℂ)) (𝓝 (2 * π * n)) := by
  have hvB : ((v : ℝ) : ℂ) ∈ ball (v : ℂ) r := mem_ball_self h.pos
  obtain ⟨him, hre⟩ := h.deriv_pos hvB
  set c : ℝ := (deriv G v).re with hcdef
  have hcG : deriv G v = (c : ℂ) := Complex.ext (by simp [hcdef]) (by simp [him])
  have hHo : IsOpen (H ∩ ball (v : ℂ) r) := QuantumZipper.isOpen_H.inter isOpen_ball
  have hdeq : EqOn (deriv Ξ) (deriv G) (H ∩ ball (v : ℂ) r) := fun z hz =>
    (Filter.EventuallyEq.deriv_eq (Filter.eventuallyEq_of_mem (hHo.mem_nhds hz) h.eqOn)).symm
  have hdGc : ContinuousOn (deriv G) (ball (v : ℂ) r) := (h.diff.deriv isOpen_ball).continuousOn
  -- a ball on which `G′` stays in the right half-plane
  have hev : ∀ᶠ z in 𝓝 (v : ℂ), 0 < (deriv G z).re := by
    have hcont : ContinuousAt (deriv G) v := hdGc.continuousAt (isOpen_ball.mem_nhds hvB)
    exact hcont.eventually ((isOpen_lt continuous_const continuous_re).mem_nhds hre)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.1 hev
  set S := H ∩ ball (v : ℂ) (min δ r) with hSdef
  have hSsub : S ⊆ H ∩ ball (v : ℂ) r := fun z hz => ⟨hz.1, ball_subset_ball (min_le_right _ _) hz.2⟩
  have hSc : IsPreconnected S :=
    ((convex_halfSpace_im_gt (r := 0)).inter (convex_ball _ _)).isPreconnected
  have hslit : ∀ z ∈ S, deriv Ξ z ∈ slitPlane := fun z hz => by
    rw [hdeq (hSsub hz)]
    exact Or.inl (hδs (ball_subset_ball (min_le_left _ _) hz.2))
  have hGcS : ContinuousOn (deriv Ξ) S :=
    (hdGc.mono fun z hz => (hSsub hz).2).congr fun z hz => hdeq (hSsub hz)
  have hSnhds : 𝓝[S] (v : ℂ) = 𝓝[H] (v : ℂ) := by
    rw [hSdef, nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (lt_min hδ h.pos)))]
  have hlim : Tendsto (deriv Ξ) (𝓝[S] (v : ℂ)) (𝓝 (c : ℂ)) := by
    rw [hSnhds, ← hcG]; exact h.tendsto_deriv hvB
  obtain ⟨n, hn⟩ := Sec7.Aux119.exists_int_tendsto_im_sub (L₁ := fun _ => 0) (L₂ := L) hSc continuousOn_const
    (hLc.mono hSsub) hGcS hslit (fun z hz => by rw [sub_zero]; exact hLe z (hSsub hz))
    (F := 𝓝[S] (v : ℂ)) inf_le_right hre hlim
  refine ⟨n, ?_⟩
  rw [hSnhds] at hn
  simpa only [sub_zero] using hn

/-- **The left inverse of a reflected map.** If `Θ ∘ Ξ = id` on the upper half-ball, then `Θ(y) → v` (inside `ℍ`)
as `y → G(v)` from `ℍ`: near `G(v)` the map `Θ` is the local inverse of `G`. -/
theorem IsPosReflect.tendsto_leftInv (h : IsPosReflect Ξ G v r) {Θ : ℂ → ℂ}
    (hΘ : ∀ w ∈ H ∩ ball (v : ℂ) r, Θ (Ξ w) = w) :
    Tendsto Θ (𝓝[H] (G v)) (𝓝[H] (v : ℂ)) := by
  have hvB : ((v : ℝ) : ℂ) ∈ ball (v : ℂ) r := mem_ball_self h.pos
  have hd0 : deriv G v ≠ 0 := fun h0 => by
    have := (h.deriv_pos hvB).2; rw [h0, zero_re] at this; exact lt_irrefl _ this
  have hs' : HasStrictDerivAt G (deriv G v) v :=
    (h.diff.analyticAt (isOpen_ball.mem_nhds hvB)).hasStrictDerivAt
  set g := hs'.localInverse G (deriv G v) v hd0 with hgdef
  have hg1 : g (G v) = v := (hs'.eventually_left_inverse hd0).self_of_nhds
  have hgc : ContinuousAt g (G v) := (hs'.to_localInverse hd0).hasDerivAt.continuousAt
  have hgB : ∀ᶠ y in 𝓝 (G v), g y ∈ ball (v : ℂ) r := by
    have := hgc.tendsto
    rw [hg1] at this
    exact this (isOpen_ball.mem_nhds hvB)
  have hright := hs'.eventually_right_inverse hd0
  have heq : ∀ᶠ y in 𝓝[H] (G v), g y ∈ H ∧ Θ y = g y := by
    filter_upwards [nhdsWithin_le_nhds (hgB.and hright), self_mem_nhdsWithin] with y ⟨hyB, hyr⟩ hyH
    have hyH' : (0 : ℝ) < y.im := hyH
    have hgH : g y ∈ H := by
      by_contra hn
      have hle : (g y).im ≤ 0 := not_lt.1 hn
      rcases hle.lt_or_eq with hlt | h0
      · have hcB : conj (g y) ∈ ball (v : ℂ) r := QuantumZipper.CA.conj_mem_ball_ofReal hyB
        have hcH : conj (g y) ∈ H := show (0 : ℝ) < (conj (g y)).im by rw [conj_im]; linarith
        have h1 := h.conj_eq _ hcB
        rw [conj_conj] at h1
        have h2 : 0 < (G (conj (g y))).im := h.conf.2.2.2.1 ⟨hcH, hcB⟩
        have h3 : (G (g y)).im < 0 := by rw [h1, conj_im]; linarith
        rw [hyr] at h3
        linarith
      · have h3 := h.conf.2.2.1 (g y) hyB h0
        rw [hyr] at h3
        linarith
    refine ⟨hgH, ?_⟩
    have e1 : Ξ (g y) = y := by rw [← h.eqOn ⟨hgH, hyB⟩]; exact hyr
    calc Θ y = Θ (Ξ (g y)) := by rw [e1]
      _ = g y := hΘ _ ⟨hgH, hyB⟩
  have h1 : Tendsto g (𝓝[H] (G v)) (𝓝 (v : ℂ)) := by
    have := hgc.tendsto.mono_left (nhdsWithin_le_nhds (s := H))
    rwa [hg1] at this
  refine tendsto_nhdsWithin_iff.2 ⟨h1.congr' (heq.mono fun y hy => hy.2.symm), heq.mono fun y hy => ?_⟩
  rw [hy.2]; exact hy.1

/-- A positive reflection restricts to every smaller ball about a real point of the ball. -/
theorem IsPosReflect.of_subset (h : IsPosReflect Ξ G v r) {y r' : ℝ} (hr' : 0 < r')
    (hsub : ball (y : ℂ) r' ⊆ ball (v : ℂ) r) : IsPosReflect Ξ G y r' where
  pos := hr'
  diff := h.diff.mono hsub
  eqOn := fun z hz => h.eqOn ⟨hz.1, hsub hz.2⟩
  conj_eq := fun z hz => h.conj_eq z (hsub hz)
  conf := by
    have hs : H ∩ ball (y : ℂ) r' ⊆ H ∩ ball (v : ℂ) r := inter_subset_inter_right H hsub
    have hs' : Hbar ∩ ball (y : ℂ) r' ⊆ Hbar ∩ ball (v : ℂ) r := inter_subset_inter_right Hbar hsub
    exact ⟨h.conf.1.mono hs, h.conf.2.1.mono hs', fun z hz hz0 => h.conf.2.2.1 z (hsub hz) hz0,
      h.conf.2.2.2.1.mono hs subset_rfl, h.conf.2.2.2.2.mono hs⟩

/-- A ball about a real point of a ball about a real point, inside it. -/
theorem exists_ball_subset_ball {v r y : ℝ} (hy : (y : ℂ) ∈ ball (v : ℂ) r) :
    ∃ r' > 0, ball (y : ℂ) r' ⊆ ball (v : ℂ) r := by
  obtain ⟨r', hr', hsub⟩ := Metric.isOpen_iff.1 isOpen_ball (y : ℂ) hy
  exact ⟨r', hr', hsub⟩

end InteractingSLE.Sec5.Aux61TwoS
