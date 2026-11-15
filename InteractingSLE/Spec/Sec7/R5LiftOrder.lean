/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftReflect

/-!
# Lemma R.5's common phase: the reflected derivative does not vanish

Packet PROVE-R5-LIFT (round 3). `R5LiftReflect` derived the positive reflected derivative from boundary data that
include injectivity on the CLOSED half-disc (to get `G′(x) ≠ 0`). On the real diameter that injectivity is a prime-end
statement. Here it is removed:

* **`deriv_ne_zero_of_real_of_im_pos`**: a holomorphic `G` on a disc about a real `x`, real on the real diameter,
  with `Im G > 0` on the upper half-disc and not locally constant at `x`, has `G′(x) ≠ 0` (order of vanishing: if
  `G − G(x) = (z − x)ⁿ h` with `n ≥ 2` and `h(x)` real nonzero, the ray `x + t e^{iθ}` with `nθ = 3π/2` or `π/2`
  has `Im G < 0`);
* **`exists_pos_tendsto_deriv_of_reflect'`**, **`…_eqOn'`**: the positive reflected derivative from boundary data
  with injectivity only on the OPEN half-disc (automatic for a composition of conformal maps).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar isOpen_H)
open scoped ComplexConjugate

namespace InteractingSLE.Sec7.R5Lift

/-- **The reflected derivative does not vanish** (order of vanishing). -/
theorem deriv_ne_zero_of_real_of_im_pos {G : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hG : DifferentiableOn ℂ G (ball (x : ℂ) r)) (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (G z).im = 0)
    (hpos : ∀ z ∈ H ∩ ball (x : ℂ) r, 0 < (G z).im) (hnc : ¬ ∀ᶠ z in 𝓝 (x : ℂ), G z = G x) :
    deriv G x ≠ 0 := by
  have hxB : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have han : AnalyticAt ℂ (fun z => G z - G x) x :=
    (hG.analyticAt (isOpen_ball.mem_nhds hxB)).sub analyticAt_const
  have hnz : ¬ ∀ᶠ z in 𝓝 (x : ℂ), G z - G x = 0 := fun h => hnc (h.mono fun z hz => sub_eq_zero.1 hz)
  obtain ⟨n, h, hh, hhx, hev⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnz
  simp only [smul_eq_mul] at hev
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h0 := hev.self_of_nhds
    simp only [sub_self, pow_zero, one_mul] at h0
    exact hhx h0.symm
  intro hd
  -- `n = 1` would give `G′(x) = h(x) ≠ 0`
  have hn1 : n ≠ 1 := by
    rintro rfl
    have h1 := ((hasDerivAt_id (x : ℂ)).sub_const (x : ℂ)).mul hh.differentiableAt.hasDerivAt
    simp only [id, sub_self, zero_mul, one_mul, add_zero] at h1
    have h2 : HasDerivAt (fun z => G z - G x) (h x) x :=
      h1.congr_of_eventuallyEq (hev.mono fun z hz => by
        show G z - G x = (z - x) * h z
        rw [hz, pow_one])
    have h3 : deriv (fun z => G z - G x) x = deriv G x := deriv_sub_const _
    rw [h2.deriv, hd] at h3
    exact hhx h3
  have hn2 : 2 ≤ n := by omega
  -- `h(x)` is real
  have hballev : ∀ᶠ z in 𝓝 (x : ℂ), z ∈ ball (x : ℂ) r := isOpen_ball.mem_nhds hxB
  have hev' : ∀ᶠ t : ℝ in 𝓝 x, (t : ℂ) ∈ ball (x : ℂ) r ∧ G t - G x = ((t : ℂ) - x) ^ n * h t :=
    (continuous_ofReal.tendsto x).eventually (hballev.and hev)
  have himh : (h x).im = 0 := by
    have hlim : Tendsto (fun t : ℝ => (h t).im) (𝓝[>] x) (𝓝 (h x).im) :=
      ((continuous_im.tendsto _).comp ((hh.continuousAt.tendsto).comp (continuous_ofReal.tendsto x))).mono_left
        nhdsWithin_le_nhds
    have hzero : ∀ᶠ t : ℝ in 𝓝[>] x, (h (t : ℂ)).im = 0 := by
      filter_upwards [hev'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht (htx : x < t)
      have hGt := congrArg Complex.im ht.2
      rw [Complex.sub_im, hreal _ ht.1 (ofReal_im t), hreal _ hxB (ofReal_im x), sub_zero,
        show ((t : ℂ) - x) ^ n = (((t - x) ^ n : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul] at hGt
      have hpow : (0 : ℝ) < (t - x) ^ n := pow_pos (sub_pos.2 htx) n
      exact (mul_eq_zero.1 hGt.symm).resolve_left hpow.ne'
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hzero.mono fun t ht => ht.symm))
  set a := (h x).re with ha
  have hhxa : h x = (a : ℂ) := Complex.ext (by simp [ha]) (by simp [himh])
  have ha0 : a ≠ 0 := fun h0 => hhx (by rw [hhxa, h0, ofReal_zero])
  -- the bad direction
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  obtain ⟨θ, hθ0, hθπ, hsin⟩ : ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ a * Real.sin (n * θ) < 0 := by
    have hn2r : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    rcases lt_or_gt_of_ne ha0 with hneg | hposa
    · refine ⟨Real.pi / (2 * n), by positivity, ?_, ?_⟩
      · rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
      · rw [show (n : ℝ) * (Real.pi / (2 * n)) = Real.pi / 2 by field_simp, Real.sin_pi_div_two]; linarith
    · refine ⟨3 * Real.pi / (2 * n), by positivity, ?_, ?_⟩
      · rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
      · rw [show (n : ℝ) * (3 * Real.pi / (2 * n)) = Real.pi + Real.pi / 2 by field_simp; ring,
          Real.sin_add_pi_div_two, Real.cos_pi]
        linarith
  set e : ℂ := exp (θ * I) with he
  have hz : Tendsto (fun t : ℝ => (x : ℂ) + t * e) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have hc : Continuous fun t : ℝ => (x : ℂ) + t * e := continuous_const.add (continuous_ofReal.mul continuous_const)
    have := hc.tendsto 0
    simp only [ofReal_zero, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlimw : Tendsto (fun t : ℝ => (e ^ n * h ((x : ℂ) + (t : ℂ) * e)).im) (𝓝[>] 0)
      (𝓝 (a * Real.sin (n * θ))) := by
    have h1 := (continuous_im.tendsto _).comp ((tendsto_const_nhds (x := e ^ n)).mul (hh.continuousAt.tendsto.comp hz))
    have hval : (e ^ n * h x).im = a * Real.sin (n * θ) := by
      rw [hhxa, he, ← Complex.exp_nat_mul, show (n : ℂ) * (θ * I) = ((n * θ : ℝ) : ℂ) * I by push_cast; ring,
        mul_comm, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
    rw [← hval]
    exact h1
  have hneg : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (e ^ n * h ((x : ℂ) + (t : ℂ) * e)).im < 0 :=
    hlimw.eventually (gt_mem_nhds hsin)
  have hall : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ((x : ℂ) + (t : ℂ) * e ∈ ball (x : ℂ) r ∧
      G ((x : ℂ) + (t : ℂ) * e) - G x = ((x : ℂ) + (t : ℂ) * e - x) ^ n * h ((x : ℂ) + (t : ℂ) * e)) ∧
      (e ^ n * h ((x : ℂ) + (t : ℂ) * e)).im < 0 ∧ 0 < t :=
    (hz.eventually (hballev.and hev)).and (hneg.and self_mem_nhdsWithin)
  obtain ⟨t, ⟨hB, hE⟩, hN, ht⟩ := hall.exists
  have hsinθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have hzH : (x : ℂ) + t * e ∈ H := by
    show 0 < ((x : ℂ) + t * e).im
    rw [Complex.add_im, ofReal_im, zero_add, Complex.im_ofReal_mul, he, Complex.exp_ofReal_mul_I_im]
    exact mul_pos ht hsinθ
  have hGpos := hpos _ ⟨hzH, hB⟩
  have hGx : (G x).im = 0 := hreal _ hxB (ofReal_im x)
  have hcalc : (G ((x : ℂ) + t * e)).im = t ^ n * (e ^ n * h ((x : ℂ) + t * e)).im := by
    have h1 := congrArg Complex.im hE
    rw [Complex.sub_im, hGx, sub_zero, add_sub_cancel_left, mul_pow,
      show ((t : ℂ)) ^ n = ((t ^ n : ℝ) : ℂ) by push_cast; ring, mul_assoc, Complex.im_ofReal_mul] at h1
    exact h1
  have : t ^ n * (e ^ n * h ((x : ℂ) + t * e)).im < 0 := mul_neg_of_pos_of_neg (pow_pos ht n) hN
  linarith

/-- **The positive reflected derivative from boundary data with injectivity on the OPEN half-disc.** -/
theorem exists_pos_tendsto_deriv_of_reflect' {g : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r)) (hc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0) (hmaps : ∀ z ∈ H ∩ ball (x : ℂ) r, g z ∈ H)
    (hinj : InjOn g (H ∩ ball (x : ℂ) r)) :
    ∃ b : ℝ, 0 < b ∧ Tendsto (deriv g) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
  set B := ball (x : ℂ) r with hB
  obtain ⟨G, hG, hGg, hsym⟩ := QuantumZipper.CA.exists_reflection_extension hd hc hreal
  have hxB : (x : ℂ) ∈ B := mem_ball_self hr
  have hHB : H ∩ B ⊆ Hbar ∩ B := inter_subset_inter_left _ fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im)
  have hxHbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im]
  have hGconj : ∀ z ∈ B, G z = conj (G (conj z)) := fun z hz => by
    have h := hsym (conj z) (QuantumZipper.CA.conj_mem_ball_ofReal hz)
    rw [conj_conj] at h
    exact h
  have hGx : HasDerivAt G (deriv G x) x := (hG.differentiableAt (isOpen_ball.mem_nhds hxB)).hasDerivAt
  have hreal' : (deriv G x).im = 0 := by
    have hev : G =ᶠ[𝓝 (x : ℂ)] (conj ∘ G ∘ conj) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxB) fun z hz => hGconj z hz
    have h1 : deriv G x = deriv (conj ∘ G ∘ conj) x := hev.deriv_eq
    rw [deriv_conj_conj] at h1
    simp only [Function.comp_apply, conj_ofReal] at h1
    exact conj_eq_iff_im.1 h1.symm
  -- `G` is not locally constant (injective on the open upper half-disc)
  have hnc : ¬ ∀ᶠ z in 𝓝 (x : ℂ), G z = G x := by
    intro hconst
    obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.1 (hconst.and (isOpen_ball.mem_nhds hxB))
    set ε' := min ε r / 2 with hε'
    have hε'0 : 0 < ε' := by positivity
    have hz1 : (x : ℂ) + ((ε' / 2 : ℝ) : ℂ) * I ∈ ball (x : ℂ) ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith [min_le_left ε r]
    have hz2 : (x : ℂ) + ((ε' : ℝ) : ℂ) * I ∈ ball (x : ℂ) ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith [min_le_left ε r]
    have hH1 : (x : ℂ) + ((ε' / 2 : ℝ) : ℂ) * I ∈ H := show 0 < ((x : ℂ) + ((ε' / 2 : ℝ) : ℂ) * I).im by
      simp only [Complex.add_im, ofReal_im, Complex.mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add]
      positivity
    have hH2 : (x : ℂ) + ((ε' : ℝ) : ℂ) * I ∈ H := show 0 < ((x : ℂ) + ((ε' : ℝ) : ℂ) * I).im by
      simp only [Complex.add_im, ofReal_im, Complex.mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add]
      positivity
    obtain ⟨h1, hB1⟩ := hεB hz1
    obtain ⟨h2, hB2⟩ := hεB hz2
    have heq : g ((x : ℂ) + ((ε' / 2 : ℝ) : ℂ) * I) = g ((x : ℂ) + ((ε' : ℝ) : ℂ) * I) := by
      rw [← hGg (hHB ⟨hH1, hB1⟩), ← hGg (hHB ⟨hH2, hB2⟩), h1, h2]
    have := hinj ⟨hH1, hB1⟩ ⟨hH2, hB2⟩ heq
    have him := congrArg Complex.im this
    simp only [Complex.add_im, ofReal_im, Complex.mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
      zero_add] at him
    linarith
  have hGreal : ∀ z ∈ B, z.im = 0 → (G z).im = 0 := fun z hz hz0 => by
    rw [hGg ⟨show (0 : ℝ) ≤ z.im from hz0.ge, hz⟩]; exact hreal z hz hz0
  have hGpos : ∀ z ∈ H ∩ B, 0 < (G z).im := fun z hz => by rw [hGg (hHB hz)]; exact hmaps z hz
  have hne : deriv G x ≠ 0 := deriv_ne_zero_of_real_of_im_pos hr hG hGreal hGpos hnc
  -- positivity from the slope in the direction `i` (as in `exists_pos_tendsto_deriv_of_reflect`)
  set b : ℝ := (deriv G x).re with hb
  have hbG : deriv G x = (b : ℂ) := Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im]; exact hreal')
  have hGx0 : (G x).im = 0 := hGreal _ hxB (ofReal_im x)
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hGx)
  have hφ : Tendsto (fun s : ℝ => (s : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun (s : ℝ) (hs : s ∈ Ioi 0) =>
      mul_ne_zero (ofReal_ne_zero.2 (ne_of_gt hs)) I_ne_zero⟩
    have : Continuous fun s : ℝ => (s : ℂ) * I := continuous_ofReal.mul continuous_const
    have h0 := this.tendsto 0
    rw [ofReal_zero, zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hre := (continuous_re.tendsto _).comp (hslope.comp hφ)
  have hpos' : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ (((s : ℂ) * I)⁻¹ • (G ((x : ℂ) + (s : ℂ) * I) - G x)).re := by
    have hball : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), (x : ℂ) + (s : ℂ) * I ∈ B := by
      have hcont : Continuous fun s : ℝ => (x : ℂ) + (s : ℂ) * I :=
        continuous_const.add (continuous_ofReal.mul continuous_const)
      have := hcont.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at this
      exact (this.eventually (isOpen_ball.mem_nhds hxB)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hball, self_mem_nhdsWithin] with s hsB (hs : 0 < s)
    have hsH : (x : ℂ) + (s : ℂ) * I ∈ H := by
      show 0 < ((x : ℂ) + (s : ℂ) * I).im
      simpa using hs
    have hgH : 0 < (G ((x : ℂ) + (s : ℂ) * I)).im := hGpos _ ⟨hsH, hsB⟩
    have hval : (((s : ℂ) * I)⁻¹ • (G ((x : ℂ) + (s : ℂ) * I) - G x)).re =
        (G ((x : ℂ) + (s : ℂ) * I)).im / s := by
      have hinv : ((s : ℂ) * I)⁻¹ = ((-s⁻¹ : ℝ) : ℂ) * I := by
        rw [mul_inv, inv_I]; push_cast; ring
      rw [smul_eq_mul, hinv]
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, sub_re, sub_im, hGx0]
      field_simp
      ring
    rw [hval]
    exact div_nonneg hgH.le hs.le
  have hb0 : 0 ≤ b := by
    have h := ge_of_tendsto hre hpos'
    simpa [Function.comp_def, hb] using h
  have hbne : b ≠ 0 := fun h => hne (by rw [hbG, h, ofReal_zero])
  refine ⟨b, lt_of_le_of_ne hb0 (Ne.symm hbne), ?_⟩
  have hcontd : ContinuousAt (deriv G) x :=
    ((hG.deriv isOpen_ball).continuousOn).continuousAt (isOpen_ball.mem_nhds hxB)
  rw [← hbG]
  refine (hcontd.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with y hy
  have hev : G =ᶠ[𝓝 y] g :=
    Filter.eventuallyEq_of_mem ((isOpen_H.inter isOpen_ball).mem_nhds hy) fun z hz => hGg (hHB hz)
  exact hev.deriv_eq

end InteractingSLE.Sec7.R5Lift
