/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftLattice
import QuantumZipper.Proofs.Complex.BasicsReflection
import QuantumZipper.Proofs.Complex.KoebeBasic

/-!
# Lemma R.5's common phase: the positive reflected derivative from boundary data

Packet PROVE-R5-LIFT. Lemma R.5's transitions "reflect across the base with positive derivative" (spec p. 475). The
lattice-limit theorems of `R5LiftLattice` take this as the hypothesis that the transition's derivative tends to a
positive real number within `ℍ`. Here it is derived from boundary data by Schwarz reflection
(`QuantumZipper.CA.exists_reflection_extension`):

* **`exists_pos_tendsto_deriv_of_reflect`**: if `g` is holomorphic on `ℍ ∩ B(x, r)`, continuous on `ℍ̄ ∩ B(x, r)`,
  real on the real diameter, maps `ℍ ∩ B(x, r)` into `ℍ` and is injective on `ℍ̄ ∩ B(x, r)`, then `g′ → b` within `ℍ`
  at `x` for a real `b > 0`;
* **`exists_pos_tendsto_deriv_of_reflect_eqOn`**: the same for a map `S` agreeing with such a `g` on `ℍ ∩ B(x, r)`
  (the transition itself is only meaningful in `ℍ`; its boundary values are those of an extension `g`).

The extension `G` is holomorphic on the disc and commutes with `conj`, so `G′(x)` is real; `G` is injective on the
disc (upper and lower halves have images in the upper and lower half-planes), so `G′(x) ≠ 0`
(`QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn`); the slope of `G` in the direction `i` at `x` is `Im G(x + is)/s > 0`,
so `G′(x) ≥ 0`.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar isOpen_H)
open scoped ComplexConjugate

namespace InteractingSLE.Sec7.R5Lift

/-- **The positive reflected derivative** from boundary data (Schwarz reflection). -/
theorem exists_pos_tendsto_deriv_of_reflect {g : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r)) (hc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0) (hmaps : ∀ z ∈ H ∩ ball (x : ℂ) r, g z ∈ H)
    (hinj : InjOn g (Hbar ∩ ball (x : ℂ) r)) :
    ∃ b : ℝ, 0 < b ∧ Tendsto (deriv g) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
  set B := ball (x : ℂ) r with hB
  obtain ⟨G, hG, hGg, hsym⟩ := QuantumZipper.CA.exists_reflection_extension hd hc hreal
  have hxB : (x : ℂ) ∈ B := mem_ball_self hr
  have hHB : H ∩ B ⊆ Hbar ∩ B := inter_subset_inter_left _ fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im)
  -- `G = conj ∘ G ∘ conj` on the disc
  have hGconj : ∀ z ∈ B, G z = conj (G (conj z)) := fun z hz => by
    have h := hsym (conj z) (QuantumZipper.CA.conj_mem_ball_ofReal hz)
    rw [conj_conj] at h
    exact h
  -- the derivative of `G` at `x` is real
  have hGx : HasDerivAt G (deriv G x) x :=
    (hG.differentiableAt (isOpen_ball.mem_nhds hxB)).hasDerivAt
  have hreal' : (deriv G x).im = 0 := by
    have hev : G =ᶠ[𝓝 (x : ℂ)] (conj ∘ G ∘ conj) :=
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hxB) fun z hz => hGconj z hz
    have h1 : deriv G x = deriv (conj ∘ G ∘ conj) x := hev.deriv_eq
    rw [deriv_conj_conj] at h1
    simp only [Function.comp_apply, conj_ofReal] at h1
    exact conj_eq_iff_im.1 h1.symm
  -- `G` is injective on the disc
  have himG : ∀ z ∈ B, 0 ≤ z.im → 0 ≤ (G z).im := fun z hz hz0 => by
    rw [hGg ⟨hz0, hz⟩]
    rcases hz0.lt_or_eq with hpos | hzero
    · exact (le_of_lt (hmaps z ⟨hpos, hz⟩) : 0 ≤ (g z).im)
    · exact (hreal z hz hzero.symm).ge
  have himG' : ∀ z ∈ B, z.im < 0 → (G z).im < 0 := fun z hz hz0 => by
    have hcz : conj z ∈ H ∩ B :=
      ⟨show 0 < (conj z).im by rw [conj_im]; linarith, QuantumZipper.CA.conj_mem_ball_ofReal hz⟩
    rw [hGconj z hz, conj_im, neg_lt_zero, hGg (hHB hcz)]
    exact hmaps _ hcz
  have hinjG : InjOn G B := by
    intro z₁ hz₁ z₂ hz₂ h
    by_cases h₁ : 0 ≤ z₁.im <;> by_cases h₂ : 0 ≤ z₂.im
    · rw [hGg ⟨h₁, hz₁⟩, hGg ⟨h₂, hz₂⟩] at h
      exact hinj ⟨h₁, hz₁⟩ ⟨h₂, hz₂⟩ h
    · have := himG z₁ hz₁ h₁; have := himG' z₂ hz₂ (not_le.1 h₂); rw [h] at *; linarith
    · have := himG z₂ hz₂ h₂; have := himG' z₁ hz₁ (not_le.1 h₁); rw [h] at *; linarith
    · have hc₁ : conj z₁ ∈ Hbar ∩ B :=
        ⟨show (0 : ℝ) ≤ (conj z₁).im by rw [conj_im]; linarith [not_le.1 h₁],
          QuantumZipper.CA.conj_mem_ball_ofReal hz₁⟩
      have hc₂ : conj z₂ ∈ Hbar ∩ B :=
        ⟨show (0 : ℝ) ≤ (conj z₂).im by rw [conj_im]; linarith [not_le.1 h₂],
          QuantumZipper.CA.conj_mem_ball_ofReal hz₂⟩
      rw [hGconj z₁ hz₁, hGconj z₂ hz₂, hGg hc₁, hGg hc₂] at h
      have h' := hinj hc₁ hc₂ (by simpa using congrArg conj h)
      simpa using congrArg conj h'
  have hne : deriv G x ≠ 0 := QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hG hinjG hxB
  -- the slope in the direction `i`
  set b : ℝ := (deriv G x).re with hb
  have hbG : deriv G x = (b : ℂ) := Complex.ext (by rw [ofReal_re]) (by rw [ofReal_im]; exact hreal')
  have hxHbar : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by rw [ofReal_im]
  have hGx0 : (G x).im = 0 := by rw [hGg ⟨hxHbar, hxB⟩]; exact hreal _ hxB (ofReal_im x)
  have hslope := (hasDerivAt_iff_tendsto_slope_zero.1 hGx)
  have hφ : Tendsto (fun s : ℝ => (s : ℂ) * I) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun (s : ℝ) (hs : s ∈ Ioi 0) =>
      mul_ne_zero (ofReal_ne_zero.2 (ne_of_gt hs)) I_ne_zero⟩
    have : Continuous fun s : ℝ => (s : ℂ) * I := continuous_ofReal.mul continuous_const
    have h0 := this.tendsto 0
    rw [ofReal_zero, zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hre := (continuous_re.tendsto _).comp (hslope.comp hφ)
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ),
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
    have hgH : 0 < (G ((x : ℂ) + (s : ℂ) * I)).im := by
      rw [hGg (hHB ⟨hsH, hsB⟩)]; exact hmaps _ ⟨hsH, hsB⟩
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
    have h := ge_of_tendsto hre hpos
    simpa [Function.comp_def, hb] using h
  have hbne : b ≠ 0 := fun h => hne (by rw [hbG, h, ofReal_zero])
  refine ⟨b, lt_of_le_of_ne hb0 (Ne.symm hbne), ?_⟩
  -- `g′ = G′` on `ℍ ∩ B`, and `G′` is continuous at `x`
  have hcontd : ContinuousAt (deriv G) x :=
    ((hG.deriv isOpen_ball).continuousOn).continuousAt (isOpen_ball.mem_nhds hxB)
  rw [← hbG]
  refine (hcontd.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hxB)] with y hy
  have hev : G =ᶠ[𝓝 y] g :=
    Filter.eventuallyEq_of_mem ((isOpen_H.inter isOpen_ball).mem_nhds hy) fun z hz => hGg (hHB hz)
  exact hev.deriv_eq

/-- **The positive reflected derivative of a map agreeing with a boundary-regular extension** on `ℍ ∩ B(x, r)`. -/
theorem exists_pos_tendsto_deriv_of_reflect_eqOn {S g : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hSg : EqOn S g (H ∩ ball (x : ℂ) r))
    (hd : DifferentiableOn ℂ g (H ∩ ball (x : ℂ) r)) (hc : ContinuousOn g (Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0) (hmaps : ∀ z ∈ H ∩ ball (x : ℂ) r, g z ∈ H)
    (hinj : InjOn g (Hbar ∩ ball (x : ℂ) r)) :
    ∃ b : ℝ, 0 < b ∧ Tendsto (deriv S) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
  obtain ⟨b, hb, hlim⟩ := exists_pos_tendsto_deriv_of_reflect hr hd hc hreal hmaps hinj
  refine ⟨b, hb, hlim.congr' ?_⟩
  filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hr))] with y hy
  exact (Filter.eventuallyEq_of_mem ((isOpen_H.inter isOpen_ball).mem_nhds hy) fun z hz => (hSg hz).symm).deriv_eq

end InteractingSLE.Sec7.R5Lift
