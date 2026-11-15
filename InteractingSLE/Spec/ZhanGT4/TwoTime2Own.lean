/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoTime2Other
import QuantumZipper.Proofs.Zipper.JointModDet
import QuantumZipper.Proofs.RS.GenerationBasic

/-!
# The own-time identity (D1): `∂_t h_t(z) = 2A₁²/(h_t(z) − A₀) − 2h_t'(z)/(z − W_t)`

Packet PROVE-ZHAN-GT4-A4. Source: Astra, *Follow-up proofs and dependency audit*, Part A.1.1, (D1)
(`source/external/AstraIG1/ig1_followup_proofs.txt` L245–L262, ruling R38): "For fixed `t_k`, differentiation of
`G = h_j ∘ g_j`, with the image-capacity derivative `A²_{j,1}`, gives
`∂_{t_j} h_j(z) = 2A²_{j,1}/(h_j(z) − A_{j,0}) − 2h_j'(z)/(z − W_j)`."

## The inverse Loewner map

`invMap W t z = g_t⁻¹(z) = f_t⁻¹(z − W_t)` (QuantumZipper's centred inverse `fwdMapInv`). For `z ∈ ℍ`:

* `hasDerivWithinAt_invMap`: **`∂_t g_t⁻¹(z) = −(2/(z − W_t)) / g_t'(g_t⁻¹(z))`** within `[0, T]` (the classical
  `∂_t f_t = −f_t' · 2/(z − W_t)`). Proof: with `w₀ = g_{t₀}⁻¹(z)` and `w_t = g_t⁻¹(z)`, the linear identity of the
  flow gives `w_t − w₀ = −(g_t(w₀) − g_{t₀}(w₀)) / Q(t, w_t)` with `Q(t, w) = exp(−∫₀ᵗ 2/(f_s(w) f_s(w₀)))`; the first
  factor is the Loewner equation at `w₀`, and `Q(t, w_t) → g_{t₀}'(w₀)` by joint continuity (QuantumZipper's joint
  continuity of `(t, z) ↦ f_t⁻¹(z)`, `RegUnif.continuousOn_fwdMapInv_joint`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

/-- The uncentred inverse Loewner map `g_t⁻¹(z) = f_t⁻¹(z − W_t)`. -/
def invMap (W : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ := fwdMapInv W t (z - W t)

variable {W : ℝ → ℝ}

theorem sub_ofReal_mem_H {z : ℂ} (hz : z ∈ H) (c : ℝ) : z - (c : ℂ) ∈ H := by
  show 0 < (z - (c : ℂ)).im
  rw [sub_im, ofReal_im, sub_zero]; exact hz

theorem invMap_mem (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    invMap W t z ∈ H \ fwdHull W t :=
  QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht (sub_ofReal_mem_H hz _)

theorem fwdMap_invMap (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    fwdMap W t (invMap W t z) = z - W t :=
  QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht (sub_ofReal_mem_H hz _)

/-- `t ↦ g_t⁻¹(z)` is continuous on `[0, T]`. -/
theorem continuousOn_invMap_time (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) {z : ℂ} (hz : z ∈ H) :
    ContinuousOn (fun t => invMap W t z) (Icc 0 T) := by
  have hj := QuantumZipper.RegUnif.continuousOn_fwdMapInv_joint hW hW0 T
  have hcl : Continuous fun t : ℝ => (t, z - (W t : ℂ)) :=
    continuous_id.prodMk (continuous_const.sub (continuous_ofReal.comp hW))
  have h := hj.comp hcl.continuousOn fun t ht => (⟨ht, sub_ofReal_mem_H hz _⟩ :
    (t, z - (W t : ℂ)) ∈ Icc 0 T ×ˢ H)
  simp only [Function.comp_def] at h
  exact h

/-- **The time derivative of the inverse Loewner map**: `∂_t g_t⁻¹(z) = −(2/(z − W_t)) / g_t'(g_t⁻¹(z))` within
`[0, T]`, for `z ∈ ℍ` (`g_t' = f_t' = exp L_t`). -/
theorem hasDerivWithinAt_invMap (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} {z : ℂ} (hz : z ∈ H)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun t => invMap W t z)
      (-(2 / (z - W t₀)) / Complex.exp (logDerivFwd W t₀ (invMap W t₀ z))) (Icc 0 T) t₀ := by
  set w₀ := invMap W t₀ z with hw₀def
  have hw₀ := invMap_mem hW hW0 ht₀.1 hz
  have hfw₀ : fwdMap W t₀ w₀ = z - W t₀ := fwdMap_invMap hW hW0 ht₀.1 hz
  obtain ⟨-, T₁, hT₁, u, hu⟩ := (QuantumZipper.FwdHolo.mem_compl_fwdHull_iff ht₀.1).1 hw₀
  have hT₁0 : 0 ≤ T₁ := ht₀.1.trans hT₁.le
  obtain ⟨δ, hδ, hlow⟩ := InteractingSLE.exists_two_mul_le_norm_of_isForwardSol hT₁0 hu
  have hw₀B : w₀ ∈ ball w₀ (aliveRad T₁ δ) := mem_ball_self (aliveRad_pos hδ)
  have ht₀1 : t₀ ∈ Icc (0 : ℝ) T₁ := ⟨ht₀.1, hT₁.le⟩
  have hmem : Icc (0 : ℝ) T₁ \ {t₀} ∈ 𝓝[Icc 0 T \ {t₀}] t₀ :=
    mem_nhdsWithin.2 ⟨Iio T₁, isOpen_Iio, hT₁, fun t ht => ⟨⟨ht.2.1.1, ht.1.le⟩, ht.2.2⟩⟩
  have hcw : Tendsto (fun t => invMap W t z) (𝓝[Icc 0 T \ {t₀}] t₀) (𝓝 w₀) :=
    ((continuousOn_invMap_time hW hW0 T hz) t₀ ht₀).tendsto.mono_left (nhdsWithin_mono _ sdiff_subset)
  have hevB : ∀ᶠ t in 𝓝[Icc 0 T \ {t₀}] t₀, invMap W t z ∈ ball w₀ (aliveRad T₁ δ) :=
    hcw (isOpen_ball.mem_nhds hw₀B)
  -- the Loewner equation at `w₀`
  have hgs := (hasDerivWithinAt_iff_tendsto_slope.1 (hasDerivWithinAt_gmap hW hu ht₀1)).mono_left
    (nhdsWithin_le_of_mem hmem)
  -- the factor `Q(t, w_t) → g_{t₀}'(w₀)`
  set F : ℝ → ℂ → ℂ := fun s w => 2 / (fwdMap W s w * fwdMap W s w₀) with hF
  have hI := continuousOn_integral_of_holo (F := F) (continuousOn_two_div_mul_aliveDisc hW hu hδ hlow hw₀B)
  have hpair : Tendsto (fun t => (t, invMap W t z)) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝[Icc 0 T₁ ×ˢ ball w₀ (aliveRad T₁ δ)] (t₀, w₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(tendsto_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hcw, ?_⟩
    filter_upwards [hmem, hevB] with t ht hB using ⟨ht.1, hB⟩
  have hQ : Tendsto (fun t => Complex.exp (-∫ s in (0 : ℝ)..t, F s (invMap W t z))) (𝓝[Icc 0 T \ {t₀}] t₀)
      (𝓝 (Complex.exp (logDerivFwd W t₀ w₀))) := by
    have h1 := ((hI (t₀, w₀) ⟨ht₀1, hw₀B⟩).tendsto.comp hpair).neg
    have h2 := (Complex.continuous_exp.tendsto _).comp h1
    have hval : Complex.exp (-∫ s in (0 : ℝ)..t₀, F s w₀) = Complex.exp (logDerivFwd W t₀ w₀) := by
      simp only [hF, logDerivFwd, sq]
    rw [← hval]
    exact h2
  have hlim := (hgs.neg).div hQ (Complex.exp_ne_zero _)
  rw [hfw₀] at hlim
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine hlim.congr' ?_
  filter_upwards [hmem, hevB] with t ht hB
  have htt : t - t₀ ≠ 0 := sub_ne_zero.2 ht.2
  have hlin := fwdMap_sub_eq_aliveDisc hW hu hδ hlow hw₀B hB ht.1
  have hft : fwdMap W t (invMap W t z) = z - W t := fwdMap_invMap hW hW0 ht.1.1 hz
  have hE := Complex.exp_ne_zero (-∫ s in (0 : ℝ)..t, F s (invMap W t z))
  rw [hft] at hlin
  simp only [Pi.div_apply, slope_def_module]
  rw [← hw₀def, hfw₀, Complex.real_smul, Complex.real_smul]
  have htt' : ((t : ℂ) - t₀) ≠ 0 := by exact_mod_cast htt
  push_cast
  field_simp
  linear_combination hlin
/-- A product whose first factor vanishes at `x` is differentiable there when the second factor is continuous. -/
theorem hasDerivWithinAt_mul_of_eq_zero {u c : ℝ → ℂ} {u' : ℂ} {s : Set ℝ} {x : ℝ}
    (hu : HasDerivWithinAt u u' s x) (hu0 : u x = 0) (hc : ContinuousWithinAt c s x) :
    HasDerivWithinAt (fun t => u t * c t) (u' * c x) s x := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hu ⊢
  have h := hu.mul (hc.tendsto.mono_left (nhdsWithin_mono _ sdiff_subset))
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp only [slope_def_module, hu0, zero_mul, sub_zero, Complex.real_smul]
  ring

/-- `g_t⁻¹` is holomorphic on `ℍ` with `(g_t⁻¹)'(z) · g_t'(g_t⁻¹(z)) = 1`. -/
theorem hasDerivAt_invMap (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ H) :
    HasDerivAt (invMap W t) (deriv (fwdMapInv W t) (z - W t)) z ∧
      deriv (fwdMapInv W t) (z - W t) * deriv (fwdMap W t) (invMap W t z) = 1 := by
  refine ⟨?_, ?_⟩
  · have h := (QuantumZipper.RS.differentiableAt_fwdMapInv hW hW0 ht (sub_ofReal_mem_H hz (W t))).hasDerivAt
    have h2 := h.comp z ((hasDerivAt_id z).sub_const (W t : ℂ))
    have h3 : HasDerivAt (fun x => fwdMapInv W t (x - (W t : ℂ))) (deriv (fwdMapInv W t) (z - W t)) z := by
      simpa [Function.comp_def] using h2
    exact h3
  · have h := InteractingSLE.deriv_fwdMapInv_mul_deriv_fwdMap hW hW0 ht (invMap_mem hW hW0 ht hz)
    rwa [fwdMap_invMap hW hW0 ht hz] at h

/-- **The core of (D1).** In the setting of Aux. lemma 8 (image clock `a`, image driver `W̃` with
`K̃_{a(t)} = φ(K_t)`), for `z ∈ ℍ` with `w₀ = g_{t₀}⁻¹(z) ∉ A` and `ȧ(t₀) = c`: the map
`t ↦ h_t(z) = g̃_{a(t)}(φ(g_t⁻¹(z)))` has derivative
`c · 2/(g̃_{a(t₀)}(ζ₀) − W̃(a(t₀))) + φ'(w₀) · ∂_t g_t⁻¹(z) · g̃'_{a(t₀)}(ζ₀)`, `ζ₀ = φ(w₀)`, within `[0, T]`. -/
theorem hasDerivWithinAt_ownMap_core (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hAK : Disjoint A (fwdHull W T)) {a W' : ℝ → ℝ} (hW'c : Continuous W') (ha0 : a 0 = 0)
    (hamono : StrictMonoOn a (Icc 0 T)) (hhull : ∀ t ∈ Icc (0 : ℝ) T, fwdHull W' (a t) = φ '' fwdHull W t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) T) {c : ℝ} (hder : HasDerivWithinAt a c (Icc 0 T) t₀)
    {z : ℂ} (hz : z ∈ H) (hzA : invMap W t₀ z ∉ A) :
    HasDerivWithinAt (fun s => fwdMap W' (a s) (φ (invMap W s z)) + W' (a s))
      (c * (2 / fwdMap W' (a t₀) (φ (invMap W t₀ z))) +
        deriv φ (invMap W t₀ z) * (-(2 / (z - W t₀)) / Complex.exp (logDerivFwd W t₀ (invMap W t₀ z))) *
          Complex.exp (logDerivFwd W' (a t₀) (φ (invMap W t₀ z)))) (Icc 0 T) t₀ := by
  set w₀ := invMap W t₀ z with hw₀def
  have hw₀ := invMap_mem hW hW0 ht₀.1 hz
  obtain ⟨-, T₁, hT₁, u, hu⟩ := (QuantumZipper.FwdHolo.mem_compl_fwdHull_iff ht₀.1).1 hw₀
  set T₂ := min T ((t₀ + T₁) / 2) with hT₂
  have ht₀T₂ : t₀ ≤ T₂ := le_min ht₀.2 (by linarith)
  have hT₂T : T₂ ≤ T := min_le_left _ _
  have hT₂0 : 0 ≤ T₂ := ht₀.1.trans ht₀T₂
  have hT₂mem : T₂ ∈ Icc (0 : ℝ) T := ⟨hT₂0, hT₂T⟩
  have hnhd : Icc (0 : ℝ) T₂ ∈ 𝓝[Icc 0 T] t₀ :=
    mem_nhdsWithin.2 ⟨Iio ((t₀ + T₁) / 2), isOpen_Iio, by show t₀ < (t₀ + T₁) / 2; linarith,
      fun t ht => ⟨ht.2.1, le_min ht.2.2 ht.1.le⟩⟩
  -- `w₀` is alive at `T₂`, so `ζ₀ = φ(w₀)` is alive for the image chain at `a(T₂)`
  have hw₀K₂ : w₀ ∉ fwdHull W T₂ := by
    rintro ⟨-, hle⟩
    have h1 := QuantumZipper.ofReal_le_swallowTime (ht₀.1.trans hT₁.le) ⟨u, hu⟩
    have h2 : ENNReal.ofReal T₂ < ENNReal.ofReal T₁ :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith [ht₀.1])).2 (lt_of_le_of_lt (min_le_right _ _) (by linarith))
    exact absurd (h1.trans hle) (not_le.2 h2)
  have hw₀A : w₀ ∈ H \ A := ⟨hw₀.1, hzA⟩
  have hζH : φ w₀ ∈ H := hφ.1.2.mapsTo hw₀A
  have hζK : φ w₀ ∉ fwdHull W' (a T₂) := by
    rw [hhull T₂ hT₂mem]
    rintro ⟨k, hk, hkw⟩
    have hkT : k ∈ fwdHull W T := (QuantumZipper.fwdHull_mono.1 hT₂T) hk
    have hkA : k ∉ A := fun hkA => Set.disjoint_left.1 hAK hkA hkT
    have hkH : k ∈ H := (QuantumZipper.fwdHull_mono.2 T) hkT
    exact hw₀K₂ (hφ.1.2.injOn ⟨hkH, hkA⟩ hw₀A hkw ▸ hk)
  have hTmem : T₂ ∈ Icc (0 : ℝ) T₂ := ⟨hT₂0, le_rfl⟩
  have hmaps₂ : MapsTo a (Icc 0 T₂) (Icc 0 (a T₂)) := fun s hs => by
    have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans hT₂T⟩
    refine ⟨?_, hamono.monotoneOn hs' hT₂mem hs.2⟩
    rw [← ha0]; exact hamono.monotoneOn ⟨le_rfl, hT₂0.trans hT₂T⟩ hs' hs.1
  have haT₂ : 0 ≤ a T₂ := (hmaps₂ hTmem).1
  obtain ⟨v, hv⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull haT₂ hζH hζK
  obtain ⟨ε, hε, hlowv⟩ := InteractingSLE.exists_two_mul_le_norm_of_isForwardSol haT₂ hv
  have hζD : φ w₀ ∈ ball (φ w₀) (aliveRad (a T₂) ε) := mem_ball_self (aliveRad_pos hε)
  have ht₀2 : t₀ ∈ Icc (0 : ℝ) T₂ := ⟨ht₀.1, ht₀T₂⟩
  -- the second bracket: the clocked Loewner equation at `ζ₀`
  have hΓ := (hasDerivWithinAt_gmap_clock hW'c hv hmaps₂ ht₀2
    (hder.mono (Icc_subset_Icc_right hT₂T))).mono_of_mem_nhdsWithin hnhd
  -- the first bracket: `u(t) = φ(g_t⁻¹ z) − ζ₀`
  have hφd : DifferentiableAt ℂ φ w₀ := hφ.1.1.differentiableAt (hA.2.2.1.mem_nhds hw₀A)
  have hu' := (hφd.hasDerivAt.comp_hasDerivWithinAt t₀ (hasDerivWithinAt_invMap hW hW0 hz ht₀)).sub_const (φ w₀)
  have hcw : ContinuousWithinAt (fun t => φ (invMap W t z)) (Icc 0 T) t₀ :=
    hφd.continuousAt.comp_continuousWithinAt (g := φ) (f := fun t => invMap W t z)
      ((continuousOn_invMap_time hW hW0 T hz) t₀ ht₀)
  have hevD : ∀ᶠ t in 𝓝[Icc 0 T] t₀, φ (invMap W t z) ∈ ball (φ w₀) (aliveRad (a T₂) ε) :=
    hcw (isOpen_ball.mem_nhds hζD)
  -- the factor `Q̃(t) = exp(−∫₀^{a t} 2/(f̃_s(φ w_t) f̃_s(ζ₀)))`
  set F : ℝ → ℂ → ℂ := fun s ζ => 2 / (fwdMap W' s ζ * fwdMap W' s (φ w₀)) with hF
  have hI := continuousOn_integral_of_holo (F := F) (continuousOn_two_div_mul_aliveDisc hW'c hv hε hlowv hζD)
  have hpair : Tendsto (fun t => (a t, φ (invMap W t z))) (𝓝[Icc 0 T] t₀)
      (𝓝[Icc 0 (a T₂) ×ˢ ball (φ w₀) (aliveRad (a T₂) ε)] (a t₀, φ w₀)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hder.continuousWithinAt.tendsto.prodMk_nhds hcw.tendsto, ?_⟩
    filter_upwards [hnhd, hevD] with t ht hD using ⟨hmaps₂ ht, hD⟩
  have hc : ContinuousWithinAt (fun t => Complex.exp (-∫ s in (0 : ℝ)..a t, F s (φ (invMap W t z))))
      (Icc 0 T) t₀ := by
    have h1 := ((hI (a t₀, φ w₀) ⟨hmaps₂ ht₀2, hζD⟩).tendsto.comp hpair).neg
    exact (Complex.continuous_exp.tendsto _).comp h1
  have hprod := hasDerivWithinAt_mul_of_eq_zero hu' (by simp only [Function.comp_apply, hw₀def, sub_self]) hc
  have hsum := hΓ.add hprod
  have hval : Complex.exp (-∫ s in (0 : ℝ)..a t₀, F s (φ (invMap W t₀ z))) =
      Complex.exp (logDerivFwd W' (a t₀) (φ w₀)) := by
    simp only [hF, logDerivFwd, sq, ← hw₀def]
  rw [hval] at hsum
  have heq : (fun s => fwdMap W' (a s) (φ (invMap W s z)) + W' (a s)) =ᶠ[𝓝[Icc 0 T] t₀]
      ((fun s => fwdMap W' (a s) (φ w₀) + ↑(W' (a s))) + fun t =>
        ((φ ∘ fun t => invMap W t z) t - φ w₀) *
          Complex.exp (-∫ s in (0 : ℝ)..a t, F s (φ (invMap W t z)))) := by
    filter_upwards [hnhd, hevD] with t ht hD
    have hlin := fwdMap_sub_eq_aliveDisc hW'c hv hε hlowv hζD hD (hmaps₂ ht)
    simp only [hF, Pi.add_apply, Function.comp_apply]
    linear_combination hlin
  exact hsum.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin ht₀)

/-- The spatial derivative of `y ↦ g̃_σ(φ(g_t⁻¹(y)))`: `g̃_σ'(ζ₀) φ'(w₀) / g_t'(w₀)`. -/
theorem hasDerivAt_ownMap_space (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ) {W' : ℝ → ℝ} (hW'c : Continuous W')
    {σ : ℝ} (hσ : 0 ≤ σ) {z : ℂ} (hz : z ∈ H) (hzA : invMap W t z ∉ A)
    (hζK : φ (invMap W t z) ∉ fwdHull W' σ) :
    HasDerivAt (fun y => fwdMap W' σ (φ (invMap W t y)) + W' σ)
      (Complex.exp (logDerivFwd W' σ (φ (invMap W t z))) * deriv φ (invMap W t z) /
        Complex.exp (logDerivFwd W t (invMap W t z))) z := by
  have hw₀ := invMap_mem hW hW0 ht hz
  have hw₀A : invMap W t z ∈ H \ A := ⟨hw₀.1, hzA⟩
  have hζH : φ (invMap W t z) ∈ H := hφ.1.2.mapsTo hw₀A
  obtain ⟨hinv, hinv1⟩ := hasDerivAt_invMap hW hW0 ht hz
  have hφd : HasDerivAt φ (deriv φ (invMap W t z)) (invMap W t z) :=
    (hφ.1.1.differentiableAt (hA.2.2.1.mem_nhds hw₀A)).hasDerivAt
  have hf := QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW'c hσ ⟨hζH, hζK⟩
  have hg := QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW ht hw₀
  have h := ((hf.comp z (hφd.comp z hinv)).add_const (W' σ : ℂ))
  refine h.congr_deriv ?_
  rw [hg.deriv] at hinv1
  have hE := Complex.exp_ne_zero (logDerivFwd W t (invMap W t z))
  have hD : deriv (fwdMapInv W t) (z - W t) = (Complex.exp (logDerivFwd W t (invMap W t z)))⁻¹ :=
    eq_inv_of_mul_eq_one_left hinv1
  rw [hD]
  field_simp

/-- **The own-time identity (D1).** Let curve `j` have continuous driver `W` (`W 0 = 0`) on `[0, T]`, `T > 0`, and
freeze the hull `A = K_k` (mapping-out function `φ`, `closure A ∩ closure K_T = ∅`). With the image clock `a` and image
driver `W̃` of Aux. lemma 8, put `h_t(z) = g̃_{a(t)}(φ(g_t⁻¹(z)))`. For every `t ∈ [0, T]` and every mapping-out
function `R` of `g_t(A)`: `R = h_t` off `g_t(A)`, `R(w) → W̃(a(t)) = A_{j,0}` as `w → W_t`, and for every holomorphic
extension `R̂` of `R` across the real line near `W_t` (`A_{j,1} = R̂'(W_t)`) and every `z ∈ ℍ \ g_t(A)`:

  `∂_t h_t(z) = 2A²_{j,1}/(h_t(z) − A_{j,0}) − 2h_t'(z)/(z − W_t)`  (within `[0, T]`).
-/
theorem exists_ownTime_identity (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    {A : Set ℂ} (hA : IsHPHull A) {φ : ℂ → ℂ} (hφ : IsMapOut A φ)
    (hd : Disjoint (closure A) (closure (fwdHull W T))) :
    ∃ (a : ℝ → ℝ) (W' : ℝ → ℝ), Continuous W' ∧ a 0 = 0 ∧ StrictMonoOn a (Icc 0 T) ∧
      (∀ t ∈ Icc (0 : ℝ) T, fwdHull W' (a t) = φ '' fwdHull W t) ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ R : ℂ → ℂ, IsMapOut ((fun z => fwdMap W t z + W t) '' A) R →
        (∀ z ∈ H, invMap W t z ∉ A → fwdMap W' (a t) (φ (invMap W t z)) + W' (a t) = R z) ∧
        Tendsto R (𝓝[H] (W t : ℂ)) (𝓝 (W' (a t) : ℂ)) ∧
        ∀ δ > (0 : ℝ), ∀ Rext : ℂ → ℂ, DifferentiableOn ℂ Rext (ball (W t : ℂ) δ) →
          EqOn Rext R (ball (W t : ℂ) δ ∩ H) → ∀ z ∈ H, invMap W t z ∉ A →
            HasDerivWithinAt (fun s => fwdMap W' (a s) (φ (invMap W s z)) + W' (a s))
              (2 * ((deriv Rext (W t)).re : ℂ) ^ 2 / (R z - W' (a t)) - 2 * deriv R z / (z - W t))
              (Icc 0 T) t := by
  obtain ⟨a, W', hW'c, ha0, hamono, -, hmain⟩ := ConformalImageFull.exists_loewner_image_rate_of_pos hW hT hA hφ hd
  have hAK : Disjoint A (fwdHull W T) :=
    Set.disjoint_left.2 fun x hxA hxK => Set.disjoint_left.1 hd (subset_closure hxA) (subset_closure hxK)
  have hhull : ∀ t ∈ Icc (0 : ℝ) T, fwdHull W' (a t) = φ '' fwdHull W t := fun t ht => (hmain t ht).2.1
  refine ⟨a, W', hW'c, ha0, hamono, hhull, fun t ht R hRm => ?_⟩
  obtain ⟨-, -, hR⟩ := hmain t ht
  obtain ⟨h1, h2, -, hrate⟩ := hR R hRm
  -- `R = h_t` off `g_t(A)`
  have hRid : ∀ y ∈ H, invMap W t y ∉ A → fwdMap W' (a t) (φ (invMap W t y)) + W' (a t) = R y := by
    intro y hy hyA
    have hw := invMap_mem hW hW0 ht.1 hy
    have h := h1 (invMap W t y) ⟨hw.1, fun h => h.elim hyA hw.2⟩
    rwa [fwdMap_invMap hW hW0 ht.1 hy, sub_add_cancel] at h
  refine ⟨hRid, h2, fun δ hδ Rext hRd hRe z hz hzA => ?_⟩
  obtain ⟨-, -, hder⟩ := hrate δ hδ Rext hRd hRe
  have hcore := hasDerivWithinAt_ownMap_core hW hW0 hA hφ hAK hW'c ha0 hamono hhull ht hder hz hzA
  -- the spatial derivative of `R` at `z`
  have hw₀ := invMap_mem hW hW0 ht.1 hz
  have hw₀A : invMap W t z ∈ H \ A := ⟨hw₀.1, hzA⟩
  have hζK : φ (invMap W t z) ∉ fwdHull W' (a t) := by
    rw [hhull t ht]
    rintro ⟨k, hk, hkw⟩
    have hkT : k ∈ fwdHull W T := (QuantumZipper.fwdHull_mono.1 ht.2) hk
    have hkA : k ∉ A := fun hkA => Set.disjoint_left.1 hAK hkA hkT
    have hkH : k ∈ H := (QuantumZipper.fwdHull_mono.2 t) hk
    exact hw₀.2 (hφ.1.2.injOn ⟨hkH, hkA⟩ hw₀A hkw ▸ hk)
  have hat : 0 ≤ a t := by
    rw [← ha0]; exact hamono.monotoneOn ⟨le_rfl, hT.le⟩ ht ht.1
  have hsp := hasDerivAt_ownMap_space hW hW0 ht.1 hA hφ hW'c hat hz hzA hζK
  have hcont : ContinuousOn (invMap W t) H := fun y hy =>
    (hasDerivAt_invMap hW hW0 ht.1 hy).1.continuousAt.continuousWithinAt
  have hO : IsOpen (H ∩ invMap W t ⁻¹' (H \ A)) := hcont.isOpen_inter_preimage QuantumZipper.isOpen_H hA.2.2.1
  have hEq : (fun y => fwdMap W' (a t) (φ (invMap W t y)) + W' (a t)) =ᶠ[𝓝 z] R := by
    filter_upwards [hO.mem_nhds ⟨hz, hw₀A⟩] with y hy using hRid y hy.1 hy.2.2
  have hdR : deriv R z = Complex.exp (logDerivFwd W' (a t) (φ (invMap W t z))) * deriv φ (invMap W t z) /
      Complex.exp (logDerivFwd W t (invMap W t z)) := by
    rw [← hEq.deriv_eq, hsp.deriv]
  have hRz := hRid z hz hzA
  refine hcore.congr_deriv ?_
  rw [hdR, ← hRz]
  have hzW : z - (W t : ℂ) ≠ 0 := fun h => by
    have : (z - (W t : ℂ)).im = 0 := by rw [h, zero_im]
    rw [sub_im, ofReal_im, sub_zero] at this
    exact (ne_of_gt hz) this
  have hE := Complex.exp_ne_zero (logDerivFwd W t (invMap W t z))
  have hf0 : fwdMap W' (a t) (φ (invMap W t z)) ≠ 0 := by
    have hζH : φ (invMap W t z) ∈ H := hφ.1.2.mapsTo hw₀A
    have := QuantumZipper.FwdHolo.mapsTo_fwdMap hW'c hat ⟨hζH, hζK⟩
    intro h
    rw [h] at this
    have h0 : (0 : ℝ) < (0 : ℂ).im := this
    simp at h0
  have hcancel : fwdMap W' (a t) (φ (invMap W t z)) + ↑(W' (a t)) - ↑(W' (a t)) =
      fwdMap W' (a t) (φ (invMap W t z)) := by ring
  rw [hcancel]
  push_cast
  field_simp
  ring

end InteractingSLE.ZhanGT4
