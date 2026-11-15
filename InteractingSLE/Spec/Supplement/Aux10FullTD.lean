/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux10FullReflect
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# Aux. lemma 10: the comparison map and its logarithm, (TD1)–(TD2)

Packet PROVE-T14-BR9. Specification Aux. lemma 10 (pp. 69–71), (TD1)–(TD2), at one time `t`, for ℝ-indexed drivers
(`exists_TD`). Data: the old chain `W` at time `t` (hull `K_t`, centred map `f_t`), the image chain `W'` at time `s`
with `K̃_s = φ(K_t)`, and a comparison function `F` with `g̃_s ∘ φ = F ∘ g_t` on `D \ K_t` and `F → W'_s` at `W_t`
(`exists_loewner_conformal`). The comparison map is `R = f̃_s ∘ φ ∘ f_t⁻¹` on `Ω = f_t(D \ K_t)`, with the chain-rule
logarithm `L = log f̃_s' ∘ φ ∘ f_t⁻¹ + L_φ ∘ f_t⁻¹ − log f_t' ∘ f_t⁻¹`.

* The interval `(y_a, y_b) = (f_t(x_a), f_t(x_b))` of two alive real points `x_a < 0 < x_b` contains `0` and the hull
  interval (`Aux10.exists_eq_of_le`/`_ge`: a real point outside it is the image of an alive real point, where `f_t⁻¹`
  tends to that point and not to the hull).
* `R` reflects across a thin rectangle around `[y_a, y_b]` (`exists_reflect`, with the localization `exists_local` and
  a pole `π = f_t(x_π)`, `x_π < x_a`), with `R' > 0` on the real axis (`deriv_pos_of_reflect`), so `Log R'` is a
  logarithm real on the axis (`exists_log_deriv`).
* `L` and `Log R'` differ by `2πin` on the upper half of the rectangle (`IsDerivLog.exists_int_eqOn`); `n = 0` because
  near `y_a = f_t(x_a)` all three terms of `L` have vanishing imaginary part
  (`Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real` at the alive points `x_a` and `φ(x_a)`, and `Im L_φ = 0` on
  the real interval).
* `R(0) = 0` from `F → W'_s`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate
open QuantumZipper (H IsForwardSol)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE

namespace Aux10

open ConformalImage

variable {W : ℝ → ℝ}

/-- `f_t` maps `ℍ \ K_t` conformally onto `ℍ`. -/
theorem isConformalBijection_fwdMap (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsConformalBijection (QuantumZipper.fwdMap W t) (H \ QuantumZipper.fwdHull W t) H :=
  ⟨QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht, QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht,
    QuantumZipper.FwdHolo.injOn_fwdMap hW ht, fun _ hw =>
      ⟨_, QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hw,
        QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht hw⟩⟩

/-- The derivative lift of `f_t⁻¹` on `ℍ`: `−log f_t' ∘ f_t⁻¹`. -/
theorem isDerivLog_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsDerivLog (QuantumZipper.fwdMapInv W t)
      (fun w => -QuantumZipper.logDerivFwd W t (QuantumZipper.fwdMapInv W t w)) H := by
  set U := H \ QuantumZipper.fwdHull W t with hU
  have hUo : IsOpen U := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht
  have hc := isConformalBijection_fwdMap hW hW0 ht
  have h := (isDerivLog_fwdMap hW ht).invFunOn hUo hc
  have heq : EqOn (Function.invFunOn (QuantumZipper.fwdMap W t) U) (QuantumZipper.fwdMapInv W t) H := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hc.2.surjOn hw
    rw [hc.2.injOn.leftInvOn_invFunOn hz, QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hz]
  refine ⟨?_, fun w hw => ?_⟩
  · refine h.1.congr fun w hw => ?_
    simp only [heq hw]
  · have hev : Function.invFunOn (QuantumZipper.fwdMap W t) U =ᶠ[𝓝 w] QuantumZipper.fwdMapInv W t :=
      Filter.eventuallyEq_of_mem (QuantumZipper.isOpen_H.mem_nhds hw) heq
    rw [← hev.deriv_eq, ← h.2 w hw]
    simp only [heq hw]

section Comparison

variable {Wr W' : ℝ → ℝ} {t s : ℝ} {D : Set ℂ} {φ Lφ : ℂ → ℂ}

/-- The domain `Ω = f_t(D \ K_t)` of the comparison map. -/
abbrev cmpDom (Wr : ℝ → ℝ) (t : ℝ) (D : Set ℂ) : Set ℂ :=
  QuantumZipper.fwdMap Wr t '' (D \ QuantumZipper.fwdHull Wr t)

/-- The comparison map `R = f̃_s ∘ φ ∘ f_t⁻¹`. -/
abbrev cmpMap (Wr W' : ℝ → ℝ) (t s : ℝ) (φ : ℂ → ℂ) (w : ℂ) : ℂ :=
  QuantumZipper.fwdMap W' s (φ (QuantumZipper.fwdMapInv Wr t w))

/-- The chain-rule logarithm `L = log f̃_s' ∘ φ ∘ f_t⁻¹ + L_φ ∘ f_t⁻¹ − log f_t' ∘ f_t⁻¹`. -/
abbrev cmpLog (Wr W' : ℝ → ℝ) (t s : ℝ) (φ Lφ : ℂ → ℂ) (w : ℂ) : ℂ :=
  QuantumZipper.logDerivFwd W' s (φ (QuantumZipper.fwdMapInv Wr t w)) +
    Lφ (QuantumZipper.fwdMapInv Wr t w) - QuantumZipper.logDerivFwd Wr t (QuantumZipper.fwdMapInv Wr t w)

theorem isOpen_sdiff_fwdHull (hWr : Continuous Wr) (ht : 0 ≤ t) (hDo : IsOpen D) (hDH : D ⊆ H) :
    IsOpen (D \ QuantumZipper.fwdHull Wr t) := by
  have : D \ QuantumZipper.fwdHull Wr t = D ∩ (H \ QuantumZipper.fwdHull Wr t) := by
    ext z; constructor
    · rintro ⟨hz, hK⟩; exact ⟨hz, hDH hz, hK⟩
    · rintro ⟨hz, -, hK⟩; exact ⟨hz, hK⟩
  rw [this]
  exact hDo.inter (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr ht)

/-- **Properties of the comparison map**: `Ω` is open in `ℍ`, `R` maps it conformally onto `ℍ`, and `L` is a
derivative lift of `R` on `Ω`. -/
theorem comparison_props (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hDo : IsOpen D) (hDH : D ⊆ H) (hφd : DifferentiableOn ℂ φ D)
    (hφinj : InjOn φ D) (hφim : φ '' D = H) (hLφ : IsDerivLog φ Lφ D)
    (hKD : QuantumZipper.fwdHull Wr t ⊆ D)
    (hK : QuantumZipper.fwdHull W' s = φ '' QuantumZipper.fwdHull Wr t) :
    IsOpen (cmpDom Wr t D) ∧ cmpDom Wr t D ⊆ H ∧
      (∀ w ∈ H, QuantumZipper.fwdMapInv Wr t w ∈ D → w ∈ cmpDom Wr t D) ∧
      (∀ w ∈ cmpDom Wr t D, QuantumZipper.fwdMapInv Wr t w ∈ D \ QuantumZipper.fwdHull Wr t) ∧
      IsDerivLog (cmpMap Wr W' t s φ) (cmpLog Wr W' t s φ Lφ) (cmpDom Wr t D) ∧
      InjOn (cmpMap Wr W' t s φ) (cmpDom Wr t D) ∧ MapsTo (cmpMap Wr W' t s φ) (cmpDom Wr t D) H ∧
      cmpMap Wr W' t s φ '' cmpDom Wr t D = H ∧ DifferentiableOn ℂ (cmpMap Wr W' t s φ) (cmpDom Wr t D) ∧
      MapsTo φ (D \ QuantumZipper.fwdHull Wr t) (H \ QuantumZipper.fwdHull W' s) := by
  set K := QuantumZipper.fwdHull Wr t with hKdef
  set K' := QuantumZipper.fwdHull W' s with hK'def
  have hDKo := isOpen_sdiff_fwdHull hWr ht hDo hDH
  have hfinv : ∀ w ∈ cmpDom Wr t D, QuantumZipper.fwdMapInv Wr t w ∈ D \ K := by
    rintro _ ⟨z, hz, rfl⟩
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hWr hWr0 ht ⟨hDH hz.1, hz.2⟩]
    exact hz
  have hΩH : cmpDom Wr t D ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWr ht ⟨hDH hz.1, hz.2⟩
  have hmem : ∀ w ∈ H, QuantumZipper.fwdMapInv Wr t w ∈ D → w ∈ cmpDom Wr t D := fun w hw hD =>
    ⟨_, ⟨hD, (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 ht hw).2⟩,
      QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 ht hw⟩
  have hΩo : IsOpen (cmpDom Wr t D) :=
    QuantumZipper.CA.isOpen_image_of_injOn (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hWr ht)
      (QuantumZipper.FwdHolo.differentiableOn_fwdMap hWr ht) (QuantumZipper.FwdHolo.injOn_fwdMap hWr ht) hDKo
      (fun z hz => ⟨hDH hz.1, hz.2⟩)
  have hφK : MapsTo φ (D \ K) (H \ K') := by
    intro z hz
    refine ⟨hφim ▸ mem_image_of_mem φ hz.1, fun h => ?_⟩
    rw [hK] at h
    obtain ⟨k, hk, hkz⟩ := h
    exact hz.2 (hφinj (hKD hk) hz.1 hkz ▸ hk)
  have h1 := isDerivLog_fwdMap hW' hs
  have hφd' : DifferentiableOn ℂ φ (D \ K) := hφd.mono sdiff_subset
  have h2 := h1.comp hDKo (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW' hs)
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW' hs) hφd' hφK (hLφ.mono sdiff_subset)
  have h3 := (isDerivLog_fwdMapInv hWr hWr0 ht).mono hΩH
  have hfd : DifferentiableOn ℂ (QuantumZipper.fwdMapInv Wr t) (cmpDom Wr t D) :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hWr hWr0 ht).mono hΩH
  have h2d : DifferentiableOn ℂ (QuantumZipper.fwdMap W' s ∘ φ) (D \ K) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW' hs).comp hφd' hφK
  have h4 := h2.comp hΩo hDKo h2d hfd hfinv h3
  refine ⟨hΩo, hΩH, hmem, hfinv, ⟨h4.1.congr fun w hw => ?_, fun w hw => ?_⟩, ?_, ?_, ?_, h2d.comp hfd hfinv, hφK⟩
  · simp only [cmpLog]; ring
  · have := h4.2 w hw
    have e : cmpMap Wr W' t s φ = (QuantumZipper.fwdMap W' s ∘ φ) ∘ QuantumZipper.fwdMapInv Wr t := rfl
    rw [e, ← this]
    congr 1
  · intro w₁ hw₁ w₂ hw₂ heq
    have hz₁ := hfinv w₁ hw₁
    have hz₂ := hfinv w₂ hw₂
    have h := QuantumZipper.FwdHolo.injOn_fwdMap hW' hs (hφK hz₁) (hφK hz₂) heq
    have hzz := hφinj hz₁.1 hz₂.1 h
    rw [← QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 ht (hΩH hw₁),
      ← QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 ht (hΩH hw₂), hzz]
  · intro w hw
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hs (hφK (hfinv w hw))
  · refine Subset.antisymm (fun _ ⟨w, hw, hwv⟩ => hwv ▸ QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hs
      (hφK (hfinv w hw))) fun v hv => ?_
    have hu := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW' hW'0 hs hv
    obtain ⟨z, hz, hzu⟩ : QuantumZipper.fwdMapInv W' s v ∈ φ '' D := hφim ▸ hu.1
    have hzK : z ∉ K := fun h => hu.2 (by show _ ∈ K'; rw [hK]; exact ⟨z, h, hzu⟩)
    refine ⟨QuantumZipper.fwdMap Wr t z, ⟨z, ⟨hz, hzK⟩, rfl⟩, ?_⟩
    simp only [cmpMap]
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hWr hWr0 ht ⟨hDH hz, hzK⟩, hzu,
      QuantumZipper.RS.fwdMap_fwdMapInv hW' hW'0 hs hv]

end Comparison

theorem convex_H : Convex ℝ H := convex_halfSpace_gt Complex.imLm.isLinear 0

/-- Near a real point outside `closure K_t`, points of `ℍ` are outside `K_t`. -/
theorem eventually_notMem_fwdHull {K : Set ℂ} {x : ℂ} (hx : x ∉ closure K) : ∀ᶠ z in 𝓝[H] x, z ∈ H \ K := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    ((isOpen_compl_iff.2 isClosed_closure).mem_nhds hx)] with z hzH hz
  exact ⟨hzH, fun h => hz (subset_closure h)⟩

/-- **(TD1)–(TD2) at one time** (ℝ-indexed drivers). -/
theorem exists_TD {Wr W' : ℝ → ℝ} (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hW' : Continuous W')
    (hW'0 : W' 0 = 0) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) {D : Set ℂ} {φ Lφ : ℂ → ℂ} (hDo : IsOpen D)
    (hDH : D ⊆ H) (hφd : DifferentiableOn ℂ φ D) (hφinj : InjOn φ D) (hφim : φ '' D = H)
    (hLφ : IsDerivLog φ Lφ D) (hKD : QuantumZipper.fwdHull Wr t ⊆ D)
    (hK : QuantumZipper.fwdHull W' s = φ '' QuantumZipper.fwdHull Wr t)
    {F : ℂ → ℂ} (hF : ∀ z ∈ D \ QuantumZipper.fwdHull Wr t, gmap W' s (φ z) = F (gmap Wr t z))
    (hFlim : Tendsto F (𝓝[H] (Wr t : ℂ)) (𝓝 (W' s : ℂ)))
    {xπ xa xb : ℝ} (hπa : xπ < xa) (hxa : xa < 0) (hxb : 0 < xb)
    (hleft : ∀ x ≤ xa, (x : ℂ) ∉ closure (QuantumZipper.fwdHull Wr t))
    (hright : ∀ x ≥ xb, (x : ℂ) ∉ closure (QuantumZipper.fwdHull Wr t))
    {S : Set ℂ} (hSo : IsOpen S) (hSK : closure (QuantumZipper.fwdHull Wr t) ⊆ S)
    (hSI : ∀ x ∈ Icc xπ xb, (x : ℂ) ∈ S) (hSD : S ∩ H ⊆ D) {Cφ : ℝ} (hSφ : ∀ z ∈ S ∩ H, ‖φ z‖ ≤ Cφ)
    {xφ : ℝ} (hxφ : ∃ v, IsForwardSol W' xφ s v) (hφxa : Tendsto φ (𝓝[H] (xa : ℂ)) (𝓝 (xφ : ℂ)))
    (hLxa : Tendsto (fun z => (Lφ z).im) (𝓝[H] (xa : ℂ)) (𝓝 0))
    {C : Set ℂ} (hC : ∀ p ∈ C, ∀ x : ℝ, (x ≤ xa ∨ xb ≤ x) → p ≠ x) :
    ∃ (y₁ y₂ : ℝ) (O : Set ℂ) (R L : ℂ → ℂ),
      y₁ < 0 ∧ 0 < y₂ ∧ IsOpen O ∧ (∀ y ∈ Ioo y₁ y₂, (y : ℂ) ∈ O) ∧
      (∀ y : ℝ, (∃ p ∈ C, Tendsto (QuantumZipper.fwdMapInv Wr t) (𝓝[H] (y : ℂ)) (𝓝 p)) → y ∈ Ioo y₁ y₂) ∧
      DifferentiableOn ℂ R (O ∪ cmpDom Wr t D) ∧ DifferentiableOn ℂ L (O ∪ cmpDom Wr t D) ∧
      (∀ w ∈ cmpDom Wr t D, R w = cmpMap Wr W' t s φ w ∧ L w = cmpLog Wr W' t s φ Lφ w) ∧
      (∀ w ∈ O, Complex.exp (L w) = deriv R w) ∧
      R 0 = 0 ∧ ∀ y ∈ Ioo y₁ y₂, (R y).im = 0 ∧ (L y).im = 0 := by
  classical
  set K := QuantumZipper.fwdHull Wr t with hKdef
  obtain ⟨hΩo, hΩH, hmem, hfinv, hIL, hRinj, hRmaps, hRim, hRd, hφK⟩ :=
    comparison_props hWr hWr0 hW' hW'0 ht hs hDo hDH hφd hφinj hφim hLφ hKD hK
  set Ω := cmpDom Wr t D with hΩdef
  set Rf := cmpMap Wr W' t s φ with hRfdef
  set Lf := cmpLog Wr W' t s φ Lφ with hLfdef
  -- the alive points and their images
  obtain ⟨vπ, hvπ⟩ := exists_isForwardSol_of_notMem_closure hWr hWr0 ht (by linarith : xπ ≠ 0)
    (hleft xπ hπa.le)
  obtain ⟨va, hva⟩ := exists_isForwardSol_of_notMem_closure hWr hWr0 ht hxa.ne (hleft xa le_rfl)
  obtain ⟨vb, hvb⟩ := exists_isForwardSol_of_notMem_closure hWr hWr0 ht hxb.ne' (hright xb le_rfl)
  have hvreal : ∀ {x : ℝ} {v : ℝ → ℂ}, IsForwardSol Wr x t v → v t = (((v t).re : ℝ) : ℂ) := fun hv =>
    Complex.ext (by simp) (by simp [im_eq_zero_of_isForwardSol_real hWr hv ⟨ht, le_rfl⟩])
  set yπ := (vπ t).re with hyπ
  set ya := (va t).re with hya
  set yb := (vb t).re with hyb
  have hya0 : ya < 0 := re_neg_of_isForwardSol hWr hWr0 hxa hva t ⟨ht, le_rfl⟩
  have hyb0 : 0 < yb := re_pos_of_isForwardSol hWr hWr0 hxb hvb t ⟨ht, le_rfl⟩
  have hπya : yπ < ya := by
    have := WangWu.re_fwdMap_lt_re_fwdMap hWr hWr0 ht hπa (Or.inr hxa) hvπ hva
    rwa [fwdMap_eq_of_isForwardSol hWr hvπ ⟨ht, le_rfl⟩, fwdMap_eq_of_isForwardSol hWr hva ⟨ht, le_rfl⟩] at this
  have hab : ya ≤ yb := by linarith
  -- localization
  obtain ⟨r₀, hr₀, hloc⟩ := exists_local hWr hWr0 ht (hπa.trans hxa) hxb hvπ hvb hSo hSK hSI
  have hloc' : ∀ w ∈ H, ∀ y ∈ Icc yπ yb, ‖w - y‖ < r₀ →
      w ∈ Ω ∧ QuantumZipper.fwdMapInv Wr t w ∈ S ∩ H := by
    intro w hw y hy hwy
    have hz := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 ht hw
    have hfz := QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 ht hw
    have hzS := hloc _ hz y hy (by rw [hfz]; exact hwy)
    exact ⟨hmem w hw (hSD ⟨hzS, hz.1⟩), hzS, hz.1⟩
  obtain ⟨C', hC'⟩ := exists_norm_fwdMap_sub_le hW' hW'0 hs
  set r := min r₀ ((ya - yπ) / 2) with hrdef
  have hr : 0 < r := lt_min hr₀ (by linarith)
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hr2 : r ≤ (ya - yπ) / 2 := min_le_right _ _
  have hIcc : Icc ya yb ⊆ Icc yπ yb := Icc_subset_Icc_left hπya.le
  obtain ⟨ρ, hρ, G, hrectΩ, hGd, hGR, hGsymm, hGreal⟩ := exists_reflect hΩo hΩH hRd hRinj hRim hab hr
    (fun w hw ⟨y, hy, hwy⟩ => (hloc' w hw y (hIcc hy) (hwy.trans_le hrr₀)).1)
    (C := Cφ + C') (fun w hw ⟨y, hy, hwy⟩ => by
      obtain ⟨-, hzS, hzH⟩ := hloc' w hw y (hIcc hy) (hwy.trans_le hrr₀)
      have hzD : QuantumZipper.fwdMapInv Wr t w ∈ D \ K :=
        ⟨hSD ⟨hzS, hzH⟩, (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hWr hWr0 ht hw).2⟩
      have hu := hφK hzD
      have h1 := hC' _ hu
      have h2 := hSφ _ ⟨hzS, hzH⟩
      show ‖QuantumZipper.fwdMap W' s (φ (QuantumZipper.fwdMapInv Wr t w))‖ ≤ Cφ + C'
      calc ‖QuantumZipper.fwdMap W' s (φ (QuantumZipper.fwdMapInv Wr t w))‖
          = ‖(QuantumZipper.fwdMap W' s (φ (QuantumZipper.fwdMapInv Wr t w)) -
              φ (QuantumZipper.fwdMapInv Wr t w)) + φ (QuantumZipper.fwdMapInv Wr t w)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
        _ ≤ Cφ + C' := by linarith)
    (π := yπ) (by linarith) hr₀ (fun z hz => by
      by_contra h
      push Not at h
      exact hz.2 (hloc' z hz.1 yπ ⟨le_rfl, by linarith⟩ h).1)
  have hGH : ∀ w ∈ rect ya yb ρ ∩ H, G w ∈ H := fun w hw => by
    rw [hGR hw]; exact hRmaps (hrectΩ hw)
  have hGinj : InjOn G (rect ya yb ρ ∩ H) := (hRinj.mono hrectΩ).congr hGR.symm
  have hpos := deriv_pos_of_reflect hGd hGsymm hGreal hGH hGinj
  obtain ⟨ρ', hρ', hρ'ρ, hLOd, hLOexp, hLOreal⟩ := exists_log_deriv hab hρ hGd hpos
  set O := rect ya yb ρ' with hOdef
  set LO : ℂ → ℂ := fun w => Complex.log (deriv G w) with hLOdef
  have hOo : IsOpen O := isOpen_rect _ _ _
  have hOρ : O ⊆ rect ya yb ρ := rect_mono hρ'ρ
  have hrealO : ∀ y ∈ Icc ya yb, (y : ℂ) ∈ O := fun y hy =>
    ⟨by simp; linarith [hy.1], by simp; linarith [hy.2], by simpa using hρ'⟩
  have hGRev : ∀ w ∈ rect ya yb ρ ∩ H, G =ᶠ[𝓝 w] Rf := fun w hw =>
    Filter.eventuallyEq_of_mem (((isOpen_rect _ _ _).inter QuantumZipper.isOpen_H).mem_nhds hw) hGR
  -- the logarithms agree on the upper half of the rectangle
  have hVo : IsOpen (O ∩ H) := hOo.inter QuantumZipper.isOpen_H
  have hVc : IsPreconnected (O ∩ H) := ((convex_rect _ _ _).inter convex_H).isPreconnected
  have hVΩ : O ∩ H ⊆ Ω := fun w hw => hrectΩ ⟨hOρ hw.1, hw.2⟩
  have hI2 : IsDerivLog Rf LO (O ∩ H) := ⟨hLOd.mono inter_subset_left, fun w hw => by
    rw [hLOexp w hw.1]
    exact (hGRev w ⟨hOρ hw.1, hw.2⟩).deriv_eq⟩
  obtain ⟨n, hn⟩ := (hIL.mono hVΩ).exists_int_eqOn hVo hVc hI2
  have hn0 : n = 0 := by
    set l := 𝓝[H] (xa : ℂ) with hl
    have hlne : l.NeBot := Sec5.CrossRestart.MobHyp.nhdsWithin_neBot xa
    have hev1 := eventually_notMem_fwdHull (hleft xa le_rfl)
    have hev3 : ∀ᶠ z in l, z ∈ D := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (hSo.mem_nhds (hSI xa ⟨hπa.le, by linarith⟩))] with z hzH hzS
      exact hSD ⟨hzS, hzH⟩
    have hfz : Tendsto (QuantumZipper.fwdMap Wr t) l (𝓝 (ya : ℂ)) := by
      have := tendsto_fwdMap_of_isForwardSol hWr ht hva
      rwa [hvreal hva] at this
    have hev2 : ∀ᶠ z in l, QuantumZipper.fwdMap Wr t z ∈ O ∩ H := by
      filter_upwards [hfz.eventually (hOo.mem_nhds (hrealO ya ⟨le_rfl, hab⟩)), hev1] with z h1 h2
      exact ⟨h1, QuantumZipper.FwdHolo.mapsTo_fwdMap hWr ht h2⟩
    -- the formula along `f_t(z)`
    have hφH : Tendsto φ l (𝓝[H] (xφ : ℂ)) := tendsto_nhdsWithin_iff.2 ⟨hφxa, by
      filter_upwards [hev3] with z hz
      exact hφim ▸ mem_image_of_mem φ hz⟩
    obtain ⟨vφ, hvφ⟩ := hxφ
    have h1 := (Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real hW' hs hvφ).comp hφH
    have h3 := Sec6.tendsto_im_logDerivFwd_of_isForwardSol_real hWr ht hva
    have hsum : Tendsto (fun z => (Lf (QuantumZipper.fwdMap Wr t z)).im) l (𝓝 0) := by
      have h := (h1.add hLxa).sub h3
      simp only [add_zero, sub_zero] at h
      refine h.congr' ?_
      filter_upwards [hev1] with z hz
      simp only [hLfdef, cmpLog, Function.comp, QuantumZipper.RS.fwdMapInv_fwdMap hWr hWr0 ht hz, sub_im,
        add_im]
    have hLOc : ContinuousAt LO (ya : ℂ) :=
      (hLOd.differentiableAt (hOo.mem_nhds (hrealO ya ⟨le_rfl, hab⟩))).continuousAt
    have hLOt := (continuous_im.tendsto _).comp ((hLOc.tendsto.comp hfz).add_const (2 * Real.pi * I * n))
    have hlim := tendsto_nhds_unique (hsum.congr' (by
      filter_upwards [hev2] with z hz
      simp only [Function.comp]
      rw [hn hz])) hLOt
    have h0 : (LO (ya : ℂ)).im = 0 := hLOreal _ (hrealO ya ⟨le_rfl, hab⟩) (by simp)
    have him : (LO (ya : ℂ) + 2 * Real.pi * I * n).im = 2 * Real.pi * n := by
      simp [h0]
    rw [him] at hlim
    have : (n : ℝ) = 0 := by
      have hπ0 : (0 : ℝ) < 2 * Real.pi := by positivity
      by_contra hne
      have := mul_ne_zero hπ0.ne' hne
      exact this hlim.symm
    exact_mod_cast this
  have hLeq : ∀ w ∈ O ∩ H, Lf w = LO w := fun w hw => by
    rw [hn hw, hn0]; simp
  -- the reflected map and logarithm
  refine ⟨ya, yb, O, fun w => if w ∈ O then G w else Rf w, fun w => if w ∈ O then LO w else Lf w,
    hya0, hyb0, hOo, fun y hy => hrealO y ⟨hy.1.le, hy.2.le⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the hull interval
    rintro y ⟨p, hpC, hp⟩
    have hp' : ∀ x' : ℝ, (∃ v, IsForwardSol Wr x' t v) → QuantumZipper.fwdMap Wr t x' = (y : ℂ) →
        (x' : ℂ) ∉ closure K → p = x' := by
      intro x' ⟨v', hv'⟩ hfx hx'K
      have hlne : (𝓝[H] (x' : ℂ)).NeBot := Sec5.CrossRestart.MobHyp.nhdsWithin_neBot x'
      have hev := eventually_notMem_fwdHull hx'K
      have hf : Tendsto (QuantumZipper.fwdMap Wr t) (𝓝[H] (x' : ℂ)) (𝓝[H] (y : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have := tendsto_fwdMap_of_isForwardSol hWr ht hv'
          rwa [← fwdMap_eq_of_isForwardSol hWr hv' ⟨ht, le_rfl⟩, hfx] at this
        · filter_upwards [hev] with z hz
          exact QuantumZipper.FwdHolo.mapsTo_fwdMap hWr ht hz
      have h1 := hp.comp hf
      have h2 : Tendsto (fun z => z) (𝓝[H] (x' : ℂ)) (𝓝 p) := h1.congr' (by
        filter_upwards [hev] with z hz
        exact QuantumZipper.RS.fwdMapInv_fwdMap hWr hWr0 ht hz)
      exact tendsto_nhds_unique h2 (tendsto_id.mono_left nhdsWithin_le_nhds)
    by_contra hy
    rcases not_and_or.1 hy with hy | hy
    · push Not at hy
      obtain ⟨x', hx', hv', hfx⟩ := exists_eq_of_le hWr hWr0 ht hxa hleft (y := y)
        (by rw [fwdMap_eq_of_isForwardSol hWr hva ⟨ht, le_rfl⟩]; exact hy)
      exact hC p hpC x' (Or.inl hx') (hp' x' hv' hfx (hleft x' hx'))
    · push Not at hy
      obtain ⟨x', hx', hv', hfx⟩ := exists_eq_of_ge hWr hWr0 ht hxb hright (y := y)
        (by rw [fwdMap_eq_of_isForwardSol hWr hvb ⟨ht, le_rfl⟩]; exact hy)
      exact hC p hpC x' (Or.inr hx') (hp' x' hv' hfx (hright x' hx'))
  · intro w hw
    rcases hw with hwO | hwΩ
    · refine (((hGd.differentiableAt ((isOpen_rect _ _ _).mem_nhds (hOρ hwO)))).congr_of_eventuallyEq
        ?_).differentiableWithinAt
      filter_upwards [hOo.mem_nhds hwO] with z hz
      simp [hz]
    · refine ((hRd.differentiableAt (hΩo.mem_nhds hwΩ)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hΩo.mem_nhds hwΩ] with z hz
      by_cases hzO : z ∈ O
      · simp only [hzO, ↓reduceIte]; exact hGR ⟨hOρ hzO, hΩH hz⟩
      · simp [hzO]
  · intro w hw
    rcases hw with hwO | hwΩ
    · refine ((hLOd.differentiableAt (hOo.mem_nhds hwO)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hOo.mem_nhds hwO] with z hz
      simp [hz]
    · refine ((hIL.1.differentiableAt (hΩo.mem_nhds hwΩ)).congr_of_eventuallyEq ?_).differentiableWithinAt
      filter_upwards [hΩo.mem_nhds hwΩ] with z hz
      by_cases hzO : z ∈ O
      · simp only [hzO, ↓reduceIte]; exact (hLeq z ⟨hzO, hΩH hz⟩).symm
      · simp [hzO]
  · intro w hw
    by_cases hwO : w ∈ O
    · simp only [hwO, ↓reduceIte]
      exact ⟨hGR ⟨hOρ hwO, hΩH hw⟩, (hLeq w ⟨hwO, hΩH hw⟩).symm⟩
    · simp [hwO]
  · intro w hw
    simp only [hw, ↓reduceIte]
    rw [hLOexp w hw]
    refine (Filter.EventuallyEq.deriv_eq ?_).symm
    filter_upwards [hOo.mem_nhds hw] with z hz
    simp [hz]
  · have h0O : (0 : ℂ) ∈ O := by exact_mod_cast hrealO 0 ⟨hya0.le, hyb0.le⟩
    simp only [h0O, ↓reduceIte]
    have hlne : (𝓝[H] (0 : ℂ)).NeBot := by simpa using Sec5.CrossRestart.MobHyp.nhdsWithin_neBot 0
    have hGc : Tendsto G (𝓝[H] (0 : ℂ)) (𝓝 (G 0)) :=
      ((hGd.differentiableAt ((isOpen_rect _ _ _).mem_nhds (hOρ h0O))).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds
    have hshift : Tendsto (fun w : ℂ => w + Wr t) (𝓝[H] (0 : ℂ)) (𝓝[H] (Wr t : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun w : ℂ => w + Wr t) (𝓝 0) (𝓝 (0 + Wr t)) :=
          (continuous_id.add continuous_const).tendsto 0
        rw [zero_add] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        have hw' : 0 < w.im := hw
        show 0 < (w + Wr t).im
        simpa using hw'
    have hRlim : Tendsto (fun w => F (w + Wr t) - W' s) (𝓝[H] (0 : ℂ)) (𝓝 0) := by
      have := (hFlim.comp hshift).sub_const (W' s : ℂ)
      simpa using this
    have hev : ∀ᶠ w in 𝓝[H] (0 : ℂ), G w = F (w + Wr t) - W' s := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (hOo.mem_nhds h0O)] with w hwH hwO
      have hwΩ := hVΩ ⟨hwO, hwH⟩
      rw [hGR ⟨hOρ hwO, hwH⟩]
      have hz := hfinv w hwΩ
      have e1 := hF _ hz
      simp only [gmap] at e1
      rw [QuantumZipper.RS.fwdMap_fwdMapInv hWr hWr0 ht (hΩH hwΩ)] at e1
      simp only [hRfdef, cmpMap]
      rw [← e1]
      ring
    exact tendsto_nhds_unique hGc (hRlim.congr' (hev.mono fun w hw => hw.symm))
  · intro y hy
    have hyO : (y : ℂ) ∈ O := hrealO y ⟨hy.1.le, hy.2.le⟩
    simp only [hyO, ↓reduceIte]
    exact ⟨hGreal _ (hOρ hyO) (by simp), hLOreal _ hyO (by simp)⟩

end Aux10

end InteractingSLE
