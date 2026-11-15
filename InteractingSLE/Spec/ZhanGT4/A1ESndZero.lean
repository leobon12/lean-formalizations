/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESndHLaw
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndZeroId

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the frozen time `σ = 0`

Packet PROVE-A1-EIGHTSND (mirror of PROVE-A1-G3LAW2's `A1G3L2SndZeroId`, `A1G3L2SndZeroLaw`, `A1G3L2SndFinal`). For the
patched Eight marginals, at the frozen time `0` (every frozen sample is live, every gate is open) the frozen hull is
empty, the canonical clock is the identity and the canonical image is the small curve itself:

* `eightSnd_live_zero`; **`eightSmall_geometry`**: the stopped small path has the seeded image geometry with its own
  word `(![0], ![0, −x])`;
* **`eightSnd0_rDrv`**, **`eightSnd0_cap`**, **`eightSnd0_VL`**, **`eightSnd0_VR`**: the canonical driver is `W₁`,
  the raw caps are the exits, the canonical forces are `VL₁ 0`, `VR₁ 0`, `VR₁ 1` (PROVE-A1-G3LAW2's generic
  `imgClk_imgDrv_zero_time`, `exists_ownData_zero_time` and `canon*_eq_of_geometry_*`);
* **`eightSndD_zero`** (density `1`), **`eightSnd0_noise`** (the residual is the small Brownian motion),
  **`eightSnd_isSeedSampleLaw_zero`** (the law in the small marginal's own filtration);
* **`eightSnd_hlaw_zero`**, **`eightSnd_hgeo_zero`**: the masked forms for the original data.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESnd

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1ELaw A1G3L2 A1SeedGeom

section Zero

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
  {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The large curve is live at the frozen time `0`.** -/
theorem eightSnd_live_zero (y₀ : Y) : eightSndLive W₂ VL₂ ζ₂ 0 y₀ := by
  obtain ⟨-, -, hS₂ζ, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  refine ⟨lt_of_le_of_lt (zero_le (a := ((eightS₂ x W₂ ζ₂ 0 y₀ : ℝ≥0) : ℝ≥0∞))) (hS₂ζ 0 y₀), fun r hr => ?_⟩
  have hr0 : r = 0 := le_antisymm hr (zero_le (a := r))
  subst hr0
  have hW0 : W₂ 0 y₀ = 0 := (h₂.path y₀).1
  have hL0 : VL₂ 0 0 y₀ = x := (h₂.path y₀).2.1 0
  show VL₂ 0 0 y₀ < W₂ 0 y₀
  rw [hW0, hL0]
  exact hx

/-- **The stopped small path has the seeded image geometry with its own word.** -/
theorem eightSmall_geometry (k : ℕ) (y₀ : Y) (x₀ : X) :
    SeedImageGeometry (![0] : Fin 1 → ℝ) (![0, -x] : Fin 2 → ℝ) (smallEightRhoL κ) (smallEightRhoR κ)
      (fun t => W₁ (min t (eightS₁ x W₁ ζ₁ k x₀)) x₀) (fun i t => VL₁ i (min t (eightS₁ x W₁ ζ₁ k x₀)) x₀)
      (fun j t => VR₁ j (min t (eightS₁ x W₁ ζ₁ k x₀)) x₀) (eightS₁ x W₁ ζ₁ k x₀) := by
  obtain ⟨hR1, hsep₁, -, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  set S := eightS₁ x W₁ ζ₁ k x₀ with hSdef
  have hSζ : (S : ℝ≥0∞) < ζ₁ x₀ := (hR1 k x₀).1
  obtain ⟨hW0, hL0, hR0, hcw, hcL, hcR, -, hLw, hwR, -, hiL, hiR, -, hLeq, hReq, -⟩ := h₁.path x₀
  have hword : IsSeedWord (![0] : Fin 1 → ℝ) (![0, -x] : Fin 2 → ℝ) (smallEightRhoL κ) (smallEightRhoR κ) := by
    have h := smallEight_isSeedWord (W := (W₂ · y₀)) (VL := fun i t => VL₂ i t y₀) hκ8
      (eightSnd_live_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ y₀)
    have hW0₂ : W₂ 0 y₀ = 0 := (h₂.path y₀).1
    have hL0₂ : VL₂ 0 0 y₀ = x := (h₂.path y₀).2.1 0
    have e1 : W₂ 0 y₀ - VL₂ 0 0 y₀ = -x := by rw [hW0₂, hL0₂]; ring
    simp only [e1] at h
    exact h
  have hmin : ∀ t : ℝ≥0, t ≤ S → min t S = t := fun t ht => min_eq_left ht
  have hlt : ∀ t : ℝ≥0, t ≤ S → (t : ℝ≥0∞) < ζ₁ x₀ := fun t ht =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hSζ
  have hmin' : ∀ t : ℝ≥0, t ≤ S → ∀ s : ℝ, s ∈ uIcc (0 : ℝ) t → min s.toNNReal S = s.toNNReal := fun t ht s hs =>
    min_eq_left ((Real.toNNReal_le_iff_le_coe.2 (by rw [uIcc_of_le t.coe_nonneg] at hs; exact hs.2)).trans ht)
  refine seedImageGeometry_of_isSeedWord hword (by simp only [min_eq_left (zero_le (a := S)), hW0])
    (fun i => by simp only [min_eq_left (zero_le (a := S))]; exact hL0 i)
    (fun j => by simp only [min_eq_left (zero_le (a := S))]; exact hR0 j)
    (continuous_stopped hcw hSζ) (fun i => continuous_stopped (hcL i) hSζ)
    (fun j => continuous_stopped (hcR j) hSζ) (fun t ht i => ?_) (fun t ht j => ?_) (fun t ht i => ?_)
    (fun t ht j => ?_) (fun t hp ht i => ?_) (fun t hp ht j => ?_)
  · refine (hiL t (hlt t ht) i).congr fun s hs => ?_
    have hs' : s ∈ uIcc (0 : ℝ) t := uIoc_subset_uIcc hs
    simp only [hmin' t ht s hs']
  · refine (hiR t (hlt t ht) j).congr fun s hs => ?_
    have hs' : s ∈ uIcc (0 : ℝ) t := uIoc_subset_uIcc hs
    simp only [hmin' t ht s hs']
  · rw [hmin t ht, show VL₁ i t x₀ = (![0] : Fin 1 → ℝ) i +
        ∫ s in (0 : ℝ)..t, 2 / (VL₁ i s.toNNReal x₀ - W₁ s.toNNReal x₀) from hLeq t (hlt t ht) i]
    congr 1
    exact intervalIntegral.integral_congr fun s hs => by simp only [hmin' t ht s hs]
  · rw [hmin t ht, show VR₁ j t x₀ = (![0, -x] : Fin 2 → ℝ) j +
        ∫ s in (0 : ℝ)..t, 2 / (VR₁ j s.toNNReal x₀ - W₁ s.toNNReal x₀) from hReq t (hlt t ht) j]
    congr 1
    exact intervalIntegral.integral_congr fun s hs => by simp only [hmin' t ht s hs]
  · rw [hmin t ht]
    fin_cases i
    exact lt_of_le_of_ne (hLw t (hlt t ht) 0) (hsep₁ x₀ t hp (hlt t ht)).1
  · rw [hmin t ht]
    fin_cases j
    · exact lt_of_le_of_ne (hwR t (hlt t ht) 0) (hsep₁ x₀ t hp (hlt t ht)).2.symm
    · exact lt_of_le_of_ne (hwR t (hlt t ht) 1)
        (smallEight_sepP_of_good hx (h₁.path x₀) (hg₁ x₀) t (hlt t ht)).symm

/-- **The canonical image at the frozen time `0`** (small direction, one pair of samples): the large driver is
continuous a little beyond `0`, the exit is a good horizon, the canonical clock is the identity and the canonical image
driver is the small driver translated by `x`, and an image chain of the stopped small driver has the identity clock and
the small driver itself. -/
theorem eightZero_chain (k : ℕ) (y₀ : Y) (x₀ : X) :
    (∃ τ', ((0 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 τ')) ∧
    A1Ref.IsGoodTime x (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ)
      (eightS₁ x W₁ ζ₁ k x₀) ∧
    (∀ t ∈ Icc (0 : ℝ) (eightS₁ x W₁ ζ₁ k x₀),
      A1Ref.imgClk x (Strip.extPath (W₁ · x₀)) 0 (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ) t = t) ∧
    (∀ t ∈ Icc (0 : ℝ) (eightS₁ x W₁ ζ₁ k x₀),
      A1Ref.imgDrv x (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ) t =
        Strip.extPath (W₁ · x₀) t + x) ∧
    ∃ a W' : ℝ → ℝ, OwnData (eightDrv W₁ (eightS₁ x W₁ ζ₁) k x₀)
      (physHull (0 - x) (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ))
      (physMap (0 - x) (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ)) (eightS₁ x W₁ ζ₁ k x₀) a W' ∧
      (∀ t ∈ Icc (0 : ℝ) (eightS₁ x W₁ ζ₁ k x₀), a t = t) ∧
      ∀ t ∈ Icc (0 : ℝ) (eightS₁ x W₁ ζ₁ k x₀), W' t = Strip.extPath (W₁ · x₀) t := by
  obtain ⟨hR1, -, hS₂ζ, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have h0ζ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ₂ y₀ :=
    lt_of_le_of_lt (zero_le (a := ((eightS₂ x W₂ ζ₂ 0 y₀ : ℝ≥0) : ℝ≥0∞))) (hS₂ζ 0 y₀)
  obtain ⟨τ', hτ', hk⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 h0ζ
  have hτ'0 : (0 : ℝ) < τ' := by simpa using hτ'
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ x₀ → ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT
  have hj0 : Strip.extPath (W₁ · x₀) 0 = 0 := A1Ref.extPath_zero_of (h₁.path x₀).1
  have hk0 : Strip.extPath (W₂ · y₀) 0 = 0 := A1Ref.extPath_zero_of (h₂.path y₀).1
  have hS : (0 : ℝ) < eightS₁ x W₁ ζ₁ k x₀ := (hR1 k x₀).2
  have hSζ : ENNReal.ofReal (eightS₁ x W₁ ζ₁ k x₀) < ζ₁ x₀ := by
    rw [ENNReal.ofReal_coe_nnreal]; exact (hR1 k x₀).1
  have hgood := isGoodTime_zero_time (xj := x) (wj := Strip.extPath (W₁ · x₀)) hτ'0 hk hS hSζ
  obtain ⟨hclk, hdrv⟩ := imgClk_imgDrv_zero_time (xj := x) hj hj0 hτ'0 hk hk0 hS hSζ
  have hWc : Continuous (eightDrv W₁ (eightS₁ x W₁ ζ₁) k x₀) :=
    continuous_eightDrv (h₁.path x₀).2.2.2.1 (hR1 k x₀).1
  obtain ⟨a, W', hown, ha, hW'⟩ := exists_ownData_zero_time (xj := x) hj hj0 hτ'0 hk hk0 hWc
    (eightDrv_zero (h₁.path x₀).1) hS hSζ (eightDrv_eqOn W₁ (eightS₁ x W₁ ζ₁) k x₀)
  simp only [NNReal.coe_zero]
  exact ⟨⟨τ', hτ'0, hk⟩, hgood, hclk, hdrv, a, W', hown, ha, hW'⟩

/-- **At the frozen time `0` the masked canonical image driver is the small driver** up to the exit. -/
theorem eightSnd0_rDrv (k : ℕ) (y₀ : Y) (x₀ : X) {t : ℝ≥0} (ht : t ≤ eightS₁ x W₁ ζ₁ k x₀) :
    rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => 0) t (x₀, y₀) = W₁ t x₀ := by
  obtain ⟨-, -, -, hdrv, -⟩ := eightZero_chain hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hlive := eightSnd_live_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ y₀
  have hj0 : Strip.extPath (W₁ · x₀) 0 = 0 := A1Ref.extPath_zero_of (h₁.path x₀).1
  simp only [rDrv, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive]
  rw [hdrv t ⟨t.coe_nonneg, by exact_mod_cast ht⟩, hdrv 0 ⟨le_rfl, NNReal.coe_nonneg _⟩, hj0]
  simp [Strip.extPath]

/-- **At the frozen time `0` the raw caps are the small exits.** -/
theorem eightSnd0_cap (k' : ℕ) (y₀ : Y) (x₀ : X) :
    eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k' (x₀, y₀) = eightS₁ x W₁ ζ₁ k' x₀ := by
  obtain ⟨hk, hgood, hclk, -, -⟩ := eightZero_chain hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ x₀
  have hlive := eightSnd_live_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ y₀
  have hT : eightSndOwn x W₁ ζ₁ W₂ ζ₂ 0 k' (x₀, y₀) = (eightS₁ x W₁ ζ₁ k' x₀ : ℝ) := by
    simp only [eightSndOwn, zero_le, ↓reduceIte]
  unfold eightSndCap
  rw [capSnd_congr_pt (T' := fun _ => (eightS₁ x W₁ ζ₁ k' x₀ : ℝ)) hT,
    capSnd_eq_of_isGoodTime (T := fun _ => (eightS₁ x W₁ ζ₁ k' x₀ : ℝ)) hlive
      (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT) (h₁.path x₀).1 hk (h₂.path y₀).1 hgood,
    hclk _ ⟨NNReal.coe_nonneg _, le_rfl⟩, Real.toNNReal_coe]

/-- The data of the identification at `σ = 0` for the force lemmas. -/
theorem eightSnd0_force_data (k : ℕ) (y₀ : Y) (x₀ : X) :
    ∃ a W' : ℝ → ℝ, OwnData (eightDrv W₁ (eightS₁ x W₁ ζ₁) k x₀)
      (physHull (0 - x) (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ))
      (physMap (0 - x) (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ)) (eightS₁ x W₁ ζ₁ k x₀) a W' ∧
      ((eightS₁ x W₁ ζ₁ k x₀ : ℝ≥0) : ℝ) ≤ a (eightS₁ x W₁ ζ₁ k x₀) ∧ W' 0 = 0 ∧
      ∀ s : ℝ≥0, s ≤ eightS₁ x W₁ ζ₁ k x₀ → W₁ (min s (eightS₁ x W₁ ζ₁ k x₀)) x₀ = W' s - W' 0 := by
  obtain ⟨-, -, -, -, a, W', hown, ha, hW'⟩ := eightZero_chain hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hS0 : (0 : ℝ) ≤ eightS₁ x W₁ ζ₁ k x₀ := NNReal.coe_nonneg _
  have hW'0 : W' 0 = 0 := by rw [hW' 0 ⟨le_rfl, hS0⟩]; exact A1Ref.extPath_zero_of (h₁.path x₀).1
  refine ⟨a, W', hown, (ha _ ⟨hS0, le_rfl⟩).symm.le, hW'0, fun s hs => ?_⟩
  rw [min_eq_left hs, hW'0, sub_zero, hW' s ⟨s.coe_nonneg, by exact_mod_cast hs⟩]
  simp [Strip.extPath]

/-- **At the frozen time `0` the canonical left seed force is the small curve's left seed** up to the exit. -/
theorem eightSnd0_VL (k : ℕ) (y₀ : Y) (x₀ : X) (i : Fin 1) {t : ℝ≥0} (ht : t ≤ eightS₁ x W₁ ζ₁ k x₀) :
    eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x₀, y₀) = VL₁ i t x₀ := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  by_cases ht0 : t = 0
  · subst ht0
    rw [eightSndVL_zero]
    obtain ⟨-, hL0, -⟩ := h₁.path x₀
    exact (hL0 0).symm
  obtain ⟨hk, hgood, -, -, -⟩ := eightZero_chain hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  obtain ⟨a, W', hown, hTa, -, hw⟩ := eightSnd0_force_data hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hlive := eightSnd_live_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ y₀
  have hgeo := eightSmall_geometry hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  rw [eightSndVL_of_ne x W₁ ζ₁ W₂ VL₂ ζ₂ 0 0 ht0]
  refine (canonSeed_eq_of_geometry_left
    (L := {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => (0 : ℝ≥0)) z.2) z.2})
    (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => (0 : ℝ≥0))
    (ω := (x₀, y₀)) (xj := x) (xk := 0) hown (eightDrv_eqOn W₁ (eightS₁ x W₁ ζ₁) k x₀)
    (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT) (A1Ref.extPath_zero_of (h₁.path x₀).1) hk
    (A1Ref.extPath_zero_of (h₂.path y₀).1) hgood hgeo hTa hw hlive 0 rfl ht).trans ?_
  simp only [min_eq_left ht]

/-- **At the frozen time `0` the canonical right forces are the small curve's right marks** up to the exit. -/
theorem eightSnd0_VR (k : ℕ) (y₀ : Y) (x₀ : X) (j : Fin 2) {t : ℝ≥0} (ht : t ≤ eightS₁ x W₁ ζ₁ k x₀) :
    eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ 0 j t (x₀, y₀) = VR₁ j t x₀ := by
  have hW0' : W₂ 0 y₀ = 0 := (h₂.path y₀).1
  have hx0 : VL₂ 0 0 y₀ = x := (h₂.path y₀).2.1 0
  by_cases ht0 : t = 0
  · subst ht0
    rw [eightSndVR_zero]
    obtain ⟨-, -, hR0, -⟩ := h₁.path x₀
    rw [show VR₁ j 0 x₀ = (![0, -x] : Fin 2 → ℝ) j from hR0 j]
    fin_cases j <;> simp [eightSndWordR, hW0', hx0]
  obtain ⟨hk, hgood, -, -, -⟩ := eightZero_chain hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  obtain ⟨a, W', hown, hTa, hW'0, hw⟩ := eightSnd0_force_data hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hlive := eightSnd_live_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ y₀
  have hgeo := eightSmall_geometry hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hj := fun T (hT : ENNReal.ofReal T < ζ₁ x₀) => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT
  have hj0 : Strip.extPath (W₁ · x₀) 0 = 0 := A1Ref.extPath_zero_of (h₁.path x₀).1
  have hk0 : Strip.extPath (W₂ · y₀) 0 = 0 := A1Ref.extPath_zero_of (h₂.path y₀).1
  have hWj := eightDrv_eqOn W₁ (eightS₁ x W₁ ζ₁) k x₀
  rw [eightSndVR_of_ne x W₁ ζ₁ W₂ VL₂ ζ₂ 0 j ht0]
  fin_cases j
  · refine (canonSeed_eq_of_geometry_right
      (L := {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => (0 : ℝ≥0)) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => (0 : ℝ≥0))
      (ω := (x₀, y₀)) (xj := x) (xk := 0) hown hWj hj hj0 hk hk0 hgood hgeo hTa hw hlive 0 rfl ht).trans ?_
    simp only [min_eq_left ht]
    rfl
  · refine (canonForce_eq_of_geometry_right
      (L := {z : X × Y | eightSndLive W₂ VL₂ ζ₂ ((fun _ => (0 : ℝ≥0)) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => (0 : ℝ≥0))
      (ω := (x₀, y₀)) (xj := x) (xk := 0) hown hWj hj hj0 hk hk0 hgood hgeo hTa hw hlive
      (p := fun z => W₂ 0 z.2) 1 (show (-x : ℝ) ≠ 0 from neg_ne_zero.2 hx.ne) ?_ ht).trans ?_
    · show W₂ 0 y₀ = -x + W' 0 + x
      rw [hW0', hW'0]
      ring
    · simp only [min_eq_left ht]
      rfl

/-- **At the frozen time `0` the family density is `1`.** -/
theorem eightSndD_zero (k : ℕ) (y₀ : Y) (x₀ : X) :
    eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x₀, y₀) = 1 := by
  obtain ⟨hR1, -, -, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have hc₂ : ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 0) := by
    rw [Icc_self]; exact continuousOn_singleton _ _
  have h0₂ : W₂ 0 y₀ = 0 := (h₂.path y₀).1
  have hWf := continuous_frzPath (W₂ := W₂) (p := -x) hc₂ le_rfl
  have hex : ∃ a W', OwnData (eightDrv W₁ (eightS₁ x W₁ ζ₁) k x₀) (fwdHull (frzPath W₂ (-x) 0 y₀) 0)
      (frzChart (frzPath W₂ (-x) 0 y₀) 0) (eightS₁ x W₁ ζ₁ k x₀) a W' := by
    refine exists_ownData (continuous_eightDrv (h₁.path x₀).2.2.2.1 (hR1 k x₀).1) (eightDrv_zero (h₁.path x₀).1)
      (hR1 k x₀).2 (isHPHull_fwdHull hWf le_rfl) (isMapOut_fwdMap_gen hWf le_rfl) ?_
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty hWf, closure_empty]
    exact empty_disjoint _
  have hn := normEll_eightRec_zero (κ := κ) (VL₁ := VL₁) (VR₁ := VR₁) hc₂ h0₂ hex (NNReal.coe_nonneg _) le_rfl
  simp only [eightSndD, seedHeightField, min_eq_left (zero_le (a := eightS₂ x W₂ ζ₂ k y₀)), NNReal.coe_zero, hn,
    sub_self, Real.exp_zero, ENNReal.ofReal_one]

/-- **At the frozen time `0` the compensated residual of the canonical data is the small Brownian motion** up to the
exit. -/
theorem eightSnd0_noise (k : ℕ) (y₀ : Y) (x₀ : X) {t : ℝ≥0} (ht : t ≤ eightS₁ x W₁ ζ₁ k x₀) :
    seedCapacityNoise (kh κ) (smallEightRhoL κ) (smallEightRhoR κ)
      (fun s => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => 0) s (x₀, y₀))
      (fun i s => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x₀, y₀))
      (fun j s => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s (x₀, y₀)) t = B₁ t x₀ := by
  obtain ⟨hR1, -, -, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have htζ : (t : ℝ≥0∞) < ζ₁ x₀ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) (hR1 k x₀).1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, -⟩ := h₁.path x₀
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  have hs : ∀ s ∈ uIcc (0 : ℝ) t, s.toNNReal ≤ eightS₁ x W₁ ζ₁ k x₀ := fun s hs =>
    (Real.toNNReal_le_iff_le_coe.2 (by rw [uIcc_of_le t.coe_nonneg] at hs; exact hs.2)).trans ht
  have eL : ∀ i, (∫ s in (0 : ℝ)..t, smallEightRhoL κ i / (rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => 0)
      s.toNNReal (x₀, y₀) - eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s.toNNReal (x₀, y₀))) =
      ∫ s in (0 : ℝ)..t, smallEightRhoL κ i / (W₁ s.toNNReal x₀ - VL₁ i s.toNNReal x₀) := fun i =>
    intervalIntegral.integral_congr fun s hs' => by
      simp only [eightSnd0_rDrv hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ (hs s hs'),
        eightSnd0_VL hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ i (hs s hs')]
  have eR : ∀ j, (∫ s in (0 : ℝ)..t, smallEightRhoR κ j / (rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => 0)
      s.toNNReal (x₀, y₀) - eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s.toNNReal (x₀, y₀))) =
      ∫ s in (0 : ℝ)..t, smallEightRhoR κ j / (W₁ s.toNNReal x₀ - VR₁ j s.toNNReal x₀) := fun j =>
    intervalIntegral.integral_congr fun s hs' => by
      simp only [eightSnd0_rDrv hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ (hs s hs'),
        eightSnd0_VR hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ j (hs s hs')]
  have hw := hweq t htζ
  simp only at hw
  unfold seedCapacityNoise
  beta_reduce
  rw [eightSnd0_rDrv hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ ht]
  simp only [eL, eR]
  rw [hw]
  have hsq : Real.sqrt (kh κ) ≠ 0 := (Real.sqrt_pos.2 hk).ne'
  field_simp
  ring

/-- **The one-sample law of the small direction at the frozen time `0`** (patched data, raw caps): in the small
marginal's own filtration with its own Brownian motion (the density is `1`, the canonical data are the small curve's,
the residual is the Brownian motion). -/
theorem eightSnd_isSeedSampleLaw_zero [𝓖₁.IsRightContinuous] (k : ℕ) (y₀ : Y) :
    IsSeedSampleLaw (P₁.withDensity fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x', y₀))
      (fun t x' => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => 0) t (x', y₀))
      (fun x' => rLife (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => 0) (x', y₀))
      (fun i t x' => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x', y₀))
      (fun j t x' => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ 0 j t (x', y₀))
      (fun t x' => seedCapacityNoise (kh κ) (smallEightRhoL κ) (smallEightRhoR κ)
        (fun s => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => 0) s (x', y₀))
        (fun i s => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x', y₀))
        (fun j s => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s (x', y₀)) t)
      (fun k' x' => eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k' (x', y₀)) k := by
  have hD : (fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x', y₀)) = fun _ => 1 :=
    funext fun x' => eightSndD_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x'
  rw [hD, show (fun _ : X => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]
  have hcap : ∀ k' x', eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k' (x', y₀) = eightS₁ x W₁ ζ₁ k' x' :=
    fun k' x' => eightSnd0_cap hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ x'
  have hx₂ : 0 < -x := by linarith
  have hne : (goodIdx (-x) (![] : Fin 0 → ℝ)).Nonempty :=
    goodIdx_nonempty hx₂ (fun m => m.elim0) (fun m => m.elim0)
  have hF := isEnclFamily_cof hne
  have hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun x' => (eightS₁ x W₁ ζ₁ m x' : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (fun m => (goodSeq (-x) (![] : Fin 0 → ℝ) m).cap) m
  set C : ℝ≥0 → Set X := fun s => {x' | s < eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x', y₀)} with hCdef
  have hCe : ∀ s, C s = {x' | (eightS₁ x W₁ ζ₁ k x' : WithTop ℝ≥0) ≤ s}ᶜ := fun s => by
    ext x'
    simp only [hCdef, mem_ofPred_eq, mem_compl_iff, hcap, WithTop.coe_le_coe, not_le]
  have hC : ∀ s : ℝ≥0, MeasurableSet[𝓖₁ s] (C s) := fun s => by
    rw [hCe s]; exact ((hs₁ k).measurableSet_le s).compl
  have hCS : ∀ s x', x' ∈ C s → s < eightS₁ x W₁ ζ₁ k x' := fun s x' hx' => by
    have h := hx'; simp only [hCdef, mem_ofPred_eq, hcap] at h; exact h
  have key : ∀ s (g g' : Set X), MeasurableSet[𝓖₁ s] g' → (∀ x' ∈ C s, (x' ∈ g ↔ x' ∈ g')) →
      MeasurableSet[𝓖₁ s] (g ∩ C s) := fun s g g' hg' hgg => by
    have e : g ∩ C s = g' ∩ C s := by
      ext x'
      exact ⟨fun h => ⟨(hgg x' h.2).1 h.1, h.2⟩, fun h => ⟨(hgg x' h.2).2 h.1, h.2⟩⟩
    rw [e]; exact hg'.inter (hC s)
  have hB := h₁.evol.1
  refine ⟨𝓖₁, B₁, hB, hB₁, hC, fun s => ?_, Eventually.of_forall fun x' t ht => ?_⟩
  · refine forall_imageGen (p := fun g => MeasurableSet[𝓖₁ s] (g ∩ C s))
      (fun r hr U hU => key s _ (W₁ r ⁻¹' U) (𝓖₁.mono hr _ ((h₁.progW.stronglyAdapted r).measurable hU))
        fun x' hx' => ?_)
      (fun r hr U hU i => key s _ (VL₁ i r ⁻¹' U) (𝓖₁.mono hr _ (((h₁.progVL i).stronglyAdapted r).measurable hU))
        fun x' hx' => ?_)
      (fun r hr U hU j => key s _ (VR₁ j r ⁻¹' U) (𝓖₁.mono hr _ (((h₁.progVR j).stronglyAdapted r).measurable hU))
        fun x' hx' => ?_)
      (fun r hr U hU => key s _ (B₁ r ⁻¹' U) (𝓖₁.mono hr _ ((hB.2.1 r) hU)) fun x' hx' => ?_)
      (fun r hr k' => key s _ {x' | (eightS₁ x W₁ ζ₁ k' x' : WithTop ℝ≥0) ≤ r}
        (𝓖₁.mono hr _ ((hs₁ k').measurableSet_le r)) fun x' _ => ?_)
      (fun r hr => key s _ univ MeasurableSet.univ fun x' hx' => ?_)
    · have hrS : r ≤ eightS₁ x W₁ ζ₁ k x' := hr.trans (hCS s x' hx').le
      simp only [mem_preimage, eightSnd0_rDrv hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' hrS]
    · have hrS : r ≤ eightS₁ x W₁ ζ₁ k x' := hr.trans (hCS s x' hx').le
      simp only [mem_preimage, eightSnd0_VL hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' i hrS]
    · have hrS : r ≤ eightS₁ x W₁ ζ₁ k x' := hr.trans (hCS s x' hx').le
      simp only [mem_preimage, eightSnd0_VR hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' j hrS]
    · have hrS : r ≤ eightS₁ x W₁ ζ₁ k x' := hr.trans (hCS s x' hx').le
      simp only [mem_preimage, eightSnd0_noise hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' hrS]
    · simp only [mem_ofPred_eq, hcap, WithTop.coe_le_coe]
    · simp only [mem_univ, iff_true, mem_ofPred_eq]
      have h1 := capSnd_le_rLife (live := eightSndLive W₂ VL₂ ζ₂) (xj := x) (Wj := W₁) (ζj := ζ₁) (xk := 0)
        (Wk := W₂) (τ := fun _ => 0) (eightSndOwn x W₁ ζ₁ W₂ ζ₂ 0 k) (x', y₀)
      have h2 : (r : ℝ≥0∞) < eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k (x', y₀) := by
        have := hx'
        simp only [hCdef, mem_ofPred_eq] at this
        exact ENNReal.coe_lt_coe.2 (hr.trans_lt this)
      exact h2.trans_le h1
  · have ht' : t ≤ eightS₁ x W₁ ζ₁ k x' := by rw [← hcap k x']; exact ht
    exact (eightSnd0_noise hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x' ht').symm

end Zero

/-! ### The masked forms for the original data -/

section ZeroMask

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ}
  {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
  {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂

/-- **The small direction's one-sample law at the frozen time `0`, masked caps** (original canonical data). -/
theorem eightSnd_hlaw_zero [𝓖₁.IsRightContinuous] (hG₁ : MeasurableSet G₁) (hG₁0 : P₁ G₁ᶜ = 0) (k : ℕ) {y' : Y}
    (hy' : y' ∈ G₂) :
    IsSeedSampleLaw (P₁.withDensity fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x', y'))
      (fun t x' => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => 0) t (x', y'))
      (fun x' => rLife (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => 0) (x', y'))
      (fun i t x' => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o 0 i t (x', y'))
      (fun j t x' => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o 0 j t (x', y'))
      (fun t x' => seedCapacityNoise (kh κ) (smallEightRhoL κ) (smallEightRhoR κ)
        (fun s => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => 0) s (x', y'))
        (fun i s => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o 0 i s (x', y'))
        (fun j s => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o 0 j s (x', y')) t)
      (fun k' x' => maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂) 0 k' (x', y')) k := by
  have hE0 : (P₁.withDensity fun x' => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ 0 k (x', y')) G₁ᶜ = 0 :=
    withDensity_absolutelyContinuous _ _ hG₁0
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ y' hy'
  have hlaw := eightSnd_isSeedSampleLaw_zero hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y'
  have hcg := fun x' (hx : x' ∉ G₁ᶜ) =>
    eightSnd_data_congr (x := x) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
      (hag₁ x' (not_not.1 hx)).1 (hag₁ x' (not_not.1 hx)).2 hW₂a hV₂a hζ₂a 0
  refine IsSeedSampleLaw.congr_off hlaw hG₁.compl hE0
    (fun x' hx => maskCap_of_not_mem (z := (x', y')) fun h => hx h.1)
    (fun x' hx t => (hcg x' hx).1 t) (fun x' hx => (hcg x' hx).2.1) (fun x' hx i t => (hcg x' hx).2.2.1 i t)
    (fun x' hx j t => (hcg x' hx).2.2.2.1 j t) (fun x' hx t => ?_)
    (fun x' hx k' => (maskCap_of_mem (z := (x', y')) (not_not.1 hx) hy').trans ((hcg x' hx).2.2.2.2 k'))
  have e1 : (fun s => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => 0) s (x', y')) =
      fun s => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => 0) s (x', y') :=
    funext fun s => (hcg x' hx).1 s
  have e2 : (fun i s => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o 0 i s (x', y')) =
      fun i s => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ 0 i s (x', y') :=
    funext fun i => funext fun s => (hcg x' hx).2.2.1 i s
  have e3 : (fun j s => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o 0 j s (x', y')) =
      fun j s => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ 0 j s (x', y') :=
    funext fun j => funext fun s => (hcg x' hx).2.2.2.1 j s
  simp only [e1, e2, e3]

/-- **The geometry of the canonical data stopped at a positive raw cap at the frozen time `0`** (good samples). -/
theorem eightSnd_hgeo_zero (k : ℕ) {z : X × Y} (hz1 : z.1 ∈ G₁) (hz2 : z.2 ∈ G₂)
    (hpos : 0 < eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z) :
    SeedImageGeometry (![0] : Fin 1 → ℝ) (eightSndWordR W₂o VL₂o 0 z.2) (smallEightRhoL κ) (smallEightRhoR κ)
      (fun t => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => 0)
        (min t (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z)) z)
      (fun i t => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o 0 i
        (min t (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z)) z)
      (fun j t => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o 0 j
        (min t (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z)) z)
      (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k z) := by
  rcases z with ⟨x₀, y₀⟩
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ y₀ hz2
  have hcg := eightSnd_data_congr (x := x) (W₁g := W₁) (ζ₁g := ζ₁) (W₂g := W₂) (ζ₂g := ζ₂)
    (hag₁ x₀ hz1).1 (hag₁ x₀ hz1).2 hW₂a hV₂a hζ₂a 0
  have hcap : eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂ 0 k (x₀, y₀) = eightS₁ x W₁ ζ₁ k x₀ :=
    (hcg.2.2.2.2 k).trans (eightSnd0_cap hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀)
  have hword : eightSndWordR W₂o VL₂o 0 y₀ = (![0, -x] : Fin 2 → ℝ) := by
    have hw : W₂ 0 y₀ = 0 := (h₂.path y₀).1
    have h0 : VL₂ 0 0 y₀ = x := (h₂.path y₀).2.1 0
    funext j
    fin_cases j <;> simp [eightSndWordR, hW₂a, hV₂a, h0, hw]
  rw [hcap, hword]
  have hG := eightSmall_geometry hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  refine hG.stop_of_eqOn
    (w' := fun t => rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o (fun _ => 0) t (x₀, y₀))
    (vL' := fun i t => eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o 0 i t (x₀, y₀))
    (vR' := fun j t => eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o 0 j t (x₀, y₀)) (fun t ht => ?_) (fun i t ht => ?_)
    (fun j t ht => ?_)
  · rw [hcg.1 t, eightSnd0_rDrv hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ ht, min_eq_left ht]
  · rw [hcg.2.2.1 i t, eightSnd0_VL hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ i ht, min_eq_left ht]
  · rw [hcg.2.2.2.1 j t, eightSnd0_VR hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀ j ht, min_eq_left ht]

end ZeroMask

end InteractingSLE.ZhanGT4.A1ESnd
