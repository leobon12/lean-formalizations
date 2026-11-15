/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndZero

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the frozen time `σ = 0`, the G3 identification

Packet PROVE-A1-G3LAW2. For the patched G3 marginals, at the frozen time `0` (every frozen sample is live, every gate is
open) and every pair of samples `(x₀, y₀)`, the canonical data of the small direction are the small curve's own data
up to the rectangle exit `S₁ᵏ(x₀)`:

* `g3Snd_live_zero`: the large curve is live at time `0`;
* **`g3Small_geometry`**: the small path stopped at `S₁ᵏ(x₀)` has the seeded image geometry with its own word
  `(![0], ![0, x − y, −y])`;
* **`g3Snd0_rDrv`**, **`g3Snd0_cap`**, **`g3Snd0_VL`**, **`g3Snd0_VR`**: the canonical driver is `W₁`, the raw caps
  are the exits `S₁^{k'}`, the canonical forces are `VL₁ 0`, `VR₁ 0`, `VR₁ 1`, `VR₁ 2`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

section Zero

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- The rectangle facts of the G3 assembly (`g3_rect` on the cofinal family). -/
theorem g3_rect_facts :
    (∀ m ω, (g3S₁ x y W₁ ζ₁ m ω : ℝ≥0∞) < ζ₁ ω ∧ 0 < (g3S₁ x y W₁ ζ₁ m ω : ℝ)) ∧
    (∀ ω (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ ω → VL₁ 0 s ω ≠ W₁ s ω ∧ VR₁ 0 s ω ≠ W₁ s ω) ∧
    (∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 1 s ω ≠ W₁ s ω) ∧
    (∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 2 s ω ≠ W₁ s ω) ∧
    (∀ m ω, (g3S₂ x y W₂ ζ₂ m ω : ℝ≥0∞) < ζ₂ ω) := by
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  obtain ⟨-, hgood₁, hsep₁, hsepO, hneP, -, -, -, -, hS₂ζ⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ (isEnclFamily_cofG hne)
  exact ⟨fun m ω => ⟨(hgood₁ m ω).1, (hgood₁ m ω).2.1⟩, hsep₁, hsepO, hneP, hS₂ζ⟩

/-- **The large curve is live at the frozen time `0`.** -/
theorem g3Snd_live_zero (y₀ : Y) : g3SndLive W₂ VL₂ ζ₂ 0 y₀ := by
  obtain ⟨-, -, -, -, hS₂ζ⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  refine ⟨lt_of_le_of_lt (zero_le (a := ((g3S₂ x y W₂ ζ₂ 0 y₀ : ℝ≥0) : ℝ≥0∞))) (hS₂ζ 0 y₀), fun r hr => ?_⟩
  have hr0 : r = 0 := le_antisymm hr (zero_le (a := r))
  subst hr0
  obtain ⟨hW0, hL0, -⟩ := h₂.path y₀
  show VL₂ 0 0 y₀ < W₂ 0 y₀
  rw [show W₂ 0 y₀ = 0 from hW0]
  have h := hL0 0
  simp only at h
  rw [h]
  simpa using hx

omit hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ in
theorem continuous_stopped {f : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hf : ContinuousOn f {s | (s : ℝ≥0∞) < ζ}) {S : ℝ≥0}
    (hS : (S : ℝ≥0∞) < ζ) : Continuous fun t : ℝ≥0 => f (min t S) :=
  hf.comp_continuous (continuous_id.min continuous_const) fun _ =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hS

/-- **The stopped small path has the seeded image geometry with its own word.** -/
theorem g3Small_geometry (k : ℕ) (y₀ : Y) (x₀ : X) :
    SeedImageGeometry (![0] : Fin 1 → ℝ) (![0, x - y, -y] : Fin 3 → ℝ) (smallG3RhoL κ) (smallG3RhoR κ)
      (fun t => W₁ (min t (g3S₁ x y W₁ ζ₁ k x₀)) x₀) (fun i t => VL₁ i (min t (g3S₁ x y W₁ ζ₁ k x₀)) x₀)
      (fun j t => VR₁ j (min t (g3S₁ x y W₁ ζ₁ k x₀)) x₀) (g3S₁ x y W₁ ζ₁ k x₀) := by
  obtain ⟨hR1, hsep₁, hsepO, hneP, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  set S := g3S₁ x y W₁ ζ₁ k x₀ with hSdef
  have hSζ : (S : ℝ≥0∞) < ζ₁ x₀ := (hR1 k x₀).1
  obtain ⟨hW0, hL0, hR0, hcw, hcL, hcR, -, hLw, hwR, -, hiL, hiR, -, hLeq, hReq, -⟩ := h₁.path x₀
  have hword : IsSeedWord (![0] : Fin 1 → ℝ) (![0, x - y, -y] : Fin 3 → ℝ) (smallG3RhoL κ) (smallG3RhoR κ) := by
    have h := smallG3_isSeedWord hκ4 hκ8 hyx (h₂.path y₀) (g3Snd_live_zero hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ y₀)
    obtain ⟨hW0₂, hL0₂, -⟩ := h₂.path y₀
    have e : (![0, VL₂ 0 0 y₀ - VL₂ 1 0 y₀, W₂ 0 y₀ - VL₂ 1 0 y₀] : Fin 3 → ℝ) = ![0, x - y, -y] := by
      have h0 := hL0₂ 0
      have h1 := hL0₂ 1
      simp only at h0 h1
      rw [h0, h1, show W₂ 0 y₀ = 0 from hW0₂]
      simp
    rwa [e] at h
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
  · rw [hmin t ht, show VR₁ j t x₀ = (![0, x - y, -y] : Fin 3 → ℝ) j +
        ∫ s in (0 : ℝ)..t, 2 / (VR₁ j s.toNNReal x₀ - W₁ s.toNNReal x₀) from hReq t (hlt t ht) j]
    congr 1
    exact intervalIntegral.integral_congr fun s hs => by simp only [hmin' t ht s hs]
  · rw [hmin t ht]
    fin_cases i
    exact lt_of_le_of_ne (hLw t (hlt t ht) 0) (hsep₁ x₀ t hp (hlt t ht)).1
  · rw [hmin t ht]
    fin_cases j
    · exact lt_of_le_of_ne (hwR t (hlt t ht) 0) (hsep₁ x₀ t hp (hlt t ht)).2.symm
    · exact lt_of_le_of_ne (hwR t (hlt t ht) 1) (hsepO x₀ t (hlt t ht)).symm
    · exact lt_of_le_of_ne (hwR t (hlt t ht) 2) (hneP x₀ t (hlt t ht)).symm

/-- **The canonical image at the frozen time `0`** (small direction, one pair of samples): the large driver is
continuous a little beyond `0`, the exit is a good horizon, the canonical clock is the identity and the canonical image
driver is the small driver translated by `y`, and an image chain of the stopped small driver has the identity clock and
the small driver itself. -/
theorem g3Zero_chain (k : ℕ) (y₀ : Y) (x₀ : X) :
    (∃ τ', ((0 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂ · y₀)) (Icc 0 τ')) ∧
    A1Ref.IsGoodTime y (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ)
      (g3S₁ x y W₁ ζ₁ k x₀) ∧
    (∀ t ∈ Icc (0 : ℝ) (g3S₁ x y W₁ ζ₁ k x₀),
      A1Ref.imgClk y (Strip.extPath (W₁ · x₀)) 0 (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ) t = t) ∧
    (∀ t ∈ Icc (0 : ℝ) (g3S₁ x y W₁ ζ₁ k x₀),
      A1Ref.imgDrv y (Strip.extPath (W₁ · x₀)) (ζ₁ x₀) 0 (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ) t =
        Strip.extPath (W₁ · x₀) t + y) ∧
    ∃ a W' : ℝ → ℝ, OwnData (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀)
      (physHull (0 - y) (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ))
      (physMap (0 - y) (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ)) (g3S₁ x y W₁ ζ₁ k x₀) a W' ∧
      (∀ t ∈ Icc (0 : ℝ) (g3S₁ x y W₁ ζ₁ k x₀), a t = t) ∧
      ∀ t ∈ Icc (0 : ℝ) (g3S₁ x y W₁ ζ₁ k x₀), W' t = Strip.extPath (W₁ · x₀) t := by
  obtain ⟨hR1, -, -, -, hS₂ζ⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have h0ζ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ₂ y₀ :=
    lt_of_le_of_lt (zero_le (a := ((g3S₂ x y W₂ ζ₂ 0 y₀ : ℝ≥0) : ℝ≥0∞))) (hS₂ζ 0 y₀)
  obtain ⟨τ', hτ', hk⟩ := A1Ref.exists_continuousOn_extPath_beyond (h₂.path y₀).2.2.2.1 h0ζ
  have hτ'0 : (0 : ℝ) < τ' := by simpa using hτ'
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ x₀ → ContinuousOn (Strip.extPath (W₁ · x₀)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT
  have hj0 : Strip.extPath (W₁ · x₀) 0 = 0 := A1Ref.extPath_zero_of (h₁.path x₀).1
  have hk0 : Strip.extPath (W₂ · y₀) 0 = 0 := A1Ref.extPath_zero_of (h₂.path y₀).1
  have hS : (0 : ℝ) < g3S₁ x y W₁ ζ₁ k x₀ := (hR1 k x₀).2
  have hSζ : ENNReal.ofReal (g3S₁ x y W₁ ζ₁ k x₀) < ζ₁ x₀ := by
    rw [ENNReal.ofReal_coe_nnreal]; exact (hR1 k x₀).1
  have hgood := isGoodTime_zero_time (xj := y) (wj := Strip.extPath (W₁ · x₀)) hτ'0 hk hS hSζ
  obtain ⟨hclk, hdrv⟩ := imgClk_imgDrv_zero_time (xj := y) hj hj0 hτ'0 hk hk0 hS hSζ
  have hWc : Continuous (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀) := continuous_eightDrv (h₁.path x₀).2.2.2.1 (hR1 k x₀).1
  obtain ⟨a, W', hown, ha, hW'⟩ := exists_ownData_zero_time (xj := y) hj hj0 hτ'0 hk hk0 hWc
    (eightDrv_zero (h₁.path x₀).1) hS hSζ (eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀)
  simp only [NNReal.coe_zero]
  exact ⟨⟨τ', hτ'0, hk⟩, hgood, hclk, hdrv, a, W', hown, ha, hW'⟩

/-- **At the frozen time `0` the masked canonical image driver is the small driver** up to the exit. -/
theorem g3Snd0_rDrv (k : ℕ) (y₀ : Y) (x₀ : X) {t : ℝ≥0} (ht : t ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => 0) t (x₀, y₀) = W₁ t x₀ := by
  obtain ⟨-, -, -, hdrv, -⟩ := g3Zero_chain hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hlive := g3Snd_live_zero hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ y₀
  have hj0 : Strip.extPath (W₁ · x₀) 0 = 0 := A1Ref.extPath_zero_of (h₁.path x₀).1
  simp only [rDrv, cImgDrvM, cImgDrv, cImgSrc, ite_eq_left hlive]
  rw [hdrv t ⟨t.coe_nonneg, by exact_mod_cast ht⟩, hdrv 0 ⟨le_rfl, NNReal.coe_nonneg _⟩, hj0]
  simp [Strip.extPath]

/-- **At the frozen time `0` the raw caps are the small exits.** -/
theorem g3Snd0_cap (k' : ℕ) (y₀ : Y) (x₀ : X) :
    g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁ ζ₁ W₂ ζ₂ 0 k' (x₀, y₀) = g3S₁ x y W₁ ζ₁ k' x₀ := by
  obtain ⟨hk, hgood, hclk, -, -⟩ := g3Zero_chain hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k' y₀ x₀
  have hlive := g3Snd_live_zero hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ y₀
  have hT : g3SndOwn x y W₁ ζ₁ W₂ ζ₂ 0 k' (x₀, y₀) = (g3S₁ x y W₁ ζ₁ k' x₀ : ℝ) := by
    simp only [g3SndOwn, zero_le, ↓reduceIte]
  unfold g3SndCap
  rw [capSnd_congr_pt (T' := fun _ => (g3S₁ x y W₁ ζ₁ k' x₀ : ℝ)) hT,
    capSnd_eq_of_isGoodTime (T := fun _ => (g3S₁ x y W₁ ζ₁ k' x₀ : ℝ)) hlive
      (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT) (h₁.path x₀).1 hk (h₂.path y₀).1 hgood,
    hclk _ ⟨NNReal.coe_nonneg _, le_rfl⟩, Real.toNNReal_coe]

/-- The data of the identification at `σ = 0` for the force lemmas. -/
theorem g3Snd0_force_data (k : ℕ) (y₀ : Y) (x₀ : X) :
    ∃ a W' : ℝ → ℝ, OwnData (eightDrv W₁ (g3S₁ x y W₁ ζ₁) k x₀)
      (physHull (0 - y) (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ))
      (physMap (0 - y) (Strip.extPath (W₂ · y₀)) ((0 : ℝ≥0) : ℝ)) (g3S₁ x y W₁ ζ₁ k x₀) a W' ∧
      ((g3S₁ x y W₁ ζ₁ k x₀ : ℝ≥0) : ℝ) ≤ a (g3S₁ x y W₁ ζ₁ k x₀) ∧ W' 0 = 0 ∧
      ∀ s : ℝ≥0, s ≤ g3S₁ x y W₁ ζ₁ k x₀ → W₁ (min s (g3S₁ x y W₁ ζ₁ k x₀)) x₀ = W' s - W' 0 := by
  obtain ⟨-, -, -, -, a, W', hown, ha, hW'⟩ := g3Zero_chain hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hS0 : (0 : ℝ) ≤ g3S₁ x y W₁ ζ₁ k x₀ := NNReal.coe_nonneg _
  have hW'0 : W' 0 = 0 := by rw [hW' 0 ⟨le_rfl, hS0⟩]; exact A1Ref.extPath_zero_of (h₁.path x₀).1
  refine ⟨a, W', hown, (ha _ ⟨hS0, le_rfl⟩).symm.le, hW'0, fun s hs => ?_⟩
  rw [min_eq_left hs, hW'0, sub_zero, hW' s ⟨s.coe_nonneg, by exact_mod_cast hs⟩]
  simp [Strip.extPath]

/-- **At the frozen time `0` the canonical left seed force is the small curve's left seed** up to the exit. -/
theorem g3Snd0_VL (k : ℕ) (y₀ : Y) (x₀ : X) (i : Fin 1) {t : ℝ≥0} (ht : t ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ 0 i t (x₀, y₀) = VL₁ i t x₀ := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  by_cases ht0 : t = 0
  · subst ht0
    rw [g3SndVL_zero]
    obtain ⟨-, hL0, -⟩ := h₁.path x₀
    exact (hL0 0).symm
  obtain ⟨hk, hgood, -, -, -⟩ := g3Zero_chain hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  obtain ⟨a, W', hown, hTa, -, hw⟩ := g3Snd0_force_data hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hlive := g3Snd_live_zero hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ y₀
  have hgeo := g3Small_geometry hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  rw [g3SndVL_of_ne y W₁ ζ₁ W₂ VL₂ ζ₂ 0 0 ht0]
  refine (canonSeed_eq_of_geometry_left (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => (0 : ℝ≥0)) z.2) z.2})
    (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => (0 : ℝ≥0))
    (ω := (x₀, y₀)) (xj := y) (xk := 0) hown (eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀)
    (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT) (A1Ref.extPath_zero_of (h₁.path x₀).1) hk
    (A1Ref.extPath_zero_of (h₂.path y₀).1) hgood hgeo hTa hw hlive 0 rfl ht).trans ?_
  simp only [min_eq_left ht]

/-- **At the frozen time `0` the canonical right forces are the small curve's right marks** up to the exit. -/
theorem g3Snd0_VR (k : ℕ) (y₀ : Y) (x₀ : X) (j : Fin 3) {t : ℝ≥0} (ht : t ≤ g3S₁ x y W₁ ζ₁ k x₀) :
    g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j t (x₀, y₀) = VR₁ j t x₀ := by
  obtain ⟨hW0₂, hL0₂, -⟩ := h₂.path y₀
  have hW0' : W₂ 0 y₀ = 0 := hW0₂
  have hx0 : VL₂ 0 0 y₀ = x := hL0₂ 0
  have hy0 : VL₂ 1 0 y₀ = y := hL0₂ 1
  by_cases ht0 : t = 0
  · subst ht0
    rw [g3SndVRc_zero]
    obtain ⟨-, -, hR0, -⟩ := h₁.path x₀
    rw [show VR₁ j 0 x₀ = (![0, x - y, -y] : Fin 3 → ℝ) j from hR0 j]
    fin_cases j <;> simp [g3SndWordR, hW0', hx0, hy0]
  obtain ⟨hk, hgood, -, -, -⟩ := g3Zero_chain hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  obtain ⟨a, W', hown, hTa, hW'0, hw⟩ := g3Snd0_force_data hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hlive := g3Snd_live_zero hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ y₀
  have hgeo := g3Small_geometry hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k y₀ x₀
  have hj := fun T (hT : ENNReal.ofReal T < ζ₁ x₀) => A1Ref.continuousOn_extPath_Icc (h₁.path x₀).2.2.2.1 hT
  have hj0 : Strip.extPath (W₁ · x₀) 0 = 0 := A1Ref.extPath_zero_of (h₁.path x₀).1
  have hk0 : Strip.extPath (W₂ · y₀) 0 = 0 := A1Ref.extPath_zero_of (h₂.path y₀).1
  have hWj := eightDrv_eqOn W₁ (g3S₁ x y W₁ ζ₁) k x₀
  rw [g3SndVRc_of_ne y W₁ ζ₁ W₂ VL₂ ζ₂ 0 j ht0]
  have hy : y < 0 := hyx.trans hx
  fin_cases j
  · refine (canonSeed_eq_of_geometry_right (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => (0 : ℝ≥0)) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => (0 : ℝ≥0))
      (ω := (x₀, y₀)) (xj := y) (xk := 0) hown hWj hj hj0 hk hk0 hgood hgeo hTa hw hlive 0 rfl ht).trans ?_
    simp only [min_eq_left ht]
    rfl
  · refine (canonForce_eq_of_geometry_right (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => (0 : ℝ≥0)) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => (0 : ℝ≥0))
      (ω := (x₀, y₀)) (xj := y) (xk := 0) hown hWj hj hj0 hk hk0 hgood hgeo hTa hw hlive
      (p := fun z => VL₂ 0 0 z.2) 1 (by simp; linarith) (by simp [hx0, hW'0]) ht).trans ?_
    simp only [min_eq_left ht]
    rfl
  · refine (canonForce_eq_of_geometry_right (L := {z : X × Y | g3SndLive W₂ VL₂ ζ₂ ((fun _ => (0 : ℝ≥0)) z.2) z.2})
      (wj := fun z t => W₁ t z.1) (ζj := fun z => ζ₁ z.1) (wk := fun z t => W₂ t z.2) (τ := fun z => (0 : ℝ≥0))
      (ω := (x₀, y₀)) (xj := y) (xk := 0) hown hWj hj hj0 hk hk0 hgood hgeo hTa hw hlive
      (p := fun z => W₂ 0 z.2) 2 (by simp; linarith) (by simp [hW0', hW'0]) ht).trans ?_
    simp only [min_eq_left ht]
    rfl

end Zero

end InteractingSLE.ZhanGT4.A1G3L2
