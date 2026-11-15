/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part3IDMain
import InteractingSLE.Spec.ZhanGT4.A2Part1Crosscut

/-!
# A.2 part 3 from (I2) alone: the image words of the application are strictly ordered

Packet PROVE-ZHAN-A2P3-ID. In the application of (I1) (`A2Part3Split.largeAccum…Statement_of_split`) the image word at a
deterministic time `q > 0` is `g_q` of the marks `x`, `y⁺`, the small tip and `y⁻` (G3), resp. `x⁺`, the small tip and
`x⁻` (Eight), relative to the image source. A.2 part 1's noncollision of the small curve
(`A2P1.ae_noncollision_simpleTrace`: every mark strictly off the driver at positive times before the lifetime) and the
strict order of two marks one of which stays off the driver (`IsForcePath.vL_lt_vL_of_lt`) make it strictly decreasing.
So the strict forms of (I1) (`imageDichotomy{G3,Eight}StrictStatement`, proved) suffice:

* **`largeAccumG3Statement_of_strict`**, **`largeAccumEightStatement_of_strict`** (the proofs of A2P3's
  `largeAccum…_of_split` with the strict image word);
* **`smallInHullG3Statement_of_pairContact`**, **`smallInHullEightStatement_of_pairContact`**: A.2 part 3
  (`A2SmallInHull…Statement`) from (I2) (`PairContact…Statement`) alone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Bornology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2P3ID

open ZhanGT4.A2X ZhanGT4.A2X.P3

/-! ### The small curves keep their marks apart -/

section Small

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **(G3) The small curve keeps its seeds and the mark `x` apart from the driver and in order.** -/
theorem smallG3_sep {κ : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) {y x : ℝ} (hyx : y < x) (hx : x < 0)
    {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 3 → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P 𝓕 W VL VR B
      ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω →
      VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω ∧ VR 0 t ω < VR 1 t ω := by
  obtain ⟨hk2, hk4⟩ := kh_bounds_G3 hκ4 hκ8
  have hk0 : 0 < kh κ := by linarith
  have h := A2P1.ae_noncollision_simpleTrace (ρL' := ![2 - kh κ / 2, kh κ - 4, 0]) hk0 hk4.le
    (A2P1.g3_ordered hyx hx) (by rw [A2P1.g3_last]; linarith)
    (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi)
    (A2P1.g3_adm hk2.le hk4.le hx) (A2P1.g3_sum _) (A2P1.g3_preL hk0 hk4) (A2P1.one_preR (by linarith))
    hE.reflect
  filter_upwards [h, hE.ae_isIntegratedSLEPath] with ω hω hp t ht0 htζ
  obtain ⟨-, hsep, -⟩ := hω
  have hfp := hp.isForcePath
  have hR : ∀ r : ℝ≥0, 0 < r → (r : ℝ≥0∞) < ζ ω → ∀ i, W r ω < VR i r ω := fun r hr0 hrζ i => by
    have := (hsep r hr0 hrζ).1 i
    simp only [Pi.neg_apply] at this
    linarith
  have hL : VL 0 t ω < W t ω := by
    have := (hsep t ht0 htζ).2 0
    simp only [Pi.neg_apply] at this
    linarith
  refine ⟨hL, hR t ht0 htζ 0, ?_⟩
  have hfr := hfp.reflect
  have hord := hfr.vL_lt_vL_of_lt htζ (i := 0) (j := 1) (by simp; linarith) fun r hr => by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ r) with h0 | h0
    · rw [← h0]
      simp only [Pi.neg_apply, hfp.vR_zero, hfp.w_zero]
      simp
      linarith
    · have := hR r h0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hr) htζ) 1
      simp only [Pi.neg_apply]
      linarith
  simp only [Pi.neg_apply] at hord
  linarith

/-- **(Eight) The small curve keeps its seeds apart from the driver.** -/
theorem smallEight_sep {κ : ℝ} (hκ8 : 8 ≤ κ) {x : ℝ} (hx : x < 0)
    {VL : Fin 1 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ ω → VL 0 t ω < W t ω ∧ W t ω < VR 0 t ω := by
  obtain ⟨hk0, hk2⟩ := kh_bounds_eight hκ8
  have h := A2P1.ae_noncollision_simpleTrace (ρL' := ![kh κ / 2 - 2, 0]) hk0 (by linarith) (A2P1.e8_ordered hx)
    (by rw [A2P1.e8_last]; exact hx) (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi)
    (A2P1.e8_adm hk2) (A2P1.e8_sum _) (A2P1.e8_preL hk0) (A2P1.one_preR (by linarith)) hE.reflect
  filter_upwards [h] with ω hω t ht0 htζ
  obtain ⟨-, hsep, -⟩ := hω
  have h1 := (hsep t ht0 htζ).1 0
  have h2 := (hsep t ht0 htζ).2 0
  simp only [Pi.neg_apply] at h1 h2
  exact ⟨by linarith, by linarith⟩

end Small

/-! ### The rewired consumers -/

/-- **The large-hull accumulation, (G3)**, from the strict (I1) and (I2) (A2P3's proof with the strict image word). -/
theorem largeAccumG3Statement_of_strict {κ : ℝ} (hD : ImageDichotomyG3StrictStatement.{u} κ)
    (hC : PairContactG3Statement.{u} κ) : LargeAccumG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hE, hch⟩ := hpair.2.2.2 (fun _ => q) (isStoppingTime_const 𝓕₁ q)
  have hneg : ∀ᵐ ω ∂P, ω ∈ {ω | (q : ℝ≥0∞) < ζ₁ ω} →
      (![VR₁ 1 q ω - VR₁ 2 q ω, VR₁ 0 q ω - VR₁ 2 q ω, W₁ q ω - VR₁ 2 q ω, VL₁ 0 q ω - VR₁ 2 q ω] : Fin 4 → ℝ) 0
        < 0 ∧ StrictAnti
      (![VR₁ 1 q ω - VR₁ 2 q ω, VR₁ 0 q ω - VR₁ 2 q ω, W₁ q ω - VR₁ 2 q ω, VL₁ 0 q ω - VR₁ 2 q ω] : Fin 4 → ℝ) := by
    filter_upwards [hpair.2.1.2.2.2.2, smallG3_sep hκ4 hκ8 hyx hx hpair.2.1] with ω hp hs hq
    have h12 := smallG3_vR_one_lt_two hκ4 hκ8 hx hp hq
    obtain ⟨a1, a2, a3⟩ := hs q hq0 hq
    refine ⟨by simpa using h12, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  filter_upwards [hD hκ4 hκ8 _ P _ _ 𝓖 W' VL' VR' B' ζ' hE hneg, hch,
    hC hκ4 hκ8 y x hyx hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0] with ω h1 hc h2 hq
  have h1' : ((W₁ q ω - VR₁ 2 q ω : ℝ) : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
      (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧ ∀ u : ℝ, u ≤ VR₁ 1 q ω - VR₁ 2 q ω →
        (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω))) := h1 hq
  have hA : preContactImage y (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q =
      (fun z : ℂ => z + (y + VR₁ 2 q ω : ℝ)) '' imgHulls (W' · ω) (ζ' ω) := by
    rw [← iUnion_physHull_eq, iUnion_physHull_eq_of_imageChain (hc hq)]
    rfl
  have he1 : ((W₁ q ω - VR₁ 2 q ω) + (y + VR₁ 2 q ω) : ℝ) = y + W₁ q ω := by ring
  have he2 : (VR₁ 1 q ω - VR₁ 2 q ω) + (y + VR₁ 2 q ω) = y + VR₁ 1 q ω := by ring
  have h := mem_closure_of_dichotomy_of_pair hA h1' (by rw [he1, he2, Complex.ofReal_add]; exact h2 hq)
  rw [he1, Complex.ofReal_add] at h
  exact h

/-- **The large-hull accumulation, (Eight)**, from the strict (I1) and (I2). -/
theorem largeAccumEightStatement_of_strict {κ : ℝ} (hD : ImageDichotomyEightStrictStatement.{u} κ)
    (hC : PairContactEightStatement.{u} κ) : LargeAccumEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P hP 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0
  obtain ⟨𝓖, W', VL', VR', B', ζ', clk, hE, hch⟩ := hpair.2.2.2 (fun _ => q) (isStoppingTime_const 𝓕₁ q)
  have hneg : ∀ᵐ ω ∂P, ω ∈ {ω | (q : ℝ≥0∞) < ζ₁ ω} →
      (![VR₁ 0 q ω - VR₁ 1 q ω, W₁ q ω - VR₁ 1 q ω, VL₁ 0 q ω - VR₁ 1 q ω] : Fin 3 → ℝ) 0 < 0 ∧
        StrictAnti (![VR₁ 0 q ω - VR₁ 1 q ω, W₁ q ω - VR₁ 1 q ω, VL₁ 0 q ω - VR₁ 1 q ω] : Fin 3 → ℝ) := by
    filter_upwards [hpair.2.1.2.2.2.2, smallEight_sep hκ8 hx hpair.2.1] with ω hp hs hq
    have h01 := smallEight_vR_zero_lt_one hκ8 hx hp hq
    obtain ⟨a1, a2⟩ := hs q hq0 hq
    refine ⟨by simpa using h01, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  filter_upwards [hD hκ8 _ P _ _ 𝓖 W' VL' VR' B' ζ' hE hneg, hch,
    hC hκ8 x hx P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ hpair q hq0] with ω h1 hc h2 hq
  have h1' : ((W₁ q ω - VR₁ 1 q ω : ℝ) : ℂ) ∈ closure (imgHulls (W' · ω) (ζ' ω)) ∨
      (IsBounded (imgHulls (W' · ω) (ζ' ω)) ∧ ∀ u : ℝ, u ≤ VR₁ 0 q ω - VR₁ 1 q ω →
        (u : ℂ) ∉ closure (imgHulls (W' · ω) (ζ' ω))) := h1 hq
  have hA : preContactImage x (W₁ · ω) (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) q =
      (fun z : ℂ => z + (x + VR₁ 1 q ω : ℝ)) '' imgHulls (W' · ω) (ζ' ω) := by
    rw [← iUnion_physHull_eq, iUnion_physHull_eq_of_imageChain (hc hq)]
    rfl
  have he1 : ((W₁ q ω - VR₁ 1 q ω) + (x + VR₁ 1 q ω) : ℝ) = x + W₁ q ω := by ring
  have he2 : (VR₁ 0 q ω - VR₁ 1 q ω) + (x + VR₁ 1 q ω) = x + VR₁ 0 q ω := by ring
  have h := mem_closure_of_dichotomy_of_pair hA h1' (by rw [he1, he2, Complex.ofReal_add]; exact h2 hq)
  rw [he1, Complex.ofReal_add] at h
  exact h

/-- **A.2, part 3, (G3)** (`A2SmallInHullG3Statement`) **from (I2) alone**: (I1) is proved
(`imageDichotomyG3StrictStatement`). -/
theorem smallInHullG3Statement_of_pairContact {κ : ℝ} (hC : PairContactG3Statement.{u} κ) :
    A2SmallInHullG3Statement.{u} κ :=
  smallInHullG3Statement_of_tip (tipInHullG3Statement_of_largeAccum
    (largeAccumG3Statement_of_strict (imageDichotomyG3StrictStatement κ) hC))

/-- **A.2, part 3, (Eight)** (`A2SmallInHullEightStatement`) **from (I2) alone**. -/
theorem smallInHullEightStatement_of_pairContact {κ : ℝ} (hC : PairContactEightStatement.{u} κ) :
    A2SmallInHullEightStatement.{u} κ :=
  smallInHullEightStatement_of_tip (tipInHullEightStatement_of_largeAccum
    (largeAccumEightStatement_of_strict (imageDichotomyEightStrictStatement κ) hC))

end InteractingSLE.ZhanGT4.A2P3ID
