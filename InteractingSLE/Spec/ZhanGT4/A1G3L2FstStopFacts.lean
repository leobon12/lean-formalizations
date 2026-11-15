/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2FstStopRec

/-!
# Zhan's A.1 under R83, (G3), large-curve direction: the record facts of `ResStopInputFst`

Packet PROVE-A1-G3LAW2. In the setting of `A1G3L2FstStopRec` (patched marginals in the usual augmentations, original
data agreeing on the conull good sets, records `𝓐' m`, `𝓑 m` stopped at `τ ∧ S₁ᵐ` and `S₂ᵐ`; the per-sample facts
`hlife`, `hgood` of the patched large curve as named hypotheses — PROVE-A1-G3LARGE's `g3Fst_lt_lifeEnd`,
`g3Fst_isGoodTime`), the record facts of `ResStopInputFst` for the masked caps, the original canonical image driver and
the large direction's forces `g3FstVL`:

* **`g3FstStop_hSm`**, **`g3FstStop_hstop`**, **`g3FstStop_hgS`** (the caps);
* **`g3FstStop_loc`** (A1-FORCES's `hloc` at the stopped frozen time `τ ∧ S₁ᵐ = τ` on `{r < cap}`);
* **`g3FstStop_hgW`**, **`g3FstStop_hgVL`** (image driver and forces).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom A1MultiMark

section Gen

variable {X Y : Type*} {live : ℝ≥0 → X → Prop} {xj xk : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞}
  {Wk : ℝ≥0 → X → ℝ} {τ₁ τ₂ : X → ℝ≥0} {z : X × Y}

/-- The large-direction mark forces read the frozen time and the mark only at the sample. -/
theorem rForceFst_tau_congr {p₁ p₂ : X → ℝ} (h : τ₁ z.1 = τ₂ z.1) (hp : p₁ z.1 = p₂ z.1) (t : ℝ≥0) :
    rForceFst live xj Wj ζj xk Wk τ₁ p₁ t z = rForceFst live xj Wj ζj xk Wk τ₂ p₂ t z :=
  canonForce_congr_pt (L := {w : X × Y | live (τ₁ w.1) w.1}) (L' := {w : X × Y | live (τ₂ w.1) w.1}) (xj := xj)
    (xk := xk) (wj := fun w t => Wj t w.2) (wj' := fun w t => Wj t w.2) (ζj := fun w => ζj w.2)
    (ζj' := fun w => ζj w.2) (wk := fun w t => Wk t w.1) (wk' := fun w t => Wk t w.1) (τ := fun w => τ₁ w.1)
    (τ' := fun w => τ₂ w.1) (p := fun w => p₁ w.1) (p' := fun w => p₂ w.1) (ω := z)
    (by show live (τ₁ z.1) z.1 ↔ live (τ₂ z.1) z.1; rw [h]) rfl rfl rfl h hp t

end Gen

section Facts

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {VL₁o : Fin 1 → ℝ≥0 → X → ℝ} {VR₁o : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞}
  {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y} {τ : X → ℝ≥0}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hlife : ∀ (k : ℕ) (_ : X) (y₀ : Y),
    (g3S₂ x y W₂ ζ₂ k y₀ : ℝ≥0∞) < lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀))
  (hgood : ∀ (k : ℕ) (x₀ : X) (y₀ : Y) {σ : ℝ≥0}, 0 < σ → σ ≤ g3S₁ x y W₁ ζ₁ k x₀ →
    A1Ref.IsGoodTime 0 (Strip.extPath (W₂ · y₀)) (lifeEnd (W₂ · y₀) (VL₂ 0 · y₀) (ζ₂ y₀)) y
      (Strip.extPath (W₁ · x₀)) σ (g3S₂ x y W₂ ζ₂ k y₀))
  (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0))
  (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x' => (τ x' : WithTop ℝ≥0))
  (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0)
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ (∀ i t, VL₁o i t x' = VL₁ i t x') ∧
    (∀ j t, VR₁o j t x' = VR₁ j t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

/-- The product of the two stopped records of rectangle `m` (large direction). -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₁ m)))
  (IsStoppingTime.measurableSpace (hs₂ m))

/-- The masked caps of the large direction. -/
local notation "𝓢" => maskCap G₁ G₂ (g3FstCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂)

include hag₁ in
omit [MeasurableSpace X] [MeasurableSpace Y] in
/-- The agreement of the small curves used by the caps. -/
theorem g3Fst_hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x' :=
  fun x' hx' => ⟨(hag₁ x' hx').1, (hag₁ x' hx').2.2.2⟩

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂

/-- **`hSm`** (large direction). -/
theorem g3FstStop_hSm (m : ℕ) : Measurable[𝓡 m] fun z => (𝓢) (τ z.1) m z := by
  obtain ⟨hS₁, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have e : (fun z => (𝓢) (τ z.1) m z) = (g3FstRecSet x y W₁ ζ₁ G₁ G₂ τ m).indicator
      (capFst (fun _ _ => True) 0 W₂ (fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) y W₁
        (g3Fτ x y W₁ ζ₁ τ m) fun z => (g3S₂ x y W₂ ζ₂ m z.2 : ℝ)) :=
    funext (g3FstStop_cap_eq (g3Fst_hag₁ hag₁) hag₂ (fun m x' => (hS₁ m x').1) τ m)
  rw [e]
  have hS₂m : Measurable[(hs₂ m).measurableSpace] (g3S₂ x y W₂ ζ₂ m) := measurable_stop_self (hs₂ m) fun _ => rfl
  have hT : Measurable[𝓡 m] fun z : X × Y => (g3S₂ x y W₂ ζ₂ m z.2 : ℝ) :=
    (hS₂m.comp (@measurable_snd X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace)).coe_nnreal_real
  exact (measurable_g3FstRecCap hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hs₁ hs₂ hτ m hT fun z _ => le_rfl).indicator
    (measurableSet_g3FstRecSet hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 m)

/-- **`hstop`** (large direction). -/
theorem g3FstStop_hstop (m : ℕ) (s : ℝ≥0) (C : Set X) (hC : C ∈ {B | MeasurableSet[hτ.measurableSpace] B}) :
    MeasurableSet[𝓡 m] (Prod.fst ⁻¹' C ∩ {z | s < (𝓢) (τ z.1) m z}) :=
  measurableSet_fst_inter_cap hτ (hs₁ m) (𝓑 := (hs₂ m).measurableSpace)
    (measurableSet_lt measurable_const
      (g3FstStop_hSm hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ m))
    (fun _ hz => WithTop.coe_le_coe.2 (g3FstStop_pos (g3Fst_hag₁ hag₁) hag₂ (zero_le.trans_lt hz)).2.2) hC

omit hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ in
include hgood in
/-- The clock up to the own time of a raw cap is finite on live samples (large direction). -/
theorem g3FstStop_fin (k : ℕ) {σ : ℝ≥0} {z : X × Y} (hl : (σ : ℝ≥0∞) < ζ₁ z.1) :
    clkSup 0 (Strip.extPath (W₂ · z.2)) (lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) y (Strip.extPath (W₁ · z.1)) σ
      (g3FstOwn x y W₁ ζ₁ W₂ ζ₂ σ k z) ≠ ∞ := by
  by_cases hle : σ ≤ g3S₁ x y W₁ ζ₁ k z.1
  · have hown : g3FstOwn x y W₁ ζ₁ W₂ ζ₂ σ k z = g3S₂ x y W₂ ζ₂ k z.2 := by
      simp only [g3FstOwn, hle, ↓reduceIte]
    rw [hown, clkSup_eq_of_isGoodTime (fun T hT => A1Ref.continuousOn_extPath_Icc
      ((h₂.path z.2).2.2.2.1.mono fun t ht => lt_of_lt_of_le ht (lifeEnd_le _ _ _)) hT)
      (by simpa [Strip.extPath] using (h₂.path z.2).1)
      (A1Ref.exists_continuousOn_extPath_beyond (h₁.path z.1).2.2.2.1 hl)
      (by simpa [Strip.extPath] using (h₁.path z.1).1) σ.coe_nonneg
      (g3Fst_good_le hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood k z.1 z.2 hle)]
    exact ENNReal.ofReal_ne_top
  · rw [clkSup_of_nonpos (by simp only [g3FstOwn, hle, ↓reduceIte, le_refl])]
    exact ENNReal.zero_ne_top

include hgood in
/-- **`hgS`** (large direction). -/
theorem g3FstStop_hgS (m k : ℕ) (r : ℝ≥0) :
    MeasurableSet[𝓡 m] ({z | (𝓢) (τ z.1) k z ≤ r} ∩ {z | r < (𝓢) (τ z.1) m z}) := by
  obtain ⟨hS₁, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hag₁' := g3Fst_hag₁ hag₁
  set Tkm : X × Y → ℝ := fun z => if τ z.1 ≤ g3S₁ x y W₁ ζ₁ k z.1 ∧ τ z.1 ≤ g3S₁ x y W₁ ζ₁ m z.1 then
    (min (g3S₂ x y W₂ ζ₂ k z.2) (g3S₂ x y W₂ ζ₂ m z.2) : ℝ) else 0 with hTkm
  set R := g3FstRecSet x y W₁ ζ₁ G₁ G₂ τ m with hR
  have hmin : ∀ z ∈ R, min ((𝓢) (τ z.1) k z) ((𝓢) (τ z.1) m z) =
      capFst (fun _ _ => True) 0 W₂ (fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) y W₁
        (g3Fτ x y W₁ ζ₁ τ m) Tkm z := by
    intro z hz
    obtain ⟨h1, h2, hle⟩ := hz
    have hl : (τ z.1 : ℝ≥0∞) < ζ₁ z.1 := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hle) (hS₁ m z.1).1
    rw [g3FstStop_mask_eq hag₁' hag₂ k h1 h2, g3FstStop_mask_eq hag₁' hag₂ m h1 h2]
    unfold g3FstCap
    rw [min_capFst_eq (live := fun t x' => (t : ℝ≥0∞) < ζ₁ x') (xj := 0) (Wj := W₂)
      (ζj := fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) (xk := y) (Wk := W₁) (τ := fun _ => τ z.1)
      (T := g3FstOwn x y W₁ ζ₁ W₂ ζ₂ (τ z.1) k) (T' := g3FstOwn x y W₁ ζ₁ W₂ ζ₂ (τ z.1) m) (z := z)
      (fun _ => g3FstStop_fin hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood k hl)
      (fun _ => g3FstStop_fin hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood m hl),
      capFst_true_eq (live := fun t x' => (t : ℝ≥0∞) < ζ₁ x') (τ₂ := fun _ => τ z.1) hl (min_eq_left hle)]
    refine capFst_congr_pt ?_
    simp only [hTkm, g3FstOwn, hle, and_true]
    split_ifs <;> simp
  have hRm := measurableSet_g3FstRecSet hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 m
  have hTm : Measurable[𝓡 m] Tkm := by
    have hE := measurableSet_g3Fst_le_le hs₁ hτ k m
    have hmin₂ : Measurable[(hs₂ m).measurableSpace] fun y' => min (g3S₂ x y W₂ ζ₂ k y') (g3S₂ x y W₂ ζ₂ m y') :=
      (measurable_stop_self ((hs₂ k).min (hs₂ m)) fun y' => by simp only [WithTop.coe_min]).mono
        (((hs₂ k).min (hs₂ m)).measurableSpace_mono (hs₂ m) fun _ => min_le_right _ _) le_rfl
    refine Measurable.ite (p := fun z : X × Y => τ z.1 ≤ g3S₁ x y W₁ ζ₁ k z.1 ∧ τ z.1 ≤ g3S₁ x y W₁ ζ₁ m z.1)
      ?_ ?_ measurable_const
    · exact @measurable_fst X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace _ hE
    · exact (hmin₂.comp (@measurable_snd X Y (hτ.min (hs₁ m)).measurableSpace
        (hs₂ m).measurableSpace)).coe_nnreal_real
  have hTle : ∀ z, 0 < Tkm z → Tkm z ≤ g3S₂ x y W₂ ζ₂ m z.2 := by
    intro z hz
    simp only [hTkm] at hz ⊢
    split_ifs at hz ⊢ with h
    · exact_mod_cast min_le_right _ _
    · exact absurd hz (lt_irrefl 0)
  have hcm := measurable_g3FstRecCap hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hs₁ hs₂ hτ m hTm hTle
  have hSm := g3FstStop_hSm hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ m
  have e : {z | (𝓢) (τ z.1) k z ≤ r} ∩ {z | r < (𝓢) (τ z.1) m z} =
      R ∩ ({z | capFst (fun _ _ => True) 0 W₂ (fun y' => lifeEnd (W₂ · y') (VL₂ 0 · y') (ζ₂ y')) y W₁
        (g3Fτ x y W₁ ζ₁ τ m) Tkm z ≤ r} ∩ {z | r < (𝓢) (τ z.1) m z}) := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hk, hm⟩
      have hzR : z ∈ R := g3FstStop_pos hag₁' hag₂ (zero_le.trans_lt hm)
      refine ⟨hzR, ?_, hm⟩
      rw [← hmin z hzR]
      exact (min_le_left _ _).trans hk
    · rintro ⟨hzR, hk, hm⟩
      refine ⟨?_, hm⟩
      rw [← hmin z hzR] at hk
      rcases min_choice ((𝓢) (τ z.1) k z) ((𝓢) (τ z.1) m z) with h | h
      · rwa [h] at hk
      · rw [h] at hk
        exact absurd (hm.trans_le hk) (lt_irrefl _)
  rw [e]
  exact hRm.inter ((measurableSet_le hcm measurable_const).inter (measurableSet_lt measurable_const hSm))

omit hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ hlife in
/-- **The stopped replacement data** (large direction): continuous (lifetime `⊤`), started at `0`,
record-measurable. -/
theorem g3FstStop_repl (m : ℕ) :
    (∀ y', ContinuousOn (fun t => W₂ (min t (g3S₂ x y W₂ ζ₂ m y')) y') {t | (t : ℝ≥0∞) < ⊤}) ∧
    (∀ y', W₂ (min 0 (g3S₂ x y W₂ ζ₂ m y')) y' = 0) ∧
    (∀ x', ContinuousOn (fun t => W₁ (min t (g3Fτ x y W₁ ζ₁ τ m x')) x') {t | (t : ℝ≥0∞) < ⊤}) ∧
    (∀ x', W₁ (min 0 (g3Fτ x y W₁ ζ₁ τ m x')) x' = 0) ∧
    (∀ t, Measurable[(hs₂ m).measurableSpace] fun y' => W₂ (min t (g3S₂ x y W₂ ζ₂ m y')) y') ∧
    (∀ t, Measurable[(hτ.min (hs₁ m)).measurableSpace] fun x' => W₁ (min t (g3Fτ x y W₁ ζ₁ τ m x')) x') := by
  obtain ⟨hS₁, -, -, -, hS₂ζ⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hτζ : ∀ x', ((g3Fτ x y W₁ ζ₁ τ m x' : ℝ≥0) : ℝ≥0∞) < ζ₁ x' := fun x' =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hS₁ m x').1
  exact ⟨fun y' => (continuous_stopped (h₂.path y').2.2.2.1 (hS₂ζ m y')).continuousOn,
    fun y' => by simp only [zero_le, min_eq_left]; exact (h₂.path y').1,
    fun x' => (continuous_stopped (h₁.path x').2.2.2.1 (hτζ x')).continuousOn,
    fun x' => by simp only [zero_le, min_eq_left]; exact (h₁.path x').1,
    fun t => measurable_stopped_at h₂.progW (hs₂ m) t,
    fun t => measurable_stopped_at' h₁.progW (hτ.min (hs₁ m)) (T := g3Fτ x y W₁ ζ₁ τ m)
      (fun x' => by simp only [g3Fτ, WithTop.coe_min]) t⟩

omit [MeasurableSpace X] [MeasurableSpace Y] hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hG₁ hG₂ hG₁0 hG₂0 in
/-- On `{r < cap}` the stopped frozen time is the stop (large direction). -/
theorem g3FstStop_tau_eq {m : ℕ} {r : ℝ≥0} {z : X × Y} (hz : r < (𝓢) (τ z.1) m z) :
    τ z.1 = g3Fτ x y W₁ ζ₁ τ m z.1 :=
  (min_eq_left (g3FstStop_pos (g3Fst_hag₁ hag₁) hag₂ (zero_le.trans_lt hz)).2.2).symm

omit hG₁ hG₂ hG₁0 hG₂0 in
include hgood in
/-- **`hloc` of the stopped records** (large direction). -/
theorem g3FstStop_loc (m : ℕ) (r : ℝ≥0) (z : X × Y) (hz : r < (𝓢) (τ z.1) m z) :
    ((g3Fτ x y W₁ ζ₁ τ m z.1 : ℝ≥0∞) < ζ₁o z.1) ∧ True ∧
    (∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂o · z.2) (VL₂o 0 · z.2) (ζ₂o z.2) →
      ContinuousOn (Strip.extPath (W₂o · z.2)) (Icc 0 T)) ∧ W₂o 0 z.2 = 0 ∧
    (∃ τ', ((g3Fτ x y W₁ ζ₁ τ m z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁o · z.1)) (Icc 0 τ')) ∧
    W₁o 0 z.1 = 0 ∧
    A1Ref.IsGoodTime 0 (Strip.extPath (W₂o · z.2)) (lifeEnd (W₂o · z.2) (VL₂o 0 · z.2) (ζ₂o z.2)) y
      (Strip.extPath (W₁o · z.1)) (g3Fτ x y W₁ ζ₁ τ m z.1) (g3S₂ x y W₂ ζ₂ m z.2) ∧
    A1Ref.IsGoodTime 0 (Strip.extPath fun t => W₂ (min t (g3S₂ x y W₂ ζ₂ m z.2)) z.2) ⊤ y
      (Strip.extPath fun t => W₁ (min t (g3Fτ x y W₁ ζ₁ τ m z.1)) z.1) (g3Fτ x y W₁ ζ₁ τ m z.1)
      (g3S₂ x y W₂ ζ₂ m z.2) ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ g3S₂ x y W₂ ζ₂ m z.2 → W₂ (min t (g3S₂ x y W₂ ζ₂ m z.2)) z.2 = W₂o t z.2) ∧
    (∀ t ≤ g3Fτ x y W₁ ζ₁ τ m z.1, W₁ (min t (g3Fτ x y W₁ ζ₁ τ m z.1)) z.1 = W₁o t z.1) ∧
    (((𝓢) (τ z.1) m z : ℝ≥0) : ℝ) ≤ A1Ref.imgClk 0 (Strip.extPath (W₂o · z.2)) y (Strip.extPath (W₁o · z.1))
      (g3Fτ x y W₁ ζ₁ τ m z.1) (g3S₂ x y W₂ ζ₂ m z.2) := by
  have hag₁' := g3Fst_hag₁ hag₁
  have hpos := zero_le.trans_lt hz
  obtain ⟨h1, h2, hle⟩ := g3FstStop_pos hag₁' hag₂ hpos
  obtain ⟨hS₁, -, -, -, -⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hτm : g3Fτ x y W₁ ζ₁ τ m z.1 = τ z.1 := min_eq_left hle
  obtain ⟨hW₁a, -, -, hζ₁a⟩ := hag₁ z.1 h1
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ z.2 h2
  have eW₁ : (W₁o · z.1) = (W₁ · z.1) := funext hW₁a
  have eW₂ : (W₂o · z.2) = (W₂ · z.2) := funext hW₂a
  have eV₂ : (VL₂o 0 · z.2) = (VL₂ 0 · z.2) := funext (hV₂a 0)
  have hl : (τ z.1 : ℝ≥0∞) < ζ₁ z.1 := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hle) (hS₁ m z.1).1
  have hgd := g3Fst_good_le hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood m z.1 z.2 hle
  have hgd' := g3Fst_good_stop hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hlife hgood m z.1 z.2 hle
  have hj : ∀ T : ℝ, ENNReal.ofReal T < lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2) →
      ContinuousOn (Strip.extPath (W₂ · z.2)) (Icc 0 T) := fun T hT => A1Ref.continuousOn_extPath_Icc
    ((h₂.path z.2).2.2.2.1.mono fun t ht => lt_of_lt_of_le ht (lifeEnd_le _ _ _)) hT
  have hk : ∃ τ' : ℝ, ((τ z.1 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₁ · z.1)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (h₁.path z.1).2.2.2.1 hl
  have hcap : (𝓢) (τ z.1) m z =
      (A1Ref.imgClk 0 (Strip.extPath (W₂ · z.2)) y (Strip.extPath (W₁ · z.1)) (τ z.1)
        (g3S₂ x y W₂ ζ₂ m z.2)).toNNReal := by
    rw [g3FstStop_mask_eq hag₁' hag₂ m h1 h2]
    unfold g3FstCap
    rw [capFst_congr_pt (T' := fun z => (g3S₂ x y W₂ ζ₂ m z.2 : ℝ))
      (by simp only [g3FstOwn, hle, ↓reduceIte])]
    exact capFst_eq_of_isGoodTime (τ := fun _ => τ z.1) (live := fun t x' => (t : ℝ≥0∞) < ζ₁ x') hl hj
      (h₂.path z.2).1 hk (h₁.path z.1).1 hgd
  rw [hτm]
  refine ⟨by rw [hζ₁a]; exact hl, trivial, fun T hT => ?_, by rw [hW₂a]; exact (h₂.path z.2).1,
    by rw [eW₁]; exact hk, by rw [hW₁a]; exact (h₁.path z.1).1,
    by rw [eW₁, eW₂, eV₂, hζ₂a]; exact hgd, hgd', fun t ht => ?_,
    fun t ht => by rw [min_eq_left ht, hW₁a], ?_⟩
  · rw [eW₂]
    exact hj T (by rwa [← eW₂, ← eV₂, ← hζ₂a])
  · rw [min_eq_left (show t ≤ g3S₂ x y W₂ ζ₂ m z.2 by exact_mod_cast ht), hW₂a]
  · rw [hcap, eW₁, eW₂]
    have hp : 0 < (A1Ref.imgClk 0 (Strip.extPath (W₂ · z.2)) y (Strip.extPath (W₁ · z.1)) (τ z.1)
        (g3S₂ x y W₂ ζ₂ m z.2)).toNNReal := by rw [← hcap]; exact hpos
    rw [Real.coe_toNNReal _ (Real.toNNReal_pos.1 hp).le]

end Facts

end InteractingSLE.ZhanGT4.A1G3L2
