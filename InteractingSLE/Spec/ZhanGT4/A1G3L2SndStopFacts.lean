/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopRec

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the record facts of `ResStopInput`

Packet PROVE-A1-G3LAW2. In the setting of `A1G3L2SndStopRec` (patched marginals in the usual augmentations, original
data agreeing on the conull good sets, records `𝓐 m`, `𝓑' m` stopped at `S₁ᵐ` and `τ ∧ S₂ᵐ`), the record facts of
`ResStopInput` for the masked caps, the original canonical image driver and the corrected forces:

* **`g3Stop_hSm`**, **`g3Stop_hstop`**, **`g3Stop_hgS`** (the caps);
* **`g3Stop_loc`**: on `{r < cap}` the original data agree with the stopped patched replacement data up to the good
  horizon `S₁ᵐ` (A1-FORCES's `hloc`);
* **`g3Stop_hgW`**, **`g3Stop_hgVL`**, **`g3Stop_hgVR`** (image driver and forces, via A1-SEEDGEOM's
  `exists_measurable_rDrv_of_stopped`, A1-G3ROW's `exists_measurable_rSeedSnd_of_stopped` and A1-FORCES's
  `exists_measurable_rForceSnd_of_stopped` at the stopped frozen time `τ ∧ S₂ᵐ`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1G3Law A1LargeDens A1SeedGeom

section Gen

variable {X Y : Type*} {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ}
  {Wk : ℝ≥0 → Y → ℝ}

/-- On a live sample the cap with the trivial live event is the cap. -/
theorem capSnd_true_eq {τ₁ τ₂ : Y → ℝ≥0} {T : X × Y → ℝ} {z : X × Y} (hl : live (τ₂ z.2) z.2)
    (hτ : τ₁ z.2 = τ₂ z.2) :
    capSnd (fun _ _ => True) xj Wj ζj xk Wk τ₁ T z = capSnd live xj Wj ζj xk Wk τ₂ T z := by
  unfold capSnd
  rw [indicator_of_mem (show z ∈ {w : X × Y | (fun (_ : ℝ≥0) (_ : Y) => True) (τ₁ w.2) w.2} from trivial),
    indicator_of_mem (show z ∈ {w : X × Y | live (τ₂ w.2) w.2} from hl), hτ]

/-- The minimum of two caps with finite clocks is the cap at the minimum own time. -/
theorem min_capSnd_eq {τ : Y → ℝ≥0} {T T' : X × Y → ℝ} {z : X × Y}
    (hfin : live (τ z.2) z.2 → clkSup xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2)
      (T z) ≠ ∞)
    (hfin' : live (τ z.2) z.2 → clkSup xj (Strip.extPath (Wj · z.1)) (ζj z.1) xk (Strip.extPath (Wk · z.2))
      (τ z.2) (T' z) ≠ ∞) :
    min (capSnd live xj Wj ζj xk Wk τ T z) (capSnd live xj Wj ζj xk Wk τ T' z) =
      capSnd live xj Wj ζj xk Wk τ (fun z => min (T z) (T' z)) z := by
  rcases le_total (T z) (T' z) with h | h
  · rw [min_eq_left (capSnd_mono h hfin'), capSnd_congr_pt (T' := fun z => min (T z) (T' z)) (min_eq_left h).symm]
  · rw [min_eq_right (capSnd_mono h hfin), capSnd_congr_pt (T' := fun z => min (T z) (T' z)) (min_eq_right h).symm]

end Gen

section Facts

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x y : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 2 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y} {τ : Y → ℝ≥0}

variable (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0))
  (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0))
  (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0) (hG₂0 : P₂ G₂ᶜ = 0)
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

/-- The product of the two stopped records of rectangle `m`. -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (hs₁ m))
  (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₂ m)))

/-- The masked caps at the stop. -/
local notation "𝓢" => maskCap G₁ G₂ (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂)

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂

/-- **`hSm`**: the masked cap at the stop is record-measurable. -/
theorem g3Stop_hSm (m : ℕ) : Measurable[𝓡 m] fun z => (𝓢) (τ z.2) m z := by
  have e : (fun z => (𝓢) (τ z.2) m z) = (g3RecSet x y W₂ VL₂ ζ₂ G₁ G₂ τ m).indicator
      (capSnd (fun _ _ => True) y W₁ ζ₁ 0 W₂ (g3Sτ x y W₂ ζ₂ τ m) fun z => (g3S₁ x y W₁ ζ₁ m z.1 : ℝ)) :=
    funext (g3Stop_cap_eq hag₁ hag₂ τ m)
  rw [e]
  have hS₁m : Measurable[(hs₁ m).measurableSpace] (g3S₁ x y W₁ ζ₁ m) := measurable_stop_self (hs₁ m) fun _ => rfl
  have hT : Measurable[𝓡 m] fun z : X × Y => (g3S₁ x y W₁ ζ₁ m z.1 : ℝ) :=
    (hS₁m.comp (@measurable_fst X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace)).coe_nnreal_real
  exact (measurable_g3RecCap hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m hT fun z _ => le_rfl).indicator
    (measurableSet_g3RecSet h₂ hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 m)

/-- **`hstop`**: events of the stopped σ-algebra at `τ` cut by the cap event are record events. -/
theorem g3Stop_hstop (m : ℕ) (s : ℝ≥0) (C : Set Y) (hC : C ∈ {B | MeasurableSet[hτ.measurableSpace] B}) :
    MeasurableSet[𝓡 m] (Prod.snd ⁻¹' C ∩ {z | s < (𝓢) (τ z.2) m z}) :=
  A1MultiMark.measurableSet_snd_inter_cap hτ (hs₂ m) (𝓐 := (hs₁ m).measurableSpace)
    (measurableSet_lt measurable_const
      (g3Stop_hSm hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ m))
    (fun _ hz => WithTop.coe_le_coe.2 (g3Stop_pos hag₁ hag₂ (zero_le.trans_lt hz)).2.2.1) hC

omit hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ in
/-- The clock up to the own time of a raw cap is finite on live samples. -/
theorem g3Stop_fin (k : ℕ) {σ : ℝ≥0} {z : X × Y} (hl : g3SndLive W₂ VL₂ ζ₂ σ z.2) :
    clkSup y (Strip.extPath (W₁ · z.1)) (ζ₁ z.1) 0 (Strip.extPath (W₂ · z.2)) σ
      (g3SndOwn x y W₁ ζ₁ W₂ ζ₂ σ k z) ≠ ∞ := by
  by_cases hle : σ ≤ g3S₂ x y W₂ ζ₂ k z.2
  · have hown : g3SndOwn x y W₁ ζ₁ W₂ ζ₂ σ k z = g3S₁ x y W₁ ζ₁ k z.1 := by
      simp only [g3SndOwn, hle, ↓reduceIte]
    rw [hown, clkSup_eq_of_isGoodTime (fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path z.1).2.2.2.1 hT)
      (by simpa [Strip.extPath] using (h₁.path z.1).1)
      (A1Ref.exists_continuousOn_extPath_beyond (h₂.path z.2).2.2.2.1 hl.1)
      (by simpa [Strip.extPath] using (h₂.path z.2).1) σ.coe_nonneg
      (g3_isGoodTime_le hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k z.2 hle z.1)]
    exact ENNReal.ofReal_ne_top
  · rw [clkSup_of_nonpos (by simp only [g3SndOwn, hle, ↓reduceIte, le_refl])]
    exact ENNReal.zero_ne_top

/-- **`hgS`**: the cap comparisons are record events. -/
theorem g3Stop_hgS (m k : ℕ) (r : ℝ≥0) :
    MeasurableSet[𝓡 m] ({z | (𝓢) (τ z.2) k z ≤ r} ∩ {z | r < (𝓢) (τ z.2) m z}) := by
  set Tkm : X × Y → ℝ := fun z => if τ z.2 ≤ g3S₂ x y W₂ ζ₂ k z.2 ∧ τ z.2 ≤ g3S₂ x y W₂ ζ₂ m z.2 then
    (min (g3S₁ x y W₁ ζ₁ k z.1) (g3S₁ x y W₁ ζ₁ m z.1) : ℝ) else 0 with hTkm
  set R := g3RecSet x y W₂ VL₂ ζ₂ G₁ G₂ τ m with hR
  -- on the record set, `min(S_k, S_m)` is the record cap at `Tkm`
  have hmin : ∀ z ∈ R, min ((𝓢) (τ z.2) k z) ((𝓢) (τ z.2) m z) =
      capSnd (fun _ _ => True) y W₁ ζ₁ 0 W₂ (g3Sτ x y W₂ ζ₂ τ m) Tkm z := by
    intro z hz
    obtain ⟨h1, h2, hle, hl⟩ := hz
    rw [g3Stop_mask_eq hag₁ hag₂ k h1 h2, g3Stop_mask_eq hag₁ hag₂ m h1 h2]
    unfold g3SndCap
    rw [min_capSnd_eq (fun hl' => g3Stop_fin hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k hl')
      (fun hl' => g3Stop_fin hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m hl'),
      capSnd_true_eq (τ₂ := fun _ => τ z.2) hl (min_eq_left hle)]
    refine capSnd_congr_pt ?_
    simp only [hTkm, g3SndOwn, hle, and_true]
    split_ifs <;> simp
  have hRm := measurableSet_g3RecSet h₂ hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 m
  -- the own time `Tkm` is record-measurable
  have hTm : Measurable[𝓡 m] Tkm := by
    have hE := measurableSet_g3_le_le hs₂ hτ k m
    have hmin₁ : Measurable[(hs₁ m).measurableSpace] fun x' => min (g3S₁ x y W₁ ζ₁ k x') (g3S₁ x y W₁ ζ₁ m x') :=
      (measurable_stop_self ((hs₁ k).min (hs₁ m)) fun x' => by simp only [WithTop.coe_min]).mono
        (((hs₁ k).min (hs₁ m)).measurableSpace_mono (hs₁ m) fun _ => min_le_right _ _) le_rfl
    refine Measurable.ite (p := fun z : X × Y => τ z.2 ≤ g3S₂ x y W₂ ζ₂ k z.2 ∧ τ z.2 ≤ g3S₂ x y W₂ ζ₂ m z.2)
      ?_ ?_ measurable_const
    · exact @measurable_snd X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace _ hE
    · exact (hmin₁.comp (@measurable_fst X Y (hs₁ m).measurableSpace
        (hτ.min (hs₂ m)).measurableSpace)).coe_nnreal_real
  have hTle : ∀ z, 0 < Tkm z → Tkm z ≤ g3S₁ x y W₁ ζ₁ m z.1 := by
    intro z hz
    simp only [hTkm] at hz ⊢
    split_ifs at hz ⊢ with h
    · exact_mod_cast min_le_right _ _
    · exact absurd hz (lt_irrefl 0)
  have hcm := measurable_g3RecCap hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m hTm hTle
  have hSm := g3Stop_hSm hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂ m
  have e : {z | (𝓢) (τ z.2) k z ≤ r} ∩ {z | r < (𝓢) (τ z.2) m z} =
      R ∩ ({z | capSnd (fun _ _ => True) y W₁ ζ₁ 0 W₂ (g3Sτ x y W₂ ζ₂ τ m) Tkm z ≤ r} ∩
        {z | r < (𝓢) (τ z.2) m z}) := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hk, hm⟩
      have hzR : z ∈ R := g3Stop_pos hag₁ hag₂ (zero_le.trans_lt hm)
      refine ⟨hzR, ?_, hm⟩
      rw [← hmin z hzR]
      exact (min_le_left _ _).trans hk
    · rintro ⟨hzR, hk, hm⟩
      refine ⟨?_, hm⟩
      rw [← hmin z hzR] at hk
      rcases min_choice ((𝓢) (τ z.2) k z) ((𝓢) (τ z.2) m z) with h | h
      · rwa [h] at hk
      · rw [h] at hk
        exact absurd (hm.trans_le hk) (lt_irrefl _)
  rw [e]
  exact hRm.inter ((measurableSet_le hcm measurable_const).inter (measurableSet_lt measurable_const hSm))

end Facts

end InteractingSLE.ZhanGT4.A1G3L2
