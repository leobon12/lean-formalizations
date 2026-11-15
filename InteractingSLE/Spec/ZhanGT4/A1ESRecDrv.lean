/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESRecCap
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopDrv

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the record facts of the image driver and the forces

Packet PROVE-A1-EIGHTSNDREC (the (Eight) mirror of PROVE-A1-G3LAW2's `A1G3L2SndStopDrv`). In the setting of
`A1ESRecCap`:

* **`eightStop_repl`**: the stopped patched replacement data (small driver stopped at `S₁ᵐ`, large driver stopped at
  `τ ∧ S₂ᵐ`, lifetimes `⊤`) are continuous, start at `0` and are record-measurable;
* **`eightStop_loc`**: on `{r < cap}` they agree with the original data up to the horizon `S₁ᵐ`, good for both, whose
  clock reaches the cap (A1-FORCES's `hloc`, at the stopped frozen time `τ ∧ S₂ᵐ = τ`);
* **`eightStop_hgW`**, **`eightStop_hgVL`**, **`eightStop_hgVR`**: the record facts of the original canonical image
  driver, of the left seed force and of the right forces (right seed, frozen large tip `W₂(τ)`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESRec

open QuantumZipper (H fwdHull)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1SeedGeom A1G3L2 A1ESnd

section Drv

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  {κ x : ℝ} {P₁ : Measure X} {P₂ : Measure Y} {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ}
  {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ}
  {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
  {W₁o : ℝ≥0 → X → ℝ} {ζ₁o : X → ℝ≥0∞} {W₂o : ℝ≥0 → Y → ℝ} {VL₂o : Fin 1 → ℝ≥0 → Y → ℝ} {ζ₂o : Y → ℝ≥0∞}
  {G₁ : Set X} {G₂ : Set Y} {τ : Y → ℝ≥0}

variable (hκ8 : 8 ≤ κ) (hx : x < 0)
  (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ (usualAugmentation 𝓕₁ P₁)
    W₁ VL₁ VR₁ B₁ ζ₁)
  (hB₁ : ∀ ω, Continuous (B₁ · ω))
  (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
  (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ (usualAugmentation 𝓕₂ P₂) W₂ VL₂ VR₂ B₂ ζ₂)
  (hB₂ : ∀ ω, Continuous (B₂ · ω))
  (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0))
  (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0))
  (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0))
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

/-- The product of the two stopped records of rectangle `m`. -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (hs₁ m))
  (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₂ m)))

/-- The masked caps at the stop. -/
local notation "𝓢" => maskCap G₁ G₂ (eightSndCap x W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂)

include hκ8 hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The stopped replacement data**: continuous (lifetime `⊤`), started at `0`, record-measurable. -/
theorem eightStop_repl (m : ℕ) :
    (∀ x', ContinuousOn (fun t => W₁ (min t (eightS₁ x W₁ ζ₁ m x')) x') {t | (t : ℝ≥0∞) < ⊤}) ∧
    (∀ x', W₁ (min 0 (eightS₁ x W₁ ζ₁ m x')) x' = 0) ∧
    (∀ y', ContinuousOn (fun t => W₂ (min t (eightSτ x W₂ ζ₂ τ m y')) y') {t | (t : ℝ≥0∞) < ⊤}) ∧
    (∀ y', W₂ (min 0 (eightSτ x W₂ ζ₂ τ m y')) y' = 0) ∧
    (∀ t, Measurable[(hs₁ m).measurableSpace] fun x' => W₁ (min t (eightS₁ x W₁ ζ₁ m x')) x') ∧
    (∀ t, Measurable[(hτ.min (hs₂ m)).measurableSpace] fun y' => W₂ (min t (eightSτ x W₂ ζ₂ τ m y')) y') := by
  obtain ⟨hS₁, -, hS₂ζ, -⟩ := eight_rect_facts hκ8 hx h₁ hB₁ hg₁ h₂ hB₂
  have hτζ : ∀ y', ((eightSτ x W₂ ζ₂ τ m y' : ℝ≥0) : ℝ≥0∞) < ζ₂ y' := fun y' =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hS₂ζ m y')
  exact ⟨fun x' => (continuous_stopped (h₁.path x').2.2.2.1 (hS₁ m x').1).continuousOn,
    fun x' => by simp only [zero_le, min_eq_left]; exact (h₁.path x').1,
    fun y' => (continuous_stopped (h₂.path y').2.2.2.1 (hτζ y')).continuousOn,
    fun y' => by simp only [zero_le, min_eq_left]; exact (h₂.path y').1,
    fun t => measurable_stopped_at h₁.progW (hs₁ m) t,
    fun t => measurable_stopped_at' h₂.progW (hτ.min (hs₂ m)) (T := eightSτ x W₂ ζ₂ τ m)
      (fun y' => by simp only [eightSτ, WithTop.coe_min]) t⟩

include hag₁ hag₂

omit [MeasurableSpace X] [MeasurableSpace Y] hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ in
/-- On `{r < cap}` the stopped frozen time is the stop. -/
theorem eightStop_tau_eq {m : ℕ} {r : ℝ≥0} {z : X × Y} (hz : r < (𝓢) (τ z.2) m z) :
    τ z.2 = eightSτ x W₂ ζ₂ τ m z.2 :=
  (min_eq_left (eightStop_pos hag₁ hag₂ (zero_le.trans_lt hz)).2.2.1).symm

/-- **`hloc` of the stopped records**: on `{r < cap}`, at the stopped frozen time `τ ∧ S₂ᵐ`, the original data agree
with the stopped patched data up to the horizon `S₁ᵐ`, good for both, whose clock reaches the cap. -/
theorem eightStop_loc (m : ℕ) (r : ℝ≥0) (z : X × Y) (hz : r < (𝓢) (τ z.2) m z) :
    eightSndLive W₂o VL₂o ζ₂o (eightSτ x W₂ ζ₂ τ m z.2) z.2 ∧ True ∧
    (∀ T : ℝ, ENNReal.ofReal T < ζ₁o z.1 → ContinuousOn (Strip.extPath (W₁o · z.1)) (Icc 0 T)) ∧ W₁o 0 z.1 = 0 ∧
    (∃ τ', ((eightSτ x W₂ ζ₂ τ m z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂o · z.2)) (Icc 0 τ')) ∧
    W₂o 0 z.2 = 0 ∧
    A1Ref.IsGoodTime x (Strip.extPath (W₁o · z.1)) (ζ₁o z.1) 0 (Strip.extPath (W₂o · z.2))
      (eightSτ x W₂ ζ₂ τ m z.2) (eightS₁ x W₁ ζ₁ m z.1) ∧
    A1Ref.IsGoodTime x (Strip.extPath fun t => W₁ (min t (eightS₁ x W₁ ζ₁ m z.1)) z.1) ⊤ 0
      (Strip.extPath fun t => W₂ (min t (eightSτ x W₂ ζ₂ τ m z.2)) z.2) (eightSτ x W₂ ζ₂ τ m z.2)
      (eightS₁ x W₁ ζ₁ m z.1) ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ eightS₁ x W₁ ζ₁ m z.1 → W₁ (min t (eightS₁ x W₁ ζ₁ m z.1)) z.1 = W₁o t z.1) ∧
    (∀ t ≤ eightSτ x W₂ ζ₂ τ m z.2, W₂ (min t (eightSτ x W₂ ζ₂ τ m z.2)) z.2 = W₂o t z.2) ∧
    (((𝓢) (τ z.2) m z : ℝ≥0) : ℝ) ≤ A1Ref.imgClk x (Strip.extPath (W₁o · z.1)) 0 (Strip.extPath (W₂o · z.2))
      (eightSτ x W₂ ζ₂ τ m z.2) (eightS₁ x W₁ ζ₁ m z.1) := by
  have hpos := zero_le.trans_lt hz
  obtain ⟨h1, h2, hle, hl⟩ := eightStop_pos hag₁ hag₂ hpos
  have hτm : eightSτ x W₂ ζ₂ τ m z.2 = τ z.2 := min_eq_left hle
  obtain ⟨hW₁a, hζ₁a⟩ := hag₁ z.1 h1
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ z.2 h2
  have eW₁ : (W₁o · z.1) = (W₁ · z.1) := funext hW₁a
  have eW₂ : (W₂o · z.2) = (W₂ · z.2) := funext hW₂a
  have eV₂ : (VL₂o 0 · z.2) = (VL₂ 0 · z.2) := funext (hV₂a 0)
  have hlo : eightSndLive W₂o VL₂o ζ₂o (τ z.2) z.2 := by
    simp only [eightSndLive, eW₂, eV₂, hζ₂a]
    exact hl
  have hgood := eight_isGoodTime_le hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m z.2 hle z.1
  have hgood' := eight_isGoodTime_stop hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m z.2 hle z.1
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ z.1 → ContinuousOn (Strip.extPath (W₁ · z.1)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path z.1).2.2.2.1 hT
  have hk : ∃ τ' : ℝ, ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂ · z.2)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (h₂.path z.2).2.2.2.1 hl.1
  have hcap : (𝓢) (τ z.2) m z =
      (A1Ref.imgClk x (Strip.extPath (W₁ · z.1)) 0 (Strip.extPath (W₂ · z.2)) (τ z.2)
        (eightS₁ x W₁ ζ₁ m z.1)).toNNReal := by
    rw [eightStop_mask_eq hag₁ hag₂ m h1 h2]
    unfold eightSndCap
    rw [capSnd_congr_pt (T' := fun z => (eightS₁ x W₁ ζ₁ m z.1 : ℝ))
      (by simp only [eightSndOwn, hle, ↓reduceIte])]
    exact capSnd_eq_of_isGoodTime (τ := fun _ => τ z.2) hl hj (h₁.path z.1).1 hk (h₂.path z.2).1 hgood
  rw [hτm]
  refine ⟨hlo, trivial, fun T hT => ?_, by rw [hW₁a]; exact (h₁.path z.1).1, by rw [eW₂]; exact hk,
    by rw [hW₂a]; exact (h₂.path z.2).1, by rw [eW₁, hζ₁a, eW₂]; exact hgood, hgood', fun t ht => ?_,
    fun t ht => by rw [min_eq_left ht, hW₂a], ?_⟩
  · rw [eW₁]
    exact hj T (by rwa [← hζ₁a])
  · rw [min_eq_left (show t ≤ eightS₁ x W₁ ζ₁ m z.1 by exact_mod_cast ht), hW₁a]
  · rw [hcap, eW₁, eW₂]
    have hp : 0 < (A1Ref.imgClk x (Strip.extPath (W₁ · z.1)) 0 (Strip.extPath (W₂ · z.2)) (τ z.2)
        (eightS₁ x W₁ ζ₁ m z.1)).toNNReal := by rw [← hcap]; exact hpos
    rw [Real.coe_toNNReal _ (Real.toNNReal_pos.1 hp).le]

/-- **`hgW`**: the original canonical image driver before the cap agrees with a record-measurable function. -/
theorem eightStop_hgW (m : ℕ) (r : ℝ≥0) : ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧ ∀ z, r < (𝓢) (τ z.2) m z →
    rDrv (eightSndLive W₂o VL₂o ζ₂o) x W₁o ζ₁o 0 W₂o τ r z = f z := by
  obtain ⟨hjc, hj0, hkc, hk0, hjm, hkm⟩ := eightStop_repl hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  obtain ⟨f, hf, hfe⟩ := exists_measurable_rDrv_of_stopped (𝓐 := (hs₁ m).measurableSpace)
    (𝓑 := (hτ.min (hs₂ m)).measurableSpace) (live := eightSndLive W₂o VL₂o ζ₂o) (live' := fun _ _ => True)
    (xj := x) (xk := 0) (Wj := W₁o) (Wj' := fun t x' => W₁ (min t (eightS₁ x W₁ ζ₁ m x')) x') (ζj := ζ₁o)
    (ζj' := fun _ => ⊤) (Wk := W₂o) (Wk' := fun t y' => W₂ (min t (eightSτ x W₂ ζ₂ τ m y')) y')
    (ζk' := fun _ => ⊤) (τ := eightSτ x W₂ ζ₂ τ m) (cap := fun z => (𝓢) (τ z.2) m z)
    (T := fun z => (eightS₁ x W₁ ζ₁ m z.1 : ℝ)) (measurable_eightSτ hs₂ hτ m) MeasurableSet.univ
    (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const r
    (fun z hz => eightStop_loc hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂ m r z hz)
  refine ⟨f, hf, fun z hz => ?_⟩
  rw [← hfe z hz]
  exact (cImg_congr_of_eq (τ := fun z : X × Y => τ z.2) (τ₀ := fun z : X × Y => eightSτ x W₂ ζ₂ τ m z.2)
    (eightStop_tau_eq hag₁ hag₂ hz)).2 r

/-- **`hgVL`**: the left (seed) force before the cap agrees with a record-measurable function. -/
theorem eightStop_hgVL (m : ℕ) (i : Fin 1) (r : ℝ≥0) : ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧
    ∀ z, r < (𝓢) (τ z.2) m z → eightSndVL x W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) i r z = f z := by
  by_cases hr : r = 0
  · refine ⟨fun _ => 0, measurable_const, fun z _ => ?_⟩
    subst hr
    rw [eightSndVL_zero]
    fin_cases i
    rfl
  obtain ⟨hjc, hj0, hkc, hk0, hjm, hkm⟩ := eightStop_repl hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  obtain ⟨f, hf, hfe⟩ := A1G3Row.exists_measurable_rSeedSnd_of_stopped (𝓐 := (hs₁ m).measurableSpace)
    (𝓑 := (hτ.min (hs₂ m)).measurableSpace) (live := eightSndLive W₂o VL₂o ζ₂o) (live' := fun _ _ => True)
    (xj := x) (xk := 0) (Wj := W₁o) (Wj' := fun t x' => W₁ (min t (eightS₁ x W₁ ζ₁ m x')) x') (ζj := ζ₁o)
    (ζj' := fun _ => ⊤) (Wk := W₂o) (Wk' := fun t y' => W₂ (min t (eightSτ x W₂ ζ₂ τ m y')) y')
    (ζk' := fun _ => ⊤) (τ := eightSτ x W₂ ζ₂ τ m) (cap := fun z => (𝓢) (τ z.2) m z)
    (T := fun z => (eightS₁ x W₁ ζ₁ m z.1 : ℝ)) (measurable_eightSτ hs₂ hτ m) MeasurableSet.univ
    (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const (-1) r
    (fun z hz => eightStop_loc hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂ m r z hz)
  refine ⟨f, hf, fun z hz => ?_⟩
  have hτe := eightStop_tau_eq hag₁ hag₂ hz
  rw [eightSndVL_of_ne x W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) i hr z, ← hfe z hz]
  exact rSeedSnd_tau_congr (τ₁ := fun _ => τ z.2) hτe (-1) r

/-- **`hgVR`**: the right forces (right seed, frozen large tip) before the cap agree with record-measurable
functions. -/
theorem eightStop_hgVR (m : ℕ) (j : Fin 2) (r : ℝ≥0) : ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧
    ∀ z, r < (𝓢) (τ z.2) m z → eightSndVR x W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) j r z = f z := by
  have hpv : ∀ (U : ℝ≥0 → Y → ℝ), IsStronglyProgressive (usualAugmentation 𝓕₂ P₂) U →
      Measurable[𝓡 m] fun z : X × Y => U (eightSτ x W₂ ζ₂ τ m z.2) z.2 := fun U hU =>
    (measurable_stoppedValue' hU (hτ.min (hs₂ m)) (T := eightSτ x W₂ ζ₂ τ m)
      (fun y' => by simp only [eightSτ, WithTop.coe_min])).comp
      (@measurable_snd X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace)
  by_cases hr : r = 0
  · subst hr
    refine ⟨fun z => eightSndWordR W₂ VL₂ (eightSτ x W₂ ζ₂ τ m z.2) z.2 j, ?_, fun z hz => ?_⟩
    · fin_cases j
      · exact measurable_const
      · exact (hpv _ h₂.progW).sub (hpv _ (h₂.progVL 0))
    · obtain ⟨-, h2, -, -⟩ := eightStop_pos hag₁ hag₂ hz
      obtain ⟨hW₂a, hV₂a, -⟩ := hag₂ z.2 h2
      rw [eightSndVR_zero]
      show eightSndWordR W₂o VL₂o (τ z.2) z.2 j = eightSndWordR W₂ VL₂ (eightSτ x W₂ ζ₂ τ m z.2) z.2 j
      rw [← eightStop_tau_eq hag₁ hag₂ hz]
      simp only [eightSndWordR, hW₂a, hV₂a]
  obtain ⟨hjc, hj0, hkc, hk0, hjm, hkm⟩ := eightStop_repl hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  have hloc := fun z hz => eightStop_loc hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂ (τ := τ) m r z hz
  fin_cases j
  · -- the right seed force
    obtain ⟨f, hf, hfe⟩ := A1G3Row.exists_measurable_rSeedSnd_of_stopped (𝓐 := (hs₁ m).measurableSpace)
      (𝓑 := (hτ.min (hs₂ m)).measurableSpace) (live := eightSndLive W₂o VL₂o ζ₂o) (live' := fun _ _ => True)
      (xj := x) (xk := 0) (Wj := W₁o) (Wj' := fun t x' => W₁ (min t (eightS₁ x W₁ ζ₁ m x')) x') (ζj := ζ₁o)
      (ζj' := fun _ => ⊤) (Wk := W₂o) (Wk' := fun t y' => W₂ (min t (eightSτ x W₂ ζ₂ τ m y')) y')
      (ζk' := fun _ => ⊤) (τ := eightSτ x W₂ ζ₂ τ m) (cap := fun z => (𝓢) (τ z.2) m z)
      (T := fun z => (eightS₁ x W₁ ζ₁ m z.1 : ℝ)) (measurable_eightSτ hs₂ hτ m) MeasurableSet.univ
      (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const 1 r hloc
    refine ⟨f, hf, fun z hz => ?_⟩
    have hτe := eightStop_tau_eq hag₁ hag₂ hz
    rw [eightSndVR_of_ne x W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) _ hr z]
    exact (rSeedSnd_tau_congr (τ₁ := fun _ => τ z.2) hτe 1 r).trans (hfe z hz)
  · -- the force of the frozen large tip `W₂(τ)`
    obtain ⟨f, hf, hfe⟩ := exists_measurable_rForceSnd_of_stopped (𝓐 := (hs₁ m).measurableSpace)
      (𝓑 := (hτ.min (hs₂ m)).measurableSpace) (live := eightSndLive W₂o VL₂o ζ₂o) (live' := fun _ _ => True)
      (xj := x) (xk := 0) (Wj := W₁o) (Wj' := fun t x' => W₁ (min t (eightS₁ x W₁ ζ₁ m x')) x') (ζj := ζ₁o)
      (ζj' := fun _ => ⊤) (Wk := W₂o) (Wk' := fun t y' => W₂ (min t (eightSτ x W₂ ζ₂ τ m y')) y')
      (ζk' := fun _ => ⊤) (τ := eightSτ x W₂ ζ₂ τ m) (measurable_eightSτ hs₂ hτ m) MeasurableSet.univ
      (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const
      (p := fun y' => W₂o (eightSτ x W₂ ζ₂ τ m y') y') (p' := fun y' => W₂ (eightSτ x W₂ ζ₂ τ m y') y')
      ((measurable_stoppedValue' h₂.progW (hτ.min (hs₂ m)) (T := eightSτ x W₂ ζ₂ τ m)
        (fun y' => by simp only [eightSτ, WithTop.coe_min])))
      (cap := fun z => (𝓢) (τ z.2) m z) (T := fun z => (eightS₁ x W₁ ζ₁ m z.1 : ℝ)) r hloc
      (fun z hz => ((hag₂ z.2 (eightStop_pos hag₁ hag₂ (zero_le.trans_lt hz)).2.1).1 _).symm)
    refine ⟨f, hf, fun z hz => ?_⟩
    have hτe := eightStop_tau_eq hag₁ hag₂ hz
    rw [eightSndVR_of_ne x W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) _ hr z, ← hfe z hz]
    exact rForceSnd_tau_congr (τ₁ := fun _ => τ z.2) (p₁ := fun y' => W₂o (τ z.2) y')
      (p₂ := fun y' => W₂o (eightSτ x W₂ ζ₂ τ m y') y') hτe (by simp only [hτe]) r

end Drv

end InteractingSLE.ZhanGT4.A1ESRec
