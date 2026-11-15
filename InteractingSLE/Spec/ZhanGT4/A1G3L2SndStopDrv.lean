/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopFacts
import InteractingSLE.Spec.ZhanGT4.A1G3RowSeed

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the record facts of the image driver and the forces

Packet PROVE-A1-G3LAW2. In the setting of `A1G3L2SndStopFacts`:

* **`g3Stop_repl`**: the stopped patched replacement data (small driver stopped at `S₁ᵐ`, large driver stopped at
  `τ ∧ S₂ᵐ`, lifetimes `⊤`) are continuous, start at `0` and are record-measurable;
* **`g3Stop_loc`**: on `{r < cap}` they agree with the original data up to the horizon `S₁ᵐ`, good for both, whose
  clock reaches the cap (A1-FORCES's `hloc`, at the stopped frozen time `τ ∧ S₂ᵐ = τ`);
* **`g3Stop_hgW`**, **`g3Stop_hgVL`**, **`g3Stop_hgVR`**: the record facts of the original canonical image driver and
  of the corrected forces.
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

variable {X Y : Type*} {live : ℝ≥0 → Y → Prop} {xj xk : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞}
  {Wk : ℝ≥0 → Y → ℝ} {τ₁ τ₂ : Y → ℝ≥0} {z : X × Y}

/-- The seed forces read the frozen time only at the sample. -/
theorem rSeedSnd_tau_congr (h : τ₁ z.2 = τ₂ z.2) (sgn : ℝ) (t : ℝ≥0) :
    rSeedSnd live xj Wj ζj xk Wk τ₁ sgn t z = rSeedSnd live xj Wj ζj xk Wk τ₂ sgn t z :=
  canonSeed_congr_pt (L := {w : X × Y | live (τ₁ w.2) w.2}) (L' := {w : X × Y | live (τ₂ w.2) w.2}) (xj := xj)
    (xk := xk) (wj := fun w t => Wj t w.1) (wj' := fun w t => Wj t w.1) (ζj := fun w => ζj w.1)
    (ζj' := fun w => ζj w.1) (wk := fun w t => Wk t w.2) (wk' := fun w t => Wk t w.2) (τ := fun w => τ₁ w.2)
    (τ' := fun w => τ₂ w.2) (ω := z) (by show live (τ₁ z.2) z.2 ↔ live (τ₂ z.2) z.2; rw [h]) rfl rfl rfl h sgn t

/-- The mark forces read the frozen time and the mark only at the sample. -/
theorem rForceSnd_tau_congr {p₁ p₂ : Y → ℝ} (h : τ₁ z.2 = τ₂ z.2) (hp : p₁ z.2 = p₂ z.2) (t : ℝ≥0) :
    rForceSnd live xj Wj ζj xk Wk τ₁ p₁ t z = rForceSnd live xj Wj ζj xk Wk τ₂ p₂ t z :=
  canonForce_congr_pt (L := {w : X × Y | live (τ₁ w.2) w.2}) (L' := {w : X × Y | live (τ₂ w.2) w.2}) (xj := xj)
    (xk := xk) (wj := fun w t => Wj t w.1) (wj' := fun w t => Wj t w.1) (ζj := fun w => ζj w.1)
    (ζj' := fun w => ζj w.1) (wk := fun w t => Wk t w.2) (wk' := fun w t => Wk t w.2) (τ := fun w => τ₁ w.2)
    (τ' := fun w => τ₂ w.2) (p := fun w => p₁ w.2) (p' := fun w => p₂ w.2) (ω := z)
    (by show live (τ₁ z.2) z.2 ↔ live (τ₂ z.2) z.2; rw [h]) rfl rfl rfl h hp t

end Gen

section Drv

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
  (hag₁ : ∀ x' ∈ G₁, (∀ t, W₁o t x' = W₁ t x') ∧ ζ₁o x' = ζ₁ x')
  (hag₂ : ∀ y' ∈ G₂, (∀ t, W₂o t y' = W₂ t y') ∧ (∀ i t, VL₂o i t y' = VL₂ i t y') ∧ ζ₂o y' = ζ₂ y')

/-- The product of the two stopped records of rectangle `m`. -/
local notation "𝓡" m => @Prod.instMeasurableSpace _ _ (IsStoppingTime.measurableSpace (hs₁ m))
  (IsStoppingTime.measurableSpace (IsStoppingTime.min hτ (hs₂ m)))

/-- The masked caps at the stop. -/
local notation "𝓢" => maskCap G₁ G₂ (g3SndCap x y W₁o ζ₁o W₂o VL₂o ζ₂o W₁ ζ₁ W₂ ζ₂)

include hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂

/-- **The stopped replacement data**: continuous (lifetime `⊤`), started at `0`, record-measurable. -/
theorem g3Stop_repl (m : ℕ) :
    (∀ x', ContinuousOn (fun t => W₁ (min t (g3S₁ x y W₁ ζ₁ m x')) x') {t | (t : ℝ≥0∞) < ⊤}) ∧
    (∀ x', W₁ (min 0 (g3S₁ x y W₁ ζ₁ m x')) x' = 0) ∧
    (∀ y', ContinuousOn (fun t => W₂ (min t (g3Sτ x y W₂ ζ₂ τ m y')) y') {t | (t : ℝ≥0∞) < ⊤}) ∧
    (∀ y', W₂ (min 0 (g3Sτ x y W₂ ζ₂ τ m y')) y' = 0) ∧
    (∀ t, Measurable[(hs₁ m).measurableSpace] fun x' => W₁ (min t (g3S₁ x y W₁ ζ₁ m x')) x') ∧
    (∀ t, Measurable[(hτ.min (hs₂ m)).measurableSpace] fun y' => W₂ (min t (g3Sτ x y W₂ ζ₂ τ m y')) y') := by
  obtain ⟨hS₁, -, -, -, hS₂ζ⟩ := g3_rect_facts hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂
  have hτζ : ∀ y', ((g3Sτ x y W₂ ζ₂ τ m y' : ℝ≥0) : ℝ≥0∞) < ζ₂ y' := fun y' =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) (hS₂ζ m y')
  exact ⟨fun x' => (continuous_stopped (h₁.path x').2.2.2.1 (hS₁ m x').1).continuousOn,
    fun x' => by simp only [zero_le, min_eq_left]; exact (h₁.path x').1,
    fun y' => (continuous_stopped (h₂.path y').2.2.2.1 (hτζ y')).continuousOn,
    fun y' => by simp only [zero_le, min_eq_left]; exact (h₂.path y').1,
    fun t => measurable_stopped_at h₁.progW (hs₁ m) t,
    fun t => measurable_stopped_at' h₂.progW (hτ.min (hs₂ m)) (T := g3Sτ x y W₂ ζ₂ τ m)
      (fun y' => by simp only [g3Sτ, WithTop.coe_min]) t⟩

include hag₁ hag₂

omit [MeasurableSpace X] [MeasurableSpace Y] hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ in
/-- On `{r < cap}` the stopped frozen time is the stop. -/
theorem g3Stop_tau_eq {m : ℕ} {r : ℝ≥0} {z : X × Y} (hz : r < (𝓢) (τ z.2) m z) :
    τ z.2 = g3Sτ x y W₂ ζ₂ τ m z.2 :=
  (min_eq_left (g3Stop_pos hag₁ hag₂ (zero_le.trans_lt hz)).2.2.1).symm

/-- **`hloc` of the stopped records**: on `{r < cap}`, at the stopped frozen time `τ ∧ S₂ᵐ`, the original data agree
with the stopped patched data up to the horizon `S₁ᵐ`, good for both, whose clock reaches the cap. -/
theorem g3Stop_loc (m : ℕ) (r : ℝ≥0) (z : X × Y) (hz : r < (𝓢) (τ z.2) m z) :
    g3SndLive W₂o VL₂o ζ₂o (g3Sτ x y W₂ ζ₂ τ m z.2) z.2 ∧ True ∧
    (∀ T : ℝ, ENNReal.ofReal T < ζ₁o z.1 → ContinuousOn (Strip.extPath (W₁o · z.1)) (Icc 0 T)) ∧ W₁o 0 z.1 = 0 ∧
    (∃ τ', ((g3Sτ x y W₂ ζ₂ τ m z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂o · z.2)) (Icc 0 τ')) ∧
    W₂o 0 z.2 = 0 ∧
    A1Ref.IsGoodTime y (Strip.extPath (W₁o · z.1)) (ζ₁o z.1) 0 (Strip.extPath (W₂o · z.2))
      (g3Sτ x y W₂ ζ₂ τ m z.2) (g3S₁ x y W₁ ζ₁ m z.1) ∧
    A1Ref.IsGoodTime y (Strip.extPath fun t => W₁ (min t (g3S₁ x y W₁ ζ₁ m z.1)) z.1) ⊤ 0
      (Strip.extPath fun t => W₂ (min t (g3Sτ x y W₂ ζ₂ τ m z.2)) z.2) (g3Sτ x y W₂ ζ₂ τ m z.2)
      (g3S₁ x y W₁ ζ₁ m z.1) ∧
    (∀ t : ℝ≥0, (t : ℝ) ≤ g3S₁ x y W₁ ζ₁ m z.1 → W₁ (min t (g3S₁ x y W₁ ζ₁ m z.1)) z.1 = W₁o t z.1) ∧
    (∀ t ≤ g3Sτ x y W₂ ζ₂ τ m z.2, W₂ (min t (g3Sτ x y W₂ ζ₂ τ m z.2)) z.2 = W₂o t z.2) ∧
    (((𝓢) (τ z.2) m z : ℝ≥0) : ℝ) ≤ A1Ref.imgClk y (Strip.extPath (W₁o · z.1)) 0 (Strip.extPath (W₂o · z.2))
      (g3Sτ x y W₂ ζ₂ τ m z.2) (g3S₁ x y W₁ ζ₁ m z.1) := by
  have hpos := zero_le.trans_lt hz
  obtain ⟨h1, h2, hle, hl⟩ := g3Stop_pos hag₁ hag₂ hpos
  have hτm : g3Sτ x y W₂ ζ₂ τ m z.2 = τ z.2 := min_eq_left hle
  obtain ⟨hW₁a, hζ₁a⟩ := hag₁ z.1 h1
  obtain ⟨hW₂a, hV₂a, hζ₂a⟩ := hag₂ z.2 h2
  have eW₁ : (W₁o · z.1) = (W₁ · z.1) := funext hW₁a
  have eW₂ : (W₂o · z.2) = (W₂ · z.2) := funext hW₂a
  have eV₂ : (VL₂o 0 · z.2) = (VL₂ 0 · z.2) := funext (hV₂a 0)
  have hlo : g3SndLive W₂o VL₂o ζ₂o (τ z.2) z.2 := by
    simp only [g3SndLive, eW₂, eV₂, hζ₂a]
    exact hl
  have hgood := g3_isGoodTime_le hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m z.2 hle z.1
  have hgood' := g3_isGoodTime_stop hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m z.2 hle z.1
  have hj : ∀ T : ℝ, ENNReal.ofReal T < ζ₁ z.1 → ContinuousOn (Strip.extPath (W₁ · z.1)) (Icc 0 T) :=
    fun T hT => A1Ref.continuousOn_extPath_Icc (h₁.path z.1).2.2.2.1 hT
  have hk : ∃ τ' : ℝ, ((τ z.2 : ℝ≥0) : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (W₂ · z.2)) (Icc 0 τ') :=
    A1Ref.exists_continuousOn_extPath_beyond (h₂.path z.2).2.2.2.1 hl.1
  have hcap : (𝓢) (τ z.2) m z =
      (A1Ref.imgClk y (Strip.extPath (W₁ · z.1)) 0 (Strip.extPath (W₂ · z.2)) (τ z.2)
        (g3S₁ x y W₁ ζ₁ m z.1)).toNNReal := by
    rw [g3Stop_mask_eq hag₁ hag₂ m h1 h2]
    unfold g3SndCap
    rw [capSnd_congr_pt (T' := fun z => (g3S₁ x y W₁ ζ₁ m z.1 : ℝ))
      (by simp only [g3SndOwn, hle, ↓reduceIte])]
    exact capSnd_eq_of_isGoodTime (τ := fun _ => τ z.2) hl hj (h₁.path z.1).1 hk (h₂.path z.2).1 hgood
  rw [hτm]
  refine ⟨hlo, trivial, fun T hT => ?_, by rw [hW₁a]; exact (h₁.path z.1).1, by rw [eW₂]; exact hk,
    by rw [hW₂a]; exact (h₂.path z.2).1, by rw [eW₁, hζ₁a, eW₂]; exact hgood, hgood', fun t ht => ?_,
    fun t ht => by rw [min_eq_left ht, hW₂a], ?_⟩
  · rw [eW₁]
    exact hj T (by rwa [← hζ₁a])
  · rw [min_eq_left (show t ≤ g3S₁ x y W₁ ζ₁ m z.1 by exact_mod_cast ht), hW₁a]
  · rw [hcap, eW₁, eW₂]
    have hp : 0 < (A1Ref.imgClk y (Strip.extPath (W₁ · z.1)) 0 (Strip.extPath (W₂ · z.2)) (τ z.2)
        (g3S₁ x y W₁ ζ₁ m z.1)).toNNReal := by rw [← hcap]; exact hpos
    rw [Real.coe_toNNReal _ (Real.toNNReal_pos.1 hp).le]

/-- **`hgW`**: the original canonical image driver before the cap agrees with a record-measurable function. -/
theorem g3Stop_hgW (m : ℕ) (r : ℝ≥0) : ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧ ∀ z, r < (𝓢) (τ z.2) m z →
    rDrv (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o τ r z = f z := by
  obtain ⟨hjc, hj0, hkc, hk0, hjm, hkm⟩ := g3Stop_repl hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  obtain ⟨f, hf, hfe⟩ := exists_measurable_rDrv_of_stopped (𝓐 := (hs₁ m).measurableSpace)
    (𝓑 := (hτ.min (hs₂ m)).measurableSpace) (live := g3SndLive W₂o VL₂o ζ₂o) (live' := fun _ _ => True)
    (xj := y) (xk := 0) (Wj := W₁o) (Wj' := fun t x' => W₁ (min t (g3S₁ x y W₁ ζ₁ m x')) x') (ζj := ζ₁o)
    (ζj' := fun _ => ⊤) (Wk := W₂o) (Wk' := fun t y' => W₂ (min t (g3Sτ x y W₂ ζ₂ τ m y')) y')
    (ζk' := fun _ => ⊤) (τ := g3Sτ x y W₂ ζ₂ τ m) (cap := fun z => (𝓢) (τ z.2) m z)
    (T := fun z => (g3S₁ x y W₁ ζ₁ m z.1 : ℝ)) (measurable_g3Sτ hs₂ hτ m) MeasurableSet.univ
    (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const r
    (fun z hz => g3Stop_loc hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂ m r z hz)
  refine ⟨f, hf, fun z hz => ?_⟩
  rw [← hfe z hz]
  exact (cImg_congr_of_eq (τ := fun z : X × Y => τ z.2) (τ₀ := fun z : X × Y => g3Sτ x y W₂ ζ₂ τ m z.2)
    (g3Stop_tau_eq hag₁ hag₂ hz)).2 r

/-- **`hgVL`**: the left forces before the cap agree with record-measurable functions. -/
theorem g3Stop_hgVL (m : ℕ) (i : Fin 1) (r : ℝ≥0) : ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧
    ∀ z, r < (𝓢) (τ z.2) m z → g3SndVL y W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) i r z = f z := by
  by_cases hr : r = 0
  · refine ⟨fun _ => 0, measurable_const, fun z _ => ?_⟩
    subst hr
    rw [g3SndVL_zero]
    fin_cases i
    rfl
  obtain ⟨hjc, hj0, hkc, hk0, hjm, hkm⟩ := g3Stop_repl hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  obtain ⟨f, hf, hfe⟩ := A1G3Row.exists_measurable_rSeedSnd_of_stopped (𝓐 := (hs₁ m).measurableSpace)
    (𝓑 := (hτ.min (hs₂ m)).measurableSpace) (live := g3SndLive W₂o VL₂o ζ₂o) (live' := fun _ _ => True)
    (xj := y) (xk := 0) (Wj := W₁o) (Wj' := fun t x' => W₁ (min t (g3S₁ x y W₁ ζ₁ m x')) x') (ζj := ζ₁o)
    (ζj' := fun _ => ⊤) (Wk := W₂o) (Wk' := fun t y' => W₂ (min t (g3Sτ x y W₂ ζ₂ τ m y')) y')
    (ζk' := fun _ => ⊤) (τ := g3Sτ x y W₂ ζ₂ τ m) (cap := fun z => (𝓢) (τ z.2) m z)
    (T := fun z => (g3S₁ x y W₁ ζ₁ m z.1 : ℝ)) (measurable_g3Sτ hs₂ hτ m) MeasurableSet.univ
    (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const (-1) r
    (fun z hz => g3Stop_loc hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂ m r z hz)
  refine ⟨f, hf, fun z hz => ?_⟩
  have hτe := g3Stop_tau_eq hag₁ hag₂ hz
  rw [g3SndVL_of_ne y W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) i hr z, ← hfe z hz]
  exact rSeedSnd_tau_congr (τ₁ := fun _ => τ z.2) hτe (-1) r

/-- **`hgVR`**: the right forces before the cap agree with record-measurable functions. -/
theorem g3Stop_hgVR (m : ℕ) (j : Fin 3) (r : ℝ≥0) : ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧
    ∀ z, r < (𝓢) (τ z.2) m z → g3SndVRc y W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) j r z = f z := by
  have hpv : ∀ (U : ℝ≥0 → Y → ℝ), IsStronglyProgressive (usualAugmentation 𝓕₂ P₂) U →
      Measurable[𝓡 m] fun z : X × Y => U (g3Sτ x y W₂ ζ₂ τ m z.2) z.2 := fun U hU =>
    (measurable_stoppedValue' hU (hτ.min (hs₂ m)) (T := g3Sτ x y W₂ ζ₂ τ m)
      (fun y' => by simp only [g3Sτ, WithTop.coe_min])).comp
      (@measurable_snd X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace)
  by_cases hr : r = 0
  · subst hr
    refine ⟨fun z => g3SndWordR W₂ VL₂ (g3Sτ x y W₂ ζ₂ τ m z.2) z.2 j, ?_, fun z hz => ?_⟩
    · fin_cases j
      · exact measurable_const
      · exact (hpv _ (h₂.progVL 0)).sub (hpv _ (h₂.progVL 1))
      · exact (hpv _ h₂.progW).sub (hpv _ (h₂.progVL 1))
    · obtain ⟨-, h2, -, -⟩ := g3Stop_pos hag₁ hag₂ hz
      obtain ⟨hW₂a, hV₂a, -⟩ := hag₂ z.2 h2
      rw [g3SndVRc_zero]
      show g3SndWordR W₂o VL₂o (τ z.2) z.2 j = g3SndWordR W₂ VL₂ (g3Sτ x y W₂ ζ₂ τ m z.2) z.2 j
      rw [← g3Stop_tau_eq hag₁ hag₂ hz]
      simp only [g3SndWordR, hW₂a, hV₂a]
  obtain ⟨hjc, hj0, hkc, hk0, hjm, hkm⟩ := g3Stop_repl hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hs₂ hτ m
  have hloc := fun z hz => g3Stop_loc hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hag₁ hag₂ (τ := τ) m r z hz
  -- the forces of the marks `x` (left mark `VL₂ 0`) and of the tip `W₂`
  have hforce : ∀ (U Uo : ℝ≥0 → Y → ℝ), IsStronglyProgressive (usualAugmentation 𝓕₂ P₂) U →
      (∀ y' ∈ G₂, ∀ t, Uo t y' = U t y') → ∃ f : X × Y → ℝ, Measurable[𝓡 m] f ∧ ∀ z, r < (𝓢) (τ z.2) m z →
        rForceSnd (g3SndLive W₂o VL₂o ζ₂o) y W₁o ζ₁o 0 W₂o (fun _ => τ z.2) (fun y' => Uo (τ z.2) y') r z =
          f z := by
    intro U Uo hU hUa
    obtain ⟨f, hf, hfe⟩ := exists_measurable_rForceSnd_of_stopped (𝓐 := (hs₁ m).measurableSpace)
      (𝓑 := (hτ.min (hs₂ m)).measurableSpace) (live := g3SndLive W₂o VL₂o ζ₂o) (live' := fun _ _ => True)
      (xj := y) (xk := 0) (Wj := W₁o) (Wj' := fun t x' => W₁ (min t (g3S₁ x y W₁ ζ₁ m x')) x') (ζj := ζ₁o)
      (ζj' := fun _ => ⊤) (Wk := W₂o) (Wk' := fun t y' => W₂ (min t (g3Sτ x y W₂ ζ₂ τ m y')) y')
      (ζk' := fun _ => ⊤) (τ := g3Sτ x y W₂ ζ₂ τ m) (measurable_g3Sτ hs₂ hτ m) MeasurableSet.univ
      (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const
      (p := fun y' => Uo (g3Sτ x y W₂ ζ₂ τ m y') y') (p' := fun y' => U (g3Sτ x y W₂ ζ₂ τ m y') y')
      ((measurable_stoppedValue' hU (hτ.min (hs₂ m)) (T := g3Sτ x y W₂ ζ₂ τ m)
        (fun y' => by simp only [g3Sτ, WithTop.coe_min])))
      (cap := fun z => (𝓢) (τ z.2) m z) (T := fun z => (g3S₁ x y W₁ ζ₁ m z.1 : ℝ)) r hloc
      (fun z hz => (hUa z.2 (g3Stop_pos hag₁ hag₂ (zero_le.trans_lt hz)).2.1 _).symm)
    refine ⟨f, hf, fun z hz => ?_⟩
    have hτe := g3Stop_tau_eq hag₁ hag₂ hz
    rw [← hfe z hz]
    exact rForceSnd_tau_congr (τ₁ := fun _ => τ z.2) (p₁ := fun y' => Uo (τ z.2) y')
      (p₂ := fun y' => Uo (g3Sτ x y W₂ ζ₂ τ m y') y') hτe (by simp only [hτe]) r
  have hU₀ : ∀ y' ∈ G₂, ∀ t, VL₂o 0 t y' = VL₂ 0 t y' := fun y' hy t => (hag₂ y' hy).2.1 0 t
  have hU₁ : ∀ y' ∈ G₂, ∀ t, W₂o t y' = W₂ t y' := fun y' hy t => (hag₂ y' hy).1 t
  fin_cases j
  · obtain ⟨f, hf, hfe⟩ := A1G3Row.exists_measurable_rSeedSnd_of_stopped (𝓐 := (hs₁ m).measurableSpace)
      (𝓑 := (hτ.min (hs₂ m)).measurableSpace) (live := g3SndLive W₂o VL₂o ζ₂o) (live' := fun _ _ => True)
      (xj := y) (xk := 0) (Wj := W₁o) (Wj' := fun t x' => W₁ (min t (g3S₁ x y W₁ ζ₁ m x')) x') (ζj := ζ₁o)
      (ζj' := fun _ => ⊤) (Wk := W₂o) (Wk' := fun t y' => W₂ (min t (g3Sτ x y W₂ ζ₂ τ m y')) y')
      (ζk' := fun _ => ⊤) (τ := g3Sτ x y W₂ ζ₂ τ m) (cap := fun z => (𝓢) (τ z.2) m z)
      (T := fun z => (g3S₁ x y W₁ ζ₁ m z.1 : ℝ)) (measurable_g3Sτ hs₂ hτ m) MeasurableSet.univ
      (fun _ _ _ => ENNReal.coe_lt_top) hjc hj0 hkc hk0 hjm hkm measurable_const measurable_const 1 r hloc
    refine ⟨f, hf, fun z hz => ?_⟩
    have hτe := g3Stop_tau_eq hag₁ hag₂ hz
    rw [g3SndVRc_of_ne y W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) _ hr z]
    exact (rSeedSnd_tau_congr (τ₁ := fun _ => τ z.2) hτe 1 r).trans (hfe z hz)
  · obtain ⟨f, hf, hfe⟩ := hforce (VL₂ 0) (VL₂o 0) (h₂.progVL 0) hU₀
    exact ⟨f, hf, fun z hz => by
      rw [g3SndVRc_of_ne y W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) _ hr z]
      exact hfe z hz⟩
  · obtain ⟨f, hf, hfe⟩ := hforce W₂ W₂o h₂.progW hU₁
    exact ⟨f, hf, fun z hz => by
      rw [g3SndVRc_of_ne y W₁o ζ₁o W₂o VL₂o ζ₂o (τ z.2) _ hr z]
      exact hfe z hz⟩

end Drv

end InteractingSLE.ZhanGT4.A1G3L2
