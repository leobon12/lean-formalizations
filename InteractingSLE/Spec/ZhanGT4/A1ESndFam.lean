/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ELawSnd
import InteractingSLE.Spec.ZhanGT4.A1RLawEightFam
import InteractingSLE.Spec.ZhanGT4.A1LargeDensSeed
import InteractingSLE.Spec.ZhanGT4.A1G3L2Shared
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomWord

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the concrete families and the assembly

Packet PROVE-A1-EIGHTSND. The data of `EightRectLawSndC`'s family law (image curve the small curve on `X`, started at
`x` in the common physical frame; conditioning curve the large curve on `Y`, started at `0`, frozen at `σ`), the mirror
of PROVE-A1-G3LAW2's corrected G3 families (`A1G3L2SndFam`):

* **`eightSndWordR`**: the initial right image word `![0, W(σ) − V(σ)]` (right seed `x⁺`, large tip, relative to the
  image `V(σ) = g_σ(x)` of the small source); the left word is `![0]` (seed `x⁻`);
* **`eightSndVL`**, **`eightSndVR`**: the image forces — the initial word at time `0`, then A1-LARGEDENS's canonical
  seed forces `rSeedSnd (∓1)` and FORCES's canonical force `rForceSnd` of the frozen tip at its **physical** point
  `W(σ)` (the canonical image lives in the common frame, see `A1G3L2SndFam`);
* **`eightSndOwn`**, **`eightSndCap`**: the raw caps — `capSnd` at the small curve's rectangle exit `eightS₁`, gated by
  the protection `σ ≤ eightS₂` of the frozen large curve;
* **`eightSndD`**: the rectangle densities at the stop, `M(S₁ᵏ, σ ∧ S₂ᵏ)` of the patched Eight records;
* measurability (`measurable_eightSndVL`, `measurable_eightSndVR`, `measurable_eightSndCap`, `measurable_eightSndD`);
* **`hasFamilyLawC_eight_of_inputs`**: `EightRectLawSndC`'s conclusion from `hD`, `hgeo`, the one-sample laws with
  the masked caps (`hasFamilyLawC_of_maskedLaw`) and `hstop`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESnd

open A2X A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom A1Forces A1MultiMark A1Marg A1Asm A1EightSeed A1RLaw
  A1G3Calc A1LargeDens A1G3L2 A1Common

section Fam

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The live event of the small direction: the large curve frozen at `σ` before its strip lifetime. -/
abbrev eightSndLive (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) : ℝ≥0 → Y → Prop :=
  fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t

/-- **The (Eight) small direction's initial right image word** at the frozen time `σ` (`EightRectLawSndC`'s
`ΘR`). -/
def eightSndWordR (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (σ : ℝ≥0) (y' : Y) : Fin 2 → ℝ :=
  ![0, W₂ σ y' - VL₂ 0 σ y']

/-- **The (Eight) small direction's left image force**: `0` at time `0`, the canonical left seed force afterwards. -/
def eightSndVL (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (_i : Fin 1) (t : ℝ≥0) (z : X × Y) : ℝ :=
  if t = 0 then 0 else rSeedSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) (-1) t z

/-- **The (Eight) small direction's right image forces, physical frame**: the initial word at time `0`; afterwards the
canonical right seed force and the canonical force of the frozen tip `W(σ)`. -/
def eightSndVR (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (j : Fin 2) (t : ℝ≥0) (z : X × Y) : ℝ :=
  if t = 0 then eightSndWordR W₂ VL₂ σ z.2 j else
    ![rSeedSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) 1 t z,
      rForceSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) (fun y' => W₂ σ y') t z] j

/-- **The image curve's own time of the raw cap `k`**: the small curve's rectangle exit when the frozen large curve is
protected (`σ ≤ eightS₂ᵏ`), `0` otherwise (patched records). -/
def eightSndOwn (x : ℝ) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0)
    (k : ℕ) (z : X × Y) : ℝ :=
  if σ ≤ eightS₂ x W₂' ζ₂' k z.2 then (eightS₁ x W₁' ζ₁' k z.1 : ℝ) else 0

/-- **The raw caps** of the (Eight) small direction: the image capacity (`capSnd`) at the own time `eightSndOwn`. -/
def eightSndCap (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0)
    (k : ℕ) : X × Y → ℝ≥0 :=
  capSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) (eightSndOwn x W₁' ζ₁' W₂' ζ₂' σ k)

/-- **The rectangle densities at the stop**: `M(S₁ᵏ, σ ∧ S₂ᵏ)` of the patched Eight records. -/
def eightSndD (κ x : ℝ) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 2 → ℝ≥0 → X → ℝ)
    (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0) (k : ℕ) (z : X × Y) : ℝ≥0∞ :=
  ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁' VL₁' VR₁' W₂' (eightS₁ x W₁' ζ₁') k) z
    (eightS₁ x W₁' ζ₁' k z.1) (min σ (eightS₂ x W₂' ζ₂' k z.2) : ℝ≥0))

omit mX mY in
theorem eightSndVL_zero (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (i : Fin 1) (z : X × Y) :
    eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i 0 z = (![0] : Fin 1 → ℝ) i := by
  fin_cases i
  simp only [eightSndVL, ↓reduceIte]
  rfl

omit mX mY in
theorem eightSndVR_zero (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (j : Fin 2) (z : X × Y) :
    eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j 0 z = eightSndWordR W₂ VL₂ σ z.2 j := by
  simp only [eightSndVR, ↓reduceIte]

omit mX mY in
theorem eightSndVL_of_ne (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (i : Fin 1) {t : ℝ≥0} (ht : t ≠ 0) (z : X × Y) :
    eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i t z =
      rSeedSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) (-1) t z := by
  unfold eightSndVL
  exact ite_eq_right_of_eq_false _ _ (eq_false ht)

omit mX mY in
theorem eightSndVR_of_ne (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (j : Fin 2) {t : ℝ≥0} (ht : t ≠ 0) (z : X × Y) :
    eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j t z =
      ![rSeedSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) 1 t z,
        rForceSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) (fun y' => W₂ σ y') t z] j := by
  unfold eightSndVR
  exact ite_eq_right_of_eq_false _ _ (eq_false ht)

end Fam

/-! ### Measurability -/

section Meas

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

variable {κ x : ℝ} {P₁ : Measure X} {𝓕₁ : Filtration ℝ≥0 mX} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {P₂ : Measure Y} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
  {ζ₂ : Y → ℝ≥0∞}

/-- The standing pathwise and measurability facts of the two regular Eight marginals for the small direction. -/
theorem eightSnd_facts
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    MeasurableSet {q : ℝ≥0 × Y | eightSndLive W₂ VL₂ ζ₂ q.1 q.2} ∧
    (∀ s y', eightSndLive W₂ VL₂ ζ₂ s y' → (s : ℝ≥0∞) < ζ₂ y') ∧
    (∀ x', ContinuousOn (W₁ · x') {t | (t : ℝ≥0∞) < ζ₁ x'}) ∧ (∀ x', W₁ 0 x' = 0) ∧
    (∀ y', ContinuousOn (W₂ · y') {t | (t : ℝ≥0∞) < ζ₂ y'}) ∧ (∀ y', W₂ 0 y' = 0) ∧
    (∀ t, Measurable (W₁ t)) ∧ (∀ t, Measurable (W₂ t)) ∧ Measurable ζ₁ ∧ Measurable ζ₂ := by
  have hcW : ∀ y', ContinuousOn (W₂ · y') {s | (s : ℝ≥0∞) < ζ₂ y'} := fun y' => (h₂.path y').2.2.2.1
  have hcV : ∀ y', ContinuousOn (VL₂ 0 · y') {s | (s : ℝ≥0∞) < ζ₂ y'} := fun y' => (h₂.path y').2.2.2.2.1 0
  have hS := measurableSet_live_of_isStronglyProgressive
    (isStronglyProgressive_indicator_isStripLife h₂.evol.2.1 h₂.progW (h₂.progVL 0) hcW hcV)
  exact ⟨hS, fun s y' h => h.1, fun x' => (h₁.path x').2.2.2.1, fun x' => (h₁.path x').1, hcW,
    fun y' => (h₂.path y').1, measurable_of_isStronglyProgressive h₁.progW,
    measurable_of_isStronglyProgressive h₂.progW, measurable_lifetime h₁.evol.2.1, measurable_lifetime h₂.evol.2.1⟩

/-- **The left force is jointly measurable in the frozen time and the sample.** -/
theorem measurable_eightSndVL
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (i : Fin 1) (t : ℝ≥0) :
    Measurable fun p : ℝ≥0 × (X × Y) => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ p.1 i t p.2 := by
  by_cases ht : t = 0
  · simp only [eightSndVL, ht, ↓reduceIte]
    exact measurable_const
  · have e : (fun p : ℝ≥0 × (X × Y) => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ p.1 i t p.2) = fun p =>
        rSeedSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => p.1) (-1) t p.2 :=
      funext fun p => eightSndVL_of_ne x W₁ ζ₁ W₂ VL₂ ζ₂ p.1 i ht p.2
    rw [e]
    obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := eightSnd_facts h₁ h₂
    exact measurable_rSeedSnd (live := eightSndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
      hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk x 0 (-1) t

/-- **The right forces are jointly measurable in the frozen time and the sample.** -/
theorem measurable_eightSndVR
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (j : Fin 2) (t : ℝ≥0) :
    Measurable fun p : ℝ≥0 × (X × Y) => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ p.1 j t p.2 := by
  have hW := measurable_uncurry_of_isStronglyProgressive h₂.progW
  have hL := fun i => measurable_uncurry_of_isStronglyProgressive (h₂.progVL i)
  have hπ : Measurable fun p : ℝ≥0 × (X × Y) => (p.1, p.2.2) := measurable_fst.prodMk measurable_snd.snd
  obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := eightSnd_facts h₁ h₂
  by_cases ht : t = 0
  · simp only [eightSndVR, ht, ↓reduceIte, eightSndWordR]
    fin_cases j
    · exact measurable_const
    · exact (hW.comp hπ).sub ((hL 0).comp hπ)
  · have e : (fun p : ℝ≥0 × (X × Y) => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ p.1 j t p.2) = fun p =>
        ![rSeedSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => p.1) 1 t p.2,
          rForceSnd (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => p.1) (fun y' => W₂ p.1 y') t p.2] j :=
      funext fun p => eightSndVR_of_ne x W₁ ζ₁ W₂ VL₂ ζ₂ p.1 j ht p.2
    rw [e]
    fin_cases j
    · exact measurable_rSeedSnd (live := eightSndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
        hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk x 0 1 t
    · exact measurable_rForceSnd (live := eightSndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
        (p := fun σ y' => W₂ σ y') hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk x 0 hW t

/-- **The raw caps are jointly measurable in the frozen time and the sample.** -/
theorem measurable_eightSndCap {W₁' : ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞} {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hS₁ : ∀ k, Measurable (eightS₁ x W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (eightS₂ x W₂' ζ₂' k)) (k : ℕ) :
    Measurable fun p : ℝ≥0 × (X × Y) => eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' p.1 k p.2 := by
  obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := eightSnd_facts h₁ h₂
  have hT : Measurable fun q : ℝ≥0 × (X × Y) => eightSndOwn x W₁' ζ₁' W₂' ζ₂' q.1 k q.2 :=
    Measurable.ite (measurableSet_le measurable_fst ((hS₂ k).comp measurable_snd.snd))
      ((hS₁ k).comp measurable_snd.fst).coe_nnreal_real measurable_const
  unfold eightSndCap
  exact measurable_capSnd (live := eightSndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂) (xj := x)
    (xk := 0) (T := fun σ => eightSndOwn x W₁' ζ₁' W₂' ζ₂' σ k) hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk hT

/-- **The densities are jointly measurable in the frozen time and the sample** (`hD`; the patched marginals, row
continuity of the rectangle field). -/
theorem measurable_eightSndD (hκ8 : 8 ≤ κ) (hx : x < 0) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    [𝓕₁.IsRightContinuous] [𝓕₂.IsRightContinuous]
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) (k : ℕ) :
    Measurable fun p : ℝ≥0 × (X × Y) => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2 := by
  have hR := eight_patched_isRectField hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k (𝓖₁ := 𝓕₁) (𝓖₂ := 𝓕₂)
  have hM := isFieldMeas_eight_of_patched hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ k
  have hS₁ := measurable_of_isStoppingTime hR.stop₁
  have hS₂ := measurable_of_isStoppingTime hR.stop₂
  set N := seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) k) with hN
  have hu : Measurable (Function.uncurry fun (s : ℝ≥0) (z : X × Y) =>
      N z (eightS₁ x W₁ ζ₁ k z.1) (min (s : ℝ) (eightS₂ x W₂ ζ₂ k z.2))) := by
    refine measurable_uncurry_of_continuous_of_measurable
      (fun z => hR.row_cont z.1 z.2 _ (NNReal.coe_nonneg _) le_rfl) fun s => ?_
    exact hM (fun z => (eightS₁ x W₁ ζ₁ k z.1 : ℝ)) (fun z => min (s : ℝ) (eightS₂ x W₂ ζ₂ k z.2))
      (hS₁.comp measurable_fst).coe_nnreal_real (measurable_const.min (hS₂.comp measurable_snd).coe_nnreal_real)
      (fun z => NNReal.coe_nonneg _) (fun z => le_min s.coe_nonneg (NNReal.coe_nonneg _))
      (fun z => ⟨(), le_rfl, min_le_right _ _⟩)
  have e : (fun p : ℝ≥0 × (X × Y) => eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2) = fun p =>
      ENNReal.ofReal (Function.uncurry (fun (s : ℝ≥0) (z : X × Y) =>
        N z (eightS₁ x W₁ ζ₁ k z.1) (min (s : ℝ) (eightS₂ x W₂ ζ₂ k z.2))) p) := by
    funext p
    simp only [eightSndD, Function.uncurry, hN, NNReal.coe_min]
  rw [e]
  exact hu.ennreal_ofReal

end Meas

/-! ### The assembly from masked-cap laws -/

section Assembly

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **`EightRectLawSndC`'s conclusion from the concrete families** (`hasFamilyLawC_of_maskedLaw` with `eightSndVL`,
`eightSndVR`, the raw caps `eightSndCap` masked off `G₁ × G₂`, the densities `eightSndD`). Inputs: `hD`, `hgeo`
(geometry at good samples with a positive raw cap), `hlaw` (the one-sample laws at good large samples with the masked
caps) and `hstop`. -/
theorem hasFamilyLawC_eight_of_inputs {κ x : ℝ} (hκ8 : 8 ≤ κ) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)} [IsProbabilityMeasure μ]
    {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁' : Fin 2 → ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (hS₁ : ∀ k, Measurable (eightS₁ x W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (eightS₂ x W₂' ζ₂' k))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₂0 : P₂ G₂ᶜ = 0)
    (hD : ∀ k, Measurable fun p : ℝ≥0 × (X × Y) => eightSndD κ x W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' p.1 k p.2)
    (hgeo : ∀ σ k z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z →
      SeedImageGeometry (![0] : Fin 1 → ℝ) (eightSndWordR W₂ VL₂ σ z.2) (smallEightRhoL κ) (smallEightRhoR κ)
        (fun t => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ)
          (min t (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun i t => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i (min t (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun j t => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j (min t (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z))
    (hlaw : ∀ k, ∀ᵐ y' ∂P₂, y' ∈ G₂ → ∀ σ : ℝ≥0,
      IsSeedSampleLaw (P₁.withDensity fun x' => eightSndD κ x W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' σ k (x', y'))
        (fun t x' => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) t (x', y'))
        (fun x' => rLife (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) (x', y'))
        (fun i t x' => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x', y'))
        (fun j t x' => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x', y'))
        (fun t x' => seedCapacityNoise (kh κ) (smallEightRhoL κ) (smallEightRhoR κ)
          (fun s => rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (fun _ => σ) s (x', y'))
          (fun i s => eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x', y'))
          (fun j s => eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ σ j s (x', y')) t)
        (fun k' x' => maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') σ k' (x', y')) k)
    (hstop : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0)),
      Nonempty (ResStopInput P₁ P₂ μ (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ (eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂)
        (eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂) (maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (eightSndD κ x W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) x W₁ ζ₁ 0
      W₂ (fun _ _ => ![0]) (fun t ω => ![0, W₂ t ω - VL₂ 0 t ω]) (smallEightRhoL κ) (smallEightRhoR κ) := by
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := eightSnd_facts h₁ h₂
  have hm3 := (measurable_rDrv_rLife (live := eightSndLive W₂ VL₂ ζ₂) hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk
    x 0).1
  exact hasFamilyLawC_of_maskedLaw hk (eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂) (eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂)
    (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (eightSndD κ x W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') hG₁ hG₂ hG₂0 hm3
    (fun i t => measurable_eightSndVL h₁ h₂ i t) (fun j t => measurable_eightSndVR h₁ h₂ j t)
    (fun k => measurable_eightSndCap h₁ h₂ hS₁ hS₂ k) hD hgeo
    (fun σ y' hl => smallEight_isSeedWord (W := (W₂ · y')) (VL := fun i t => VL₂ i t y') hκ8 hl)
    (fun σ z _ i => eightSndVL_zero x W₁ ζ₁ W₂ VL₂ ζ₂ σ i z) (fun σ z _ j => eightSndVR_zero x W₁ ζ₁ W₂ VL₂ ζ₂ σ j z)
    hlaw hstop

end Assembly

end InteractingSLE.ZhanGT4.A1ESnd
