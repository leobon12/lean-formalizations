/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawFstFam
import InteractingSLE.Spec.ZhanGT4.A1LargeDensSeed

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the concrete families and the assembly

Packet PROVE-A1-G3LAW (R83). The data of `G3RectLawSndC`'s family law (image curve the small curve on `X`,
conditioning curve the large curve on `Y`, frozen time `σ` of the large curve), the mirror of the large direction
(`A1G3LawFstFam`) and of A1-RECTLAW2's design (its "What remains" B.2–B.4):

* **`g3SndWordR`**: the initial right image word `![0, V_x − V_y, W − V_y]` (right seed, image of `x`, large tip,
  relative to the image `V_y` of the small curve's start); the left word is `![0]`;
* **`g3SndVL`**, **`g3SndVR`**: the image forces — the initial word at time `0`, then A1-LARGEDENS's canonical seed
  forces `rSeedSnd (∓1)` for the seeds and FORCES's canonical forces `rForceSnd` of the frozen-chart marks
  `−y + V_x(σ)`, `−y + W(σ)`;
* **`g3SndOwn`**, **`g3SndCap`**: the raw caps — FORCES's `capSnd` at the small curve's rectangle exit `g3S₁`, gated by
  the protection `σ ≤ g3S₂` of the frozen large curve;
* **`g3SndD`**: the rectangle density at the stop, `M(S₁ᵏ, σ ∧ S₂ᵏ)` of the patched G3 records;
* measurability, initial values, admissibility (`smallG3_isSeedWord`);
* **`hasFamilyLawC_g3_of_inputs`**: `G3RectLawSndC`'s conclusion (verbatim, the original marginals) from four named
  inputs `hD`, `hgeo`, `hlaw`, `hstop` (A1-RECTLAW2's `hasFamilyLawC_of_masked`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open A2X A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom A1Forces A1MultiMark A1Marg A1Asm A1EightSeed A1RLaw
  A1G3Calc A1LargeDens

/-! ### The concrete families -/

section Fam

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The live event of the small direction: the large curve frozen at `σ` before its strip lifetime. -/
abbrev g3SndLive (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) : ℝ≥0 → Y → Prop :=
  fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t

/-- **The (G3) small direction's initial right image word** at the frozen time `σ` (`G3RectLawSndC`'s `ΘR`). -/
def g3SndWordR (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (σ : ℝ≥0) (y' : Y) : Fin 3 → ℝ :=
  ![0, VL₂ 0 σ y' - VL₂ 1 σ y', W₂ σ y' - VL₂ 1 σ y']

/-- **The (G3) small direction's left image force**: `0` at time `0`, the canonical left seed force afterwards. -/
def g3SndVL (y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (_i : Fin 1) (t : ℝ≥0) (z : X × Y) : ℝ :=
  if t = 0 then 0 else rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (-1) t z

/-- **The (G3) small direction's right image forces**: the initial word at time `0`; afterwards the canonical right
seed force and the canonical forces of the frozen-chart marks `−y + V_x(σ)` (image of `x`) and `−y + W(σ)` (tip). -/
def g3SndVR (y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (j : Fin 3) (t : ℝ≥0) (z : X × Y) : ℝ :=
  if t = 0 then g3SndWordR W₂ VL₂ σ z.2 j else
    ![rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) 1 t z,
      rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (fun y' => (0 - y) + VL₂ 0 σ y') t z,
      rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (fun y' => (0 - y) + W₂ σ y') t z] j

/-- **The image curve's own time of the raw cap `k`**: the small curve's rectangle exit when the frozen large curve is
protected (`σ ≤ g3S₂ᵏ`), `0` otherwise (patched records). -/
def g3SndOwn (x y : ℝ) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0)
    (k : ℕ) (z : X × Y) : ℝ :=
  if σ ≤ g3S₂ x y W₂' ζ₂' k z.2 then (g3S₁ x y W₁' ζ₁' k z.1 : ℝ) else 0

/-- **The raw caps** of the (G3) small direction: the image capacity (`capSnd`) at the own time `g3SndOwn`. -/
def g3SndCap (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0)
    (k : ℕ) : X × Y → ℝ≥0 :=
  capSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (g3SndOwn x y W₁' ζ₁' W₂' ζ₂' σ k)

/-- **The rectangle densities at the stop**: `M(S₁ᵏ, σ ∧ S₂ᵏ)` of the patched G3 records. -/
def g3SndD (κ x y : ℝ) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 3 → ℝ≥0 → X → ℝ)
    (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ) (ζ₂' : Y → ℝ≥0∞) (σ : ℝ≥0) (k : ℕ) (z : X × Y) : ℝ≥0∞ :=
  ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁' VL₁' VR₁' W₂' (g3S₁ x y W₁' ζ₁') k) z
    (g3S₁ x y W₁' ζ₁' k z.1) (min σ (g3S₂ x y W₂' ζ₂' k z.2) : ℝ≥0))

omit mX mY in
theorem g3SndVL_zero (y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (i : Fin 1) (z : X × Y) :
    g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i 0 z = (![0] : Fin 1 → ℝ) i := by
  fin_cases i
  simp only [g3SndVL, ↓reduceIte]
  rfl

omit mX mY in
theorem g3SndVR_zero (y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (j : Fin 3) (z : X × Y) :
    g3SndVR y W₁ ζ₁ W₂ VL₂ ζ₂ σ j 0 z = g3SndWordR W₂ VL₂ σ z.2 j := by
  simp only [g3SndVR, ↓reduceIte]

end Fam

/-! ### Measurability -/

section Meas

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

variable {κ x y : ℝ} {P₁ : Measure X} {𝓕₁ : Filtration ℝ≥0 mX} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {P₂ : Measure Y} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
  {ζ₂ : Y → ℝ≥0∞}

/-- The standing pathwise and measurability facts of the two regular G3 marginals for the small direction. -/
theorem g3Snd_facts
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) :
    MeasurableSet {q : ℝ≥0 × Y | g3SndLive W₂ VL₂ ζ₂ q.1 q.2} ∧
    (∀ s y', g3SndLive W₂ VL₂ ζ₂ s y' → (s : ℝ≥0∞) < ζ₂ y') ∧
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
theorem measurable_g3SndVL
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (i : Fin 1) (t : ℝ≥0) :
    Measurable fun p : ℝ≥0 × (X × Y) => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ p.1 i t p.2 := by
  by_cases ht : t = 0
  · simp only [g3SndVL, ht, ↓reduceIte]
    exact measurable_const
  · have e : (fun p : ℝ≥0 × (X × Y) => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ p.1 i t p.2) = fun p =>
        rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => p.1) (-1) t p.2 :=
      funext fun p => by unfold g3SndVL; exact ite_eq_right_of_eq_false _ _ (eq_false ht)
    rw [e]
    obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Snd_facts h₁ h₂
    exact measurable_rSeedSnd (live := g3SndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
      hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0 (-1) t

/-- **The right forces are jointly measurable in the frozen time and the sample.** -/
theorem measurable_g3SndVR
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (j : Fin 3) (t : ℝ≥0) :
    Measurable fun p : ℝ≥0 × (X × Y) => g3SndVR y W₁ ζ₁ W₂ VL₂ ζ₂ p.1 j t p.2 := by
  have hW := measurable_uncurry_of_isStronglyProgressive h₂.progW
  have hL := fun i => measurable_uncurry_of_isStronglyProgressive (h₂.progVL i)
  have hπ : Measurable fun p : ℝ≥0 × (X × Y) => (p.1, p.2.2) := measurable_fst.prodMk measurable_snd.snd
  obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Snd_facts h₁ h₂
  by_cases ht : t = 0
  · simp only [g3SndVR, ht, ↓reduceIte, g3SndWordR]
    fin_cases j
    · exact measurable_const
    · exact ((hL 0).comp hπ).sub ((hL 1).comp hπ)
    · exact (hW.comp hπ).sub ((hL 1).comp hπ)
  · have e : (fun p : ℝ≥0 × (X × Y) => g3SndVR y W₁ ζ₁ W₂ VL₂ ζ₂ p.1 j t p.2) = fun p =>
        ![rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => p.1) 1 t p.2,
          rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => p.1) (fun y' => (0 - y) + VL₂ 0 p.1 y') t p.2,
          rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => p.1) (fun y' => (0 - y) + W₂ p.1 y') t p.2] j :=
      funext fun p => by unfold g3SndVR; exact ite_eq_right_of_eq_false _ _ (eq_false ht)
    rw [e]
    fin_cases j
    · exact measurable_rSeedSnd (live := g3SndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
        hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0 1 t
    · exact measurable_rForceSnd (live := g3SndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
        (p := fun σ y' => (0 - y) + VL₂ 0 σ y') hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0
        (measurable_const.add (hL 0)) t
    · exact measurable_rForceSnd (live := g3SndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
        (p := fun σ y' => (0 - y) + W₂ σ y') hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0
        (measurable_const.add hW) t

/-- **The raw caps are jointly measurable in the frozen time and the sample.** -/
theorem measurable_g3SndCap {W₁' : ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞} {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hS₁ : ∀ k, Measurable (g3S₁ x y W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (g3S₂ x y W₂' ζ₂' k)) (k : ℕ) :
    Measurable fun p : ℝ≥0 × (X × Y) => g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' p.1 k p.2 := by
  obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Snd_facts h₁ h₂
  have hT : Measurable fun q : ℝ≥0 × (X × Y) => g3SndOwn x y W₁' ζ₁' W₂' ζ₂' q.1 k q.2 :=
    Measurable.ite (measurableSet_le measurable_fst ((hS₂ k).comp measurable_snd.snd))
      ((hS₁ k).comp measurable_snd.fst).coe_nnreal_real measurable_const
  unfold g3SndCap
  exact measurable_capSnd (live := g3SndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂) (xj := y)
    (xk := 0) (T := fun σ => g3SndOwn x y W₁' ζ₁' W₂' ζ₂' σ k) hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk hT

end Meas

end InteractingSLE.ZhanGT4.A1G3Law
