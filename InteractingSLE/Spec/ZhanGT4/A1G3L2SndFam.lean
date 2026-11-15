/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawSndRect
import InteractingSLE.Spec.ZhanGT4.A1G3L2Shared

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the corrected right forces and the assembly from masked laws

Packet PROVE-A1-G3LAW2. **Frame correction.** The canonical image processes of the small direction
(`rDrv … y W₁ ζ₁ 0 W₂ …`, image start `xj = y`, conditioning start `xk = 0`) live in the common frame of the two
curves (`A1Ref.imgDrv` reads `physHull y (W₁) ·` and `physMap 0 (W₂) σ`): the image of a frozen-chart point is
`g̃_t(p) − g̃_0`, with `p` the **physical** point. The frozen-chart marks of the small image word are the image
`g_σ(x) = V_x(σ)` of the ordinary mark and the frozen tip `W(σ)` (the right word `g3SndWordR` is
`![0, V_x(σ) − V_y(σ), W(σ) − V_y(σ)]`, relative to the image start `g_σ(y) = V_y(σ)`). PROVE-A1-G3LAW's `g3SndVR`
reads them at `−y + V_x(σ)`, `−y + W(σ)` (the large direction's convention `xk − xj + ·`, correct only for
`xj = 0`), which differ from the word by `−y ≠ 0`; its forces are not continuous at time `0` and the geometry input of
`hasFamilyLawC_g3_of_inputs` cannot hold for them. Here:

* **`g3SndVRc`**: the right forces with the physical frozen-chart marks `V_x(σ)`, `W(σ)`;
* `g3SndVRc_zero`, `measurable_g3SndVRc`;
* **`hasFamilyLawC_g3_of_inputsC`**: `G3RectLawSndC`'s conclusion from `hD`, `hgeo` (for `g3SndVRc`), the one-sample
  laws with the **masked** caps (`hasFamilyLawC_of_maskedLaw`) and `hstop`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open A2X A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom A1Forces A1MultiMark A1Marg A1Asm A1EightSeed A1RLaw
  A1G3Calc A1LargeDens A1G3Law

section Fam

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The (G3) small direction's right image forces, physical frame**: the initial word at time `0`; afterwards the
canonical right seed force and the canonical forces of the frozen-chart marks `V_x(σ)` (image of `x`) and `W(σ)` (the
frozen tip). -/
def g3SndVRc (y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (j : Fin 3) (t : ℝ≥0) (z : X × Y) : ℝ :=
  if t = 0 then g3SndWordR W₂ VL₂ σ z.2 j else
    ![rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) 1 t z,
      rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (fun y' => VL₂ 0 σ y') t z,
      rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (fun y' => W₂ σ y') t z] j

omit mX mY in
theorem g3SndVRc_zero (y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (j : Fin 3) (z : X × Y) :
    g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j 0 z = g3SndWordR W₂ VL₂ σ z.2 j := by
  simp only [g3SndVRc, ↓reduceIte]

omit mX mY in
theorem g3SndVRc_of_ne (y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (j : Fin 3) {t : ℝ≥0} (ht : t ≠ 0) (z : X × Y) :
    g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j t z =
      ![rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) 1 t z,
        rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (fun y' => VL₂ 0 σ y') t z,
        rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (fun y' => W₂ σ y') t z] j := by
  unfold g3SndVRc
  exact ite_eq_right_of_eq_false _ _ (eq_false ht)

omit mX mY in
theorem g3SndVL_of_ne (y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ)
    (ζ₂ : Y → ℝ≥0∞) (σ : ℝ≥0) (i : Fin 1) {t : ℝ≥0} (ht : t ≠ 0) (z : X × Y) :
    g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i t z = rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (-1) t z := by
  unfold g3SndVL
  exact ite_eq_right_of_eq_false _ _ (eq_false ht)

end Fam

section Meas

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

variable {κ x y : ℝ} {P₁ : Measure X} {𝓕₁ : Filtration ℝ≥0 mX} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {P₂ : Measure Y} {𝓕₂ : Filtration ℝ≥0 mY}
  {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ}
  {ζ₂ : Y → ℝ≥0∞}

/-- **The corrected right forces are jointly measurable in the frozen time and the sample.** -/
theorem measurable_g3SndVRc
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂) (j : Fin 3) (t : ℝ≥0) :
    Measurable fun p : ℝ≥0 × (X × Y) => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ p.1 j t p.2 := by
  have hW := measurable_uncurry_of_isStronglyProgressive h₂.progW
  have hL := fun i => measurable_uncurry_of_isStronglyProgressive (h₂.progVL i)
  have hπ : Measurable fun p : ℝ≥0 × (X × Y) => (p.1, p.2.2) := measurable_fst.prodMk measurable_snd.snd
  obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Snd_facts h₁ h₂
  by_cases ht : t = 0
  · simp only [g3SndVRc, ht, ↓reduceIte, g3SndWordR]
    fin_cases j
    · exact measurable_const
    · exact ((hL 0).comp hπ).sub ((hL 1).comp hπ)
    · exact (hW.comp hπ).sub ((hL 1).comp hπ)
  · have e : (fun p : ℝ≥0 × (X × Y) => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ p.1 j t p.2) = fun p =>
        ![rSeedSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => p.1) 1 t p.2,
          rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => p.1) (fun y' => VL₂ 0 p.1 y') t p.2,
          rForceSnd (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => p.1) (fun y' => W₂ p.1 y') t p.2] j :=
      funext fun p => g3SndVRc_of_ne y W₁ ζ₁ W₂ VL₂ ζ₂ p.1 j ht p.2
    rw [e]
    fin_cases j
    · exact measurable_rSeedSnd (live := g3SndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
        hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0 1 t
    · exact measurable_rForceSnd (live := g3SndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
        (p := fun σ y' => VL₂ 0 σ y') hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0 (hL 0) t
    · exact measurable_rForceSnd (live := g3SndLive W₂ VL₂ ζ₂) (Wj := W₁) (ζj := ζ₁) (Wk := W₂) (ζk := ζ₂)
        (p := fun σ y' => W₂ σ y') hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0 hW t

end Meas

/-! ### The assembly from masked-cap laws -/

section Assembly

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **`G3RectLawSndC`'s conclusion from the concrete families with the corrected right forces** (`hasFamilyLawC_of_
maskedLaw` with `g3SndVL`, `g3SndVRc`, the raw caps `g3SndCap` masked off `G₁ × G₂`, the densities `g3SndD`). Inputs:
`hD`, `hgeo` (geometry at good samples with a positive raw cap), `hlaw` (the one-sample laws at good large samples with
the masked caps) and `hstop`. -/
theorem hasFamilyLawC_g3_of_inputsC {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) {P₁ : Measure X}
    {P₂ : Measure Y} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)} [IsProbabilityMeasure μ]
    {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁' : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (hS₁ : ∀ k, Measurable (g3S₁ x y W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (g3S₂ x y W₂' ζ₂' k))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₂0 : P₂ G₂ᶜ = 0)
    (hD : ∀ k, Measurable fun p : ℝ≥0 × (X × Y) => g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' p.1 k p.2)
    (hgeo : ∀ σ k z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z →
      SeedImageGeometry (![0] : Fin 1 → ℝ) (g3SndWordR W₂ VL₂ σ z.2) (smallG3RhoL κ) (smallG3RhoR κ)
        (fun t => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁'
            W₂' ζ₂' σ k z)) z)
        (fun i t => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun j t => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
            (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z))
    (hlaw : ∀ k, ∀ᵐ y' ∂P₂, y' ∈ G₂ → ∀ σ : ℝ≥0,
      IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' σ k (x', y'))
        (fun t x' => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) t (x', y'))
        (fun x' => rLife (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (x', y'))
        (fun i t x' => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x', y'))
        (fun j t x' => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x', y'))
        (fun t x' => seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
          (fun s => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) s (x', y'))
          (fun i s => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x', y'))
          (fun j s => g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂ σ j s (x', y')) t)
        (fun k' x' => maskCap G₁ G₂ (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') σ k' (x', y')) k)
    (hstop : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0)),
      Nonempty (ResStopInput P₁ P₂ μ (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂)
        (g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂) (maskCap G₁ G₂ (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
      W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
      (smallG3RhoR κ) := by
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Snd_facts h₁ h₂
  have hm3 := (measurable_rDrv_rLife (live := (g3SndLive W₂ VL₂ ζ₂)) hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0).1
  exact hasFamilyLawC_of_maskedLaw hk (g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂) (g3SndVRc y W₁ ζ₁ W₂ VL₂ ζ₂)
    (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') hG₁ hG₂ hG₂0 hm3
    (fun i t => measurable_g3SndVL h₁ h₂ i t) (fun j t => measurable_g3SndVRc h₁ h₂ j t)
    (fun k => measurable_g3SndCap h₁ h₂ hS₁ hS₂ k) hD hgeo
    (fun σ y' hl => smallG3_isSeedWord hκ4 hκ8 hyx (h₂.path y') hl)
    (fun σ z _ i => g3SndVL_zero y W₁ ζ₁ W₂ VL₂ ζ₂ σ i z) (fun σ z _ j => g3SndVRc_zero y W₁ ζ₁ W₂ VL₂ ζ₂ σ j z)
    hlaw hstop

end Assembly

end InteractingSLE.ZhanGT4.A1G3L2
