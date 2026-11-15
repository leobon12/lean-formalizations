/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawSndFam
import InteractingSLE.Spec.ZhanGT4.A1G3LawFstRect

/-!
# Zhan's A.1 under R83, (G3), small-curve direction: the assembly and the record-side inputs

Packet PROVE-A1-G3LAW (R83), the small-direction mirror of `A1G3LawFstRect`:

* **`hasFamilyLawC_g3_of_inputs`**: `G3RectLawSndC`'s conclusion (verbatim, the original marginals) from the concrete
  families `g3SndVL`, `g3SndVR`, `g3SndCap`, `g3SndD` and four named inputs `hD`, `hgeo`, `hlaw`, `hstop`
  (A1-RECTLAW2's `hasFamilyLawC_of_masked`);
* **`measurable_g3SndD`**: the input `hD`, PROVED;
* **`g3Snd_hopt`**: row optional sampling at `τ ∧ S₂ᵐ`; **`g3SndResStop`**: `ResStopInput` from the remaining record
  facts; **`g3Snd_hgζ`**: the record fact `hgζ`, PROVED.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom A1Forces A1MultiMark A1Marg A1Asm A1EightSeed A1RLaw
  A1Law A1Patch A1SeedField A1G3Calc A1Common A1EightFin A1LargeDens

/-! ### The (G3) small-direction family law from its remaining inputs -/

section Assembly

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **`G3RectLawSndC`'s conclusion from the concrete families** (`hasFamilyLawC_of_masked` with the forces `g3SndVL`,
`g3SndVR`, the raw caps `g3SndCap`, the densities `g3SndD`, masked off the good sets `G₁`, `G₂` of the patches).
Proved here: the joint measurability of the canonical driver, the forces and the raw caps, the admissibility of the
initial word and the initial forces. The remaining inputs are named: `hD`, `hgeo` (geometry at good samples with a
positive raw cap), `hlaw` (the one-sample laws at good large samples, raw caps, residual noise) and `hstop`. -/
theorem hasFamilyLawC_g3_of_inputs {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) {P₁ : Measure X}
    {P₂ : Measure Y} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)} [IsProbabilityMeasure μ]
    {𝓕₁ : Filtration ℝ≥0 mX} {𝓕₂ : Filtration ℝ≥0 mY} {W₂ : ℝ≥0 → Y → ℝ} {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ}
    {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞} {W₁ : ℝ≥0 → X → ℝ}
    {VL₁ : Fin 1 → ℝ≥0 → X → ℝ} {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞}
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    {W₂' : ℝ≥0 → Y → ℝ} {ζ₂' : Y → ℝ≥0∞} {W₁' : ℝ≥0 → X → ℝ} {VL₁' : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁' : Fin 3 → ℝ≥0 → X → ℝ} {ζ₁' : X → ℝ≥0∞}
    (hS₁ : ∀ k, Measurable (g3S₁ x y W₁' ζ₁' k)) (hS₂ : ∀ k, Measurable (g3S₂ x y W₂' ζ₂' k))
    {G₁ : Set X} {G₂ : Set Y} (hG₁ : MeasurableSet G₁) (hG₂ : MeasurableSet G₂) (hG₁0 : P₁ G₁ᶜ = 0)
    (hG₂0 : P₂ G₂ᶜ = 0)
    (hD : ∀ k, Measurable fun p : ℝ≥0 × (X × Y) => g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' p.1 k p.2)
    (hgeo : ∀ σ k z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z →
      SeedImageGeometry (![0] : Fin 1 → ℝ) (g3SndWordR W₂ VL₂ σ z.2) (smallG3RhoL κ) (smallG3RhoR κ)
        (fun t => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁'
            W₂' ζ₂' σ k z)) z)
        (fun i t => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun j t => g3SndVR y W₁ ζ₁ W₂ VL₂ ζ₂ σ j (min t (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
            (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z))
    (hlaw : ∀ k, ∀ᵐ y' ∂P₂, y' ∈ G₂ → ∀ σ : ℝ≥0,
      IsSeedSampleLaw (P₁.withDensity fun x' => g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' σ k (x', y'))
        (fun t x' => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) t (x', y'))
        (fun x' => rLife (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) (x', y'))
        (fun i t x' => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x', y')) (fun j t x' => g3SndVR y W₁ ζ₁ W₂ VL₂ ζ₂ σ j t (x',
            y'))
        (fun t x' => seedCapacityNoise (kh κ) (smallG3RhoL κ) (smallG3RhoR κ)
          (fun s => rDrv (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (fun _ => σ) s (x', y'))
          (fun i s => g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x', y')) (fun j s => g3SndVR y W₁ ζ₁ W₂ VL₂ ζ₂ σ j s (x', y')) t)
        (fun k' x' => g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k' (x', y')) k)
    (hstop : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y' => (τ y' : WithTop ℝ≥0)),
      Nonempty (ResStopInput P₁ P₂ μ (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ (g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂) (g3SndVR y W₁ ζ₁
          W₂ VL₂ ζ₂)
        (maskCap G₁ G₂ (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂')) (g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B
            | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawC (kh κ) P₁ P₂ μ 𝓕₂ (fun t ω => Strip.IsStripLife (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω) t) y W₁ ζ₁ 0
      W₂ (fun _ _ => ![0]) (fun t ω => ![0, VL₂ 0 t ω - VL₂ 1 t ω, W₂ t ω - VL₂ 1 t ω]) (smallG3RhoL κ)
      (smallG3RhoR κ) := by
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  obtain ⟨hlive, hlk, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Snd_facts h₁ h₂
  have hm3 := (measurable_rDrv_rLife (live := (g3SndLive W₂ VL₂ ζ₂)) hlive hlk hjc hj0 hkc hk0 hjm hkm hζj hζk y 0).1
  exact hasFamilyLawC_of_masked hk (g3SndVL y W₁ ζ₁ W₂ VL₂ ζ₂) (g3SndVR y W₁ ζ₁ W₂ VL₂ ζ₂) (g3SndCap x y W₁ ζ₁ W₂ VL₂
      ζ₂ W₁' ζ₁' W₂' ζ₂') (g3SndD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') hG₁ hG₂ hG₁0 hG₂0 hm3
    (fun i t => measurable_g3SndVL h₁ h₂ i t) (fun j t => measurable_g3SndVR h₁ h₂ j t)
    (fun k => measurable_g3SndCap h₁ h₂ hS₁ hS₂ k) hD hgeo
    (fun σ y' hl => smallG3_isSeedWord hκ4 hκ8 hyx (h₂.path y') hl)
    (fun σ z _ i => g3SndVL_zero y W₁ ζ₁ W₂ VL₂ ζ₂ σ i z) (fun σ z _ j => g3SndVR_zero y W₁ ζ₁ W₂ VL₂ ζ₂ σ j z)
    hlaw hstop

end Assembly

/-! ### The record-side inputs of the small direction -/

section Rect

variable {X Y : Type} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The densities are jointly measurable** (`hD` of `hasFamilyLawC_g3_of_inputs`): the row `s ↦ M(S₁ᵏ, s ∧ S₂ᵏ)`
is continuous (`IsRectField.row_cont`) and measurable in the sample at each `s` (A1-RECTMEAS's `g3RectMeas`), so
Carathéodory applies. -/
theorem measurable_g3SndD {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    [StandardBorelSpace X] [StandardBorelSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hB₂ : ∀ ω, Continuous (B₂ · ω)) (k : ℕ) :
    Measurable fun p : ℝ≥0 × (X × Y) => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2 := by
  have hR := g3_isRectField hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k (𝓖₁ := 𝓖₁) (𝓖₂ := 𝓖₂)
  have hM := A1RectMeas.g3RectMeas κ hκ4 hκ8 y x hyx hx X Y mX mY inferInstance inferInstance P₁ inferInstance P₂
    inferInstance 𝓖₁ 𝓖₂ inferInstance inferInstance W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ hB₂ h₁ hB₁ hg₁ k
  have hS₁ := measurable_of_isStoppingTime hR.stop₁
  have hS₂ := measurable_of_isStoppingTime hR.stop₂
  set N := seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) k) with hN
  have hu : Measurable (Function.uncurry fun (s : ℝ≥0) (z : X × Y) =>
      N z (g3S₁ x y W₁ ζ₁ k z.1) (min (s : ℝ) (g3S₂ x y W₂ ζ₂ k z.2))) := by
    refine measurable_uncurry_of_continuous_of_measurable
      (fun z => hR.row_cont z.1 z.2 _ (NNReal.coe_nonneg _) le_rfl) fun s => ?_
    exact hM (fun z => (g3S₁ x y W₁ ζ₁ k z.1 : ℝ)) (fun z => min (s : ℝ) (g3S₂ x y W₂ ζ₂ k z.2))
      (hS₁.comp measurable_fst).coe_nnreal_real (measurable_const.min (hS₂.comp measurable_snd).coe_nnreal_real)
      (fun z => NNReal.coe_nonneg _) (fun z => le_min s.coe_nonneg (NNReal.coe_nonneg _))
      (fun z => ⟨(), le_rfl, min_le_right _ _⟩)
  have e : (fun p : ℝ≥0 × (X × Y) => g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2) = fun p =>
      ENNReal.ofReal (Function.uncurry (fun (s : ℝ≥0) (z : X × Y) =>
        N z (g3S₁ x y W₁ ζ₁ k z.1) (min (s : ℝ) (g3S₂ x y W₂ ζ₂ k z.2))) p) := by
    funext p
    simp only [g3SndD, Function.uncurry, hN, NNReal.coe_min]
  rw [e]
  exact hu.ennreal_ofReal

/-- **Optional sampling of the patched G3 rows at `τ ∧ S₂ᵐ`** (`ResStopInput.hopt`, small direction). -/
theorem g3Snd_hopt {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    [StandardBorelSpace X] [StandardBorelSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0))
    {τ : Y → ℝ≥0} (hτ : IsStoppingTime 𝓖₂ fun y' => (τ y' : WithTop ℝ≥0)) (m : ℕ) :
    ∀ᵐ x' ∂P₁, ∀ C, MeasurableSet[(hτ.min (hs₂ m)).measurableSpace] C →
      ∫⁻ y' in C, ENNReal.ofReal (g3M κ x y W₁ VL₁ VR₁ ζ₁ W₂ m (x', y') (g3S₁ x y W₁ ζ₁ m x')
          (g3S₂ x y W₂ ζ₂ m y')) ∂P₂ =
        ∫⁻ y' in C, g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ (τ y') m (x', y') ∂P₂ :=
  IsRectField.opt_snd (g3_isRectField hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m (𝓖₁ := 𝓖₁) (𝓖₂ := 𝓖₂)) hτ

/-- **The per-stop inputs of the small direction from the remaining record facts** (`ResStopInput` for (G3)): the
records are the stopped σ-algebras of the patched exits (`𝓑'` stopped at `τ ∧ S₂ᵐ`), the exit density is the patched
seeded height field at the rectangle corner, (1.7) on the records is the coupling's `RectDens` hypothesis and the
optional sampling is `g3Snd_hopt`. The remaining inputs are the record facts of the caps, forces and image driver. -/
def g3SndResStop {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0)
    [StandardBorelSpace X] [StandardBorelSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂)
    (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
    (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0)) {μ : Measure (X × Y)}
    (hd : ∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
      ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) ω (g3S₁ x y W₁ ζ₁ m ω.1) (g3S₂
          x y W₂ ζ₂ m ω.2)))
    {τ : Y → ℝ≥0} (hτ : IsStoppingTime 𝓖₂ fun y' => (τ y' : WithTop ℝ≥0)) {nL nR : ℕ}
    {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}
    {VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ} {VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ}
    {S : ℝ≥0 → ℕ → X × Y → ℝ≥0} {𝓔 : Set (Set Y)}
    (hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (hs₁ m).measurableSpace
      (hτ.min (hs₂ m)).measurableSpace] fun z => S (τ z.2) m z)
    (hstop : ∀ m (s : ℝ≥0) (C : Set Y), C ∈ 𝓔 →
      MeasurableSet[@Prod.instMeasurableSpace X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace]
        (Prod.snd ⁻¹' C ∩ {z | s < S (τ z.2) m z}))
    (hgW : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hs₁ m).measurableSpace
      (hτ.min (hs₂ m)).measurableSpace] f ∧ ∀ z, r < S (τ z.2) m z → rDrv live xj Wj ζj xk Wk τ r z = f z)
    (hgVL : ∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hs₁ m).measurableSpace
      (hτ.min (hs₂ m)).measurableSpace] f ∧ ∀ z, r < S (τ z.2) m z → VL (τ z.2) i r z = f z)
    (hgVR : ∀ m j r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hs₁ m).measurableSpace
      (hτ.min (hs₂ m)).measurableSpace] f ∧ ∀ z, r < S (τ z.2) m z → VR (τ z.2) j r z = f z)
    (hgS : ∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y (hs₁ m).measurableSpace
      (hτ.min (hs₂ m)).measurableSpace] ({z | S (τ z.2) k z ≤ r} ∩ {z | r < S (τ z.2) m z}))
    (hgζ : ∀ m z, (S (τ z.2) m z : ℝ≥0∞) ≤ rLife live xj Wj ζj xk Wk τ z)
    (hcov : ∀ᵐ z ∂μ, live (τ z.2) z.2 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.1))
        (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) →
      ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) s ≤ S (τ z.2) m z) :
    ResStopInput P₁ P₂ μ live xj Wj ζj xk Wk VL VR S (g3SndD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂) τ 𝓔 where
  𝓐 m := (hs₁ m).measurableSpace
  𝓑 m := (hs₂ m).measurableSpace
  𝓑' m := (hτ.min (hs₂ m)).measurableSpace
  D₀ m ω := ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) ω (g3S₁ x y W₁ ζ₁ m ω.1)
      (g3S₂ x y W₂ ζ₂ m ω.2))
  hA m := (hs₁ m).measurableSpace_le
  hB' m := IsStoppingTime.measurableSpace_mono _ _ fun _ => min_le_right _ _
  hB m := (hs₂ m).measurableSpace_le
  hD₀ m := by
    have hM := A1RectMeas.g3RectMeas κ hκ4 hκ8 y x hyx hx X Y mX mY inferInstance inferInstance P₁ inferInstance P₂
      inferInstance 𝓖₁ 𝓖₂ inferInstance inferInstance W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ hB₂ h₁ hB₁ hg₁ m
    exact (hM (fun ω => (g3S₁ x y W₁ ζ₁ m ω.1 : ℝ)) (fun ω => (g3S₂ x y W₂ ζ₂ m ω.2 : ℝ))
      ((measurable_of_isStoppingTime (hs₁ m)).comp measurable_fst).coe_nnreal_real
      ((measurable_of_isStoppingTime (hs₂ m)).comp measurable_snd).coe_nnreal_real (fun ω => NNReal.coe_nonneg _)
      (fun ω => NNReal.coe_nonneg _) fun ω => ⟨(), le_rfl, le_rfl⟩).ennreal_ofReal
  hrect m A C hA hC := rect_of_rectDens (hs₁ m).measurableSpace_le (hs₂ m).measurableSpace_le (hd m) A C hA hC
  hopt m := g3Snd_hopt hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₂ hτ m
  hSm := hSm
  hstop := hstop
  hgW := hgW
  hgVL := hgVL
  hgVR := hgVR
  hgS := hgS
  hgζ := hgζ
  hcov := hcov

omit mX mY in
/-- **`hgζ` of the small direction**: the masked caps at the stop precede the image lifetime (FORCES's
`capSnd_le_rLife`). -/
theorem g3Snd_hgζ (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ)
    (ζ₂' : Y → ℝ≥0∞) (G₁ : Set X) (G₂ : Set Y) (τ : Y → ℝ≥0) (m : ℕ) (z : X × Y) :
    (maskCap G₁ G₂ (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z : ℝ≥0∞) ≤
      rLife (g3SndLive W₂ VL₂ ζ₂) y W₁ ζ₁ 0 W₂ τ z := by
  have hmask : maskCap G₁ G₂ (g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z ≤
      g3SndCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' (τ z.2) m z := by
    by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [maskCap_of_mem hG.1 hG.2]
    · rw [maskCap_of_not_mem hG]; exact bot_le
  have hcap := A1Forces.capSnd_le_rLife (live := g3SndLive W₂ VL₂ ζ₂) (xj := y) (Wj := W₁) (ζj := ζ₁) (xk := 0)
    (Wk := W₂) (τ := fun _ => τ z.2) (g3SndOwn x y W₁' ζ₁' W₂' ζ₂' (τ z.2) m) z
  have hlife := (cImg_congr_of_eq (z := z) (τ := fun z => τ z.2) (τ₀ := fun _ => τ z.2)
    (live := fun t (z : X × Y) => g3SndLive W₂ VL₂ ζ₂ t z.2) (xj := y) (Wj := fun t (z : X × Y) => W₁ t z.1)
    (ζj := fun z : X × Y => ζ₁ z.1) (xk := 0) (Wk := fun t (z : X × Y) => W₂ t z.2) rfl).1
  refine (ENNReal.coe_le_coe.2 hmask).trans (hcap.trans ?_)
  exact hlife.symm.le

end Rect

end InteractingSLE.ZhanGT4.A1G3Law
