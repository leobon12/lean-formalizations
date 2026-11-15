/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3LawFstFam
import InteractingSLE.Spec.ZhanGT4.A1RLawEightRect
import InteractingSLE.Spec.ZhanGT4.A1RectMeasG3

/-!
# Zhan's A.1 under R83, (G3), large-curve direction: the assembly and the record-side inputs

Packet PROVE-A1-G3LAW (R83), mirroring A1-RECTLAW2's (Eight) `A1RLawEightFam`/`A1RLawEightRect`:

* **`hasFamilyLawFstC_g3_of_inputs`**: `G3RectLawFstC`'s conclusion (verbatim, the original marginals) from the concrete
  families and four named inputs `hD`, `hgeo`, `hlaw`, `hstop` (A1-RECTLAW2's `hasFamilyLawFstC_of_masked`);
* **`measurable_g3FstD`**: the input `hD` (joint measurability of the densities), PROVED;
* **`g3Fst_hopt`**: column optional sampling at `τ ∧ S₁ᵐ`; **`g3FstResStop`**: `ResStopInputFst` from the remaining
  record facts; **`g3Fst_hgζ`**: the record fact `hgζ`, PROVED.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Law

open QuantumZipper (H fwdMap fwdHull)
open A2X A1Canon A1Ref A1Core A1Frozen A1Family A1SeedGeom A1Forces A1MultiMark A1Marg A1Asm A1EightSeed A1RLaw
  A1Law A1Patch A1SeedField A1G3Calc A1Common A1EightFin

/-! ### The (G3) large-direction family law from its remaining inputs -/

section Assembly

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **`G3RectLawFstC`'s conclusion from the concrete families** (`hasFamilyLawFstC_of_masked` with the forces
`g3FstVL`, the raw caps `g3FstCap`, the densities `g3FstD`, masked off the good sets `G₁`, `G₂` of the
patches). Proved here: the joint measurability of the canonical driver, the forces and the raw caps, the admissibility
of the initial word and the initial forces. The remaining inputs are named: `hD` (the densities), `hgeo` (the geometry
at good samples with a positive raw cap), `hlaw` (the one-sample laws at good small samples, with the raw caps and the
residual as the noise) and `hstop` (the per-stop record inputs). -/
theorem hasFamilyLawFstC_g3_of_inputs {κ x y : ℝ} (hκ : 0 < κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {μ : Measure (X × Y)} [IsProbabilityMeasure μ]
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
    (hD : ∀ k, Measurable fun p : ℝ≥0 × (X × Y) => g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' p.1 k p.2)
    (hgeo : ∀ σ k z, z.1 ∈ G₁ → z.2 ∈ G₂ → 0 < g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z →
      SeedImageGeometry (g3FstWord W₁ VL₁ VR₁ σ z.1) ![] (largeG3ImgRhoL κ) ![]
        (fun t => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y
          W₁ (fun _ => σ) (min t (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun i t => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i
          (min t (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z)) z)
        (fun j _ => (j.elim0 : ℝ)) (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k z))
    (hlaw : ∀ k, ∀ᵐ x' ∂P₁, x' ∈ G₁ → ∀ σ : ℝ≥0,
      IsSeedSampleLaw (P₂.withDensity fun y' => g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂' σ k (x', y'))
        (fun t y' => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y
          W₁ (fun _ => σ) t (x', y'))
        (fun y' => rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y
          W₁ (fun _ => σ) (x', y'))
        (fun i t y' => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i t (x', y')) (fun j _ _ => (j.elim0 : ℝ))
        (fun t y' => seedCapacityNoise κ (largeG3ImgRhoL κ) ![]
          (fun s => rDrvFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω))
            y W₁ (fun _ => σ) s (x', y'))
          (fun i s => g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i s (x', y')) (fun j _ => (j.elim0 : ℝ)) t)
        (fun k' y' => g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' σ k' (x', y')) k)
    (hstop : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (ResStopInputFst P₁ P₂ μ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
        (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ (g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂)
        (fun _ j _ _ => (j.elim0 : ℝ)) (maskCap G₁ G₂ (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂'))
        (g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawFstC κ P₁ P₂ μ 𝓕₁ (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂
      (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁
      (fun t ω => ![VR₁ 1 t ω - VR₁ 2 t ω, VR₁ 0 t ω - VR₁ 2 t ω, W₁ t ω - VR₁ 2 t ω, VL₁ 0 t ω - VR₁ 2 t ω])
      (fun _ _ => ![]) (largeG3ImgRhoL κ) ![] := by
  obtain ⟨hlive, hjc, hj0, hkc, hk0, hjm, hkm, hζj, hζk⟩ := g3Fst_facts h₁ h₂
  have hm3 := (measurable_rDrvFst_rLifeFst (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) hlive (fun _ _ h => h) hjc hj0
    hkc hk0 hjm hkm hζj hζk 0 y).1
  exact hasFamilyLawFstC_of_masked hκ (g3FstVL y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂) (fun _ j _ _ => (j.elim0 : ℝ))
    (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (g3FstD κ x y W₁' VL₁' VR₁' ζ₁' W₂' ζ₂') hG₁ hG₂ hG₁0 hG₂0
    hm3 (fun i t => measurable_g3FstVL h₁ h₂ i t) (fun j => j.elim0)
    (fun k => measurable_g3FstCap h₁ h₂ hS₁ hS₂ k) hD hgeo
    (fun σ x' hσ => isSeedWord_g3FstWord hx h₁.path σ x' hσ)
    (fun σ z _ i => g3FstVL_zero y W₁ VL₁ VR₁ ζ₁ W₂ VL₂ ζ₂ σ i z) (fun _ _ _ j => j.elim0) hlaw hstop

end Assembly

/-! ### The record-side inputs -/

section Rect

variable {X Y : Type} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The large direction's densities are jointly measurable** in the frozen time and the sample (input `hD` of
`hasFamilyLawFstC_g3_of_inputs`): the column `s ↦ M(s ∧ S₁ᵏ, S₂ᵏ)` is continuous (`IsRectField.col_cont`) and
measurable in the sample at each `s` (A1-RECTMEAS's `g3RectMeas`), so Carathéodory applies. -/
theorem measurable_g3FstD {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0) [StandardBorelSpace X]
    [StandardBorelSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω)) (k :
        ℕ) :
    Measurable fun p : ℝ≥0 × (X × Y) => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2 := by
  have hR := g3_isRectField hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ k (𝓖₁ := 𝓖₁) (𝓖₂ := 𝓖₂)
  have hM := A1RectMeas.g3RectMeas κ hκ4 hκ8 y x hyx hx X Y mX mY inferInstance inferInstance P₁ inferInstance P₂
    inferInstance 𝓖₁ 𝓖₂ inferInstance inferInstance W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ hB₂ h₁ hB₁ hg₁ k
  have hS₁ := measurable_of_isStoppingTime hR.stop₁
  have hS₂ := measurable_of_isStoppingTime hR.stop₂
  set N := seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) k) with hN
  have hu : Measurable (Function.uncurry fun (s : ℝ≥0) (z : X × Y) =>
      N z (min (s : ℝ) (g3S₁ x y W₁ ζ₁ k z.1)) (g3S₂ x y W₂ ζ₂ k z.2)) := by
    refine measurable_uncurry_of_continuous_of_measurable (fun z => hR.col_cont z.1 z.2) fun s => ?_
    exact hM (fun z => min (s : ℝ) (g3S₁ x y W₁ ζ₁ k z.1)) (fun z => (g3S₂ x y W₂ ζ₂ k z.2 : ℝ))
      (measurable_const.min (hS₁.comp measurable_fst).coe_nnreal_real)
      (hS₂.comp measurable_snd).coe_nnreal_real (fun z => le_min s.coe_nonneg (NNReal.coe_nonneg _))
      (fun z => NNReal.coe_nonneg _) (fun z => ⟨(), min_le_right _ _, le_rfl⟩)
  have e : (fun p : ℝ≥0 × (X × Y) => g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ p.1 k p.2) = fun p =>
      ENNReal.ofReal (Function.uncurry (fun (s : ℝ≥0) (z : X × Y) =>
        N z (min (s : ℝ) (g3S₁ x y W₁ ζ₁ k z.1)) (g3S₂ x y W₂ ζ₂ k z.2)) p) := by
    funext p
    simp only [g3FstD, Function.uncurry, hN, NNReal.coe_min]
  rw [e]
  exact hu.ennreal_ofReal

/-- **Optional sampling of the patched G3 columns at `τ ∧ S₁ᵏ`** (`ResStopInputFst.hopt`, large direction): for every
stopping time `τ` of the small curve's (right-continuous) filtration, almost every large sample `y` and every event `A`
of the σ-algebra stopped at `τ ∧ S₁ᵏ`, the exit density and the family density at the stop have the same integral
over `A`. -/
theorem g3Fst_hopt {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0) [StandardBorelSpace X]
    [StandardBorelSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
    {τ : X → ℝ≥0} (hτ : IsStoppingTime 𝓖₁ fun x' => (τ x' : WithTop ℝ≥0)) (m : ℕ) :
    ∀ᵐ y' ∂P₂, ∀ A, MeasurableSet[(hτ.min (hs₁ m)).measurableSpace] A →
      ∫⁻ x' in A, ENNReal.ofReal (g3M κ x y W₁ VL₁ VR₁ ζ₁ W₂ m (x', y') (g3S₁ x y W₁ ζ₁ m x')
          (g3S₂ x y W₂ ζ₂ m y')) ∂P₁ =
        ∫⁻ x' in A, g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂ (τ x') m (x', y') ∂P₁ :=
  IsRectField.opt_fst (g3_isRectField hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ m (𝓖₁ := 𝓖₁) (𝓖₂ := 𝓖₂)) hτ

/-- **The per-stop inputs of the large direction from the remaining record facts** (`ResStopInputFst` for (G3)):
the records are the stopped σ-algebras of the patched exits (`𝓐'` stopped at `τ ∧ S₁ᵐ`), the exit density is the
patched seeded height field at the rectangle corner, (1.7) on the records is the coupling's `RectDens` hypothesis and
the optional sampling is `g3Fst_hopt`. The caps `S`, forces `VL`, `VR` and image data are arbitrary; their record
facts (`hSm`, `hstop`, `hgW`, `hgVL`, `hgVR`, `hgS`, `hgζ`) and the clock exhaustion `hcov` are the remaining
inputs. -/
def g3FstResStop {κ x y : ℝ} (hκ4 : 4 < κ) (hκ8 : κ < 8) (hyx : y < x) (hx : x < 0) [StandardBorelSpace X]
    [StandardBorelSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 2 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallG3 (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x, y] ![] ![κ - 4, -4] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0))
    (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0)) {μ : Measure (X × Y)}
    (hd : ∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
      ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) ω
        (g3S₁ x y W₁ ζ₁ m ω.1) (g3S₂ x y W₂ ζ₂ m ω.2)))
    {τ : X → ℝ≥0} (hτ : IsStoppingTime 𝓖₁ fun x => (τ x : WithTop ℝ≥0)) {nL nR : ℕ}
    {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}
    {VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ} {VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ} {S : ℝ≥0 → ℕ → X × Y → ℝ≥0}
    {𝓔 : Set (Set X)}
    (hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] fun z => S (τ z.1) m z)
    (hstop : ∀ m (s : ℝ≥0) (B : Set X), B ∈ 𝓔 →
      MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace (hs₂ m).measurableSpace]
        (Prod.fst ⁻¹' B ∩ {z | s < S (τ z.1) m z}))
    (hgW : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] f ∧ ∀ z, r < S (τ z.1) m z → rDrvFst live xj Wj ζj xk Wk τ r z = f z)
    (hgVL : ∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] f ∧ ∀ z, r < S (τ z.1) m z → VL (τ z.1) i r z = f z)
    (hgVR : ∀ m j r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] f ∧ ∀ z, r < S (τ z.1) m z → VR (τ z.1) j r z = f z)
    (hgS : ∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y (hτ.min (hs₁ m)).measurableSpace
      (hs₂ m).measurableSpace] ({z | S (τ z.1) k z ≤ r} ∩ {z | r < S (τ z.1) m z}))
    (hgζ : ∀ m z, (S (τ z.1) m z : ℝ≥0∞) ≤ rLifeFst live xj Wj ζj xk Wk τ z)
    (hcov : ∀ᵐ z ∂μ, live (τ z.1) z.1 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.2))
        (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) →
      ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) s ≤ S (τ z.1) m z) :
    ResStopInputFst P₁ P₂ μ live xj Wj ζj xk Wk VL VR S (g3FstD κ x y W₁ VL₁ VR₁ ζ₁ W₂ ζ₂) τ 𝓔 where
  𝓐 m := (hs₁ m).measurableSpace
  𝓐' m := (hτ.min (hs₁ m)).measurableSpace
  𝓑 m := (hs₂ m).measurableSpace
  D₀ m ω := ENNReal.ofReal (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ (g3S₁ x y W₁ ζ₁) m) ω
    (g3S₁ x y W₁ ζ₁ m ω.1) (g3S₂ x y W₂ ζ₂ m ω.2))
  hA' m := IsStoppingTime.measurableSpace_mono _ _ fun _ => min_le_right _ _
  hA m := (hs₁ m).measurableSpace_le
  hB m := (hs₂ m).measurableSpace_le
  hD₀ m := by
    have hM := A1RectMeas.g3RectMeas κ hκ4 hκ8 y x hyx hx X Y mX mY inferInstance inferInstance P₁ inferInstance P₂
      inferInstance 𝓖₁ 𝓖₂ inferInstance inferInstance W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ hB₂ h₁ hB₁ hg₁ m
    exact (hM (fun ω => (g3S₁ x y W₁ ζ₁ m ω.1 : ℝ)) (fun ω => (g3S₂ x y W₂ ζ₂ m ω.2 : ℝ))
      ((measurable_of_isStoppingTime (hs₁ m)).comp measurable_fst).coe_nnreal_real
      ((measurable_of_isStoppingTime (hs₂ m)).comp measurable_snd).coe_nnreal_real (fun ω => NNReal.coe_nonneg _)
      (fun ω => NNReal.coe_nonneg _) fun ω => ⟨(), le_rfl, le_rfl⟩).ennreal_ofReal
  hrect m A B hA hB := rect_of_rectDens (hs₁ m).measurableSpace_le (hs₂ m).measurableSpace_le (hd m) A B hA hB
  hopt m := g3Fst_hopt hκ4 hκ8 hyx hx h₁ hB₁ hg₁ h₂ hB₂ hs₁ hτ m
  hSm := hSm
  hstop := hstop
  hgW := hgW
  hgVL := hgVL
  hgVR := hgVR
  hgS := hgS
  hgζ := hgζ
  hcov := hcov

omit mX mY in
/-- **`hgζ` of the large direction**: the masked caps at the stop precede the image lifetime (FORCES's
`capFst_le_rLifeFst`). -/
theorem g3Fst_hgζ (x y : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 2 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ)
    (ζ₂' : Y → ℝ≥0∞) (G₁ : Set X) (G₂ : Set Y) (τ : X → ℝ≥0) (m : ℕ) (z : X × Y) :
    (maskCap G₁ G₂ (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z : ℝ≥0∞) ≤
      rLifeFst (fun t ω => (t : ℝ≥0∞) < ζ₁ ω) 0 W₂ (fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) y W₁ τ z := by
  have hmask : maskCap G₁ G₂ (g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.1) m z ≤
      g3FstCap x y W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' (τ z.1) m z := by
    by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [maskCap_of_mem hG.1 hG.2]
    · rw [maskCap_of_not_mem hG]; exact bot_le
  have hcap := A1Forces.capFst_le_rLifeFst (live := fun t ω => (t : ℝ≥0∞) < ζ₁ ω) (xj := 0) (Wj := W₂)
    (ζj := fun ω => lifeEnd (W₂ · ω) (VL₂ 0 · ω) (ζ₂ ω)) (xk := y) (Wk := W₁) (τ := fun _ => τ z.1)
    (g3FstOwn x y W₁' ζ₁' W₂' ζ₂' (τ z.1) m) z
  have hlife := (cImg_congr_of_eq (z := z) (τ := fun z => τ z.1) (τ₀ := fun _ => τ z.1)
    (live := fun t (z : X × Y) => (t : ℝ≥0∞) < ζ₁ z.1) (xj := 0) (Wj := fun t (z : X × Y) => W₂ t z.2)
    (ζj := fun z : X × Y => lifeEnd (W₂ · z.2) (VL₂ 0 · z.2) (ζ₂ z.2)) (xk := y) (Wk := fun t (z : X × Y) => W₁ t z.1)
    rfl).1
  refine (ENNReal.coe_le_coe.2 hmask).trans (hcap.trans ?_)
  exact hlife.symm.le

end Rect

end InteractingSLE.ZhanGT4.A1G3Law
