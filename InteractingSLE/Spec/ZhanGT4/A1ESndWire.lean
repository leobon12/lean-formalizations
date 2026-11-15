/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1ESndZero
import InteractingSLE.Spec.ZhanGT4.A1RLawStmt

/-!
# Zhan's A.1 under R83, (Eight), small-curve direction: the family law from the record facts

Packet PROVE-A1-EIGHTSND (mirror of PROVE-A1-EIGHTFAM's `A1EFamWire` for the large direction):

* **`eightSndResStop`**: A1-RECTLAW2's `ResStopInput` of the small direction from the remaining record facts (records
  `(S₁ᵐ, τ ∧ S₂ᵐ)` of the patched exits, exit density, (1.7) from `RectDens`, optional sampling `eightSnd_hopt`);
* `eightSnd_hgζ`: the record fact `hgζ` (the masked caps precede the image lifetime);
* **`EightSndRecordStatement`** (the remaining input: the record facts `hSm`, `hstop`, `hgW`, `hgVL`, `hgVR`, `hgS`,
  `hcov` of `eightSndResStop`) and **`eightRectLawSndC_of_records : EightSndRecordStatement κ → EightRectLawSndC κ`**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1ESnd

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref A1Canon A1Core A1Frozen A1Marg A1Law A1Patch A1SeedField A1EightSeed A1G3Calc A1Common A1EightFin
  A1Asm A1Family A1Forces A1RLaw A1LargeDens A1ELaw A1G3L2 A1SeedGeom

section Stop

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The per-stop inputs of the small direction from the remaining record facts** (`ResStopInput` for (Eight)): the
records are the stopped σ-algebras of the patched exits (`𝓑'` stopped at `τ ∧ S₂ᵐ`), the exit density is the patched
seeded height field at the rectangle corner, (1.7) on the records is the coupling's `RectDens` hypothesis and the
optional sampling is A1-RECTLAW2's `eightSnd_hopt`. The caps `S`, forces `VL`, `VR` and image data are arbitrary;
their record facts and the clock exhaustion `hcov` are the remaining inputs. -/
def eightSndResStop {κ x : ℝ} (hκ8 : 8 ≤ κ) (hx : x < 0) {P₁ : Measure X} {P₂ : Measure Y}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] {𝓖₁ : Filtration ℝ≥0 mX} {𝓖₂ : Filtration ℝ≥0 mY}
    [𝓖₁.IsRightContinuous] [𝓖₂.IsRightContinuous] {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
    {VR₁ : Fin 2 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
    {VL₂ : Fin 1 → ℝ≥0 → Y → ℝ} {VR₂ : Fin 0 → ℝ≥0 → Y → ℝ} {B₂ : ℝ≥0 → Y → ℝ} {ζ₂ : Y → ℝ≥0∞}
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓖₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω))
    (hg₁ : ∀ ω, GoodSmallEight (W₁ · ω) (fun i t => VL₁ i t ω) (fun i t => VR₁ i t ω) (B₁ · ω) (ζ₁ ω))
    (h₂ : IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓖₂ W₂ VL₂ VR₂ B₂ ζ₂) (hB₂ : ∀ ω, Continuous (B₂ · ω))
    (hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (eightS₁ x W₁ ζ₁ m ω : WithTop ℝ≥0))
    (hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (eightS₂ x W₂ ζ₂ m ω : WithTop ℝ≥0)) {μ : Measure (X × Y)}
    (hd : ∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
      ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m) ω
        (eightS₁ x W₁ ζ₁ m ω.1) (eightS₂ x W₂ ζ₂ m ω.2)))
    {τ : Y → ℝ≥0} (hτ : IsStoppingTime 𝓖₂ fun y => (τ y : WithTop ℝ≥0)) {nL nR : ℕ}
    {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}
    {VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ} {VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ} {S : ℝ≥0 → ℕ → X × Y → ℝ≥0}
    {𝓔 : Set (Set Y)}
    (hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (hs₁ m).measurableSpace
      (hτ.min (hs₂ m)).measurableSpace] fun z => S (τ z.2) m z)
    (hstop : ∀ m (s : ℝ≥0) (B : Set Y), B ∈ 𝓔 →
      MeasurableSet[@Prod.instMeasurableSpace X Y (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace]
        (Prod.snd ⁻¹' B ∩ {z | s < S (τ z.2) m z}))
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
    ResStopInput P₁ P₂ μ live xj Wj ζj xk Wk VL VR S (eightSndD κ x W₁ VL₁ VR₁ ζ₁ W₂ ζ₂) τ 𝓔 where
  𝓐 m := (hs₁ m).measurableSpace
  𝓑 m := (hs₂ m).measurableSpace
  𝓑' m := (hτ.min (hs₂ m)).measurableSpace
  D₀ m ω := ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁ VL₁ VR₁ W₂ (eightS₁ x W₁ ζ₁) m) ω
    (eightS₁ x W₁ ζ₁ m ω.1) (eightS₂ x W₂ ζ₂ m ω.2))
  hA m := (hs₁ m).measurableSpace_le
  hB' m := IsStoppingTime.measurableSpace_mono _ _ fun _ => min_le_right _ _
  hB m := (hs₂ m).measurableSpace_le
  hD₀ m := by
    have hM := isFieldMeas_eight_of_patched hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ m
    exact (hM (fun ω => (eightS₁ x W₁ ζ₁ m ω.1 : ℝ)) (fun ω => (eightS₂ x W₂ ζ₂ m ω.2 : ℝ))
      ((measurable_of_isStoppingTime (hs₁ m)).comp measurable_fst).coe_nnreal_real
      ((measurable_of_isStoppingTime (hs₂ m)).comp measurable_snd).coe_nnreal_real (fun ω => NNReal.coe_nonneg _)
      (fun ω => NNReal.coe_nonneg _) fun ω => ⟨(), le_rfl, le_rfl⟩).ennreal_ofReal
  hrect m A B hA hB := rect_of_rectDens (hs₁ m).measurableSpace_le (hs₂ m).measurableSpace_le (hd m) A B hA hB
  hopt m := eightSnd_hopt hκ8 hx h₁ hB₁ hg₁ h₂ hB₂ hs₂ hτ m
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
theorem eightSnd_hgζ (x : ℝ) (W₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞) (W₂ : ℝ≥0 → Y → ℝ)
    (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (ζ₂ : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞) (W₂' : ℝ≥0 → Y → ℝ)
    (ζ₂' : Y → ℝ≥0∞) (G₁ : Set X) (G₂ : Set Y) (τ : Y → ℝ≥0) (m : ℕ) (z : X × Y) :
    (maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z : ℝ≥0∞) ≤
      rLife (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ τ z := by
  have hmask : maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z ≤
      eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' (τ z.2) m z := by
    by_cases hG : z.1 ∈ G₁ ∧ z.2 ∈ G₂
    · rw [maskCap_of_mem hG.1 hG.2]
    · rw [maskCap_of_not_mem hG]; exact bot_le
  have hcap := A1Forces.capSnd_le_rLife (live := eightSndLive W₂ VL₂ ζ₂) (xj := x) (Wj := W₁) (ζj := ζ₁) (xk := 0)
    (Wk := W₂) (τ := fun _ => τ z.2) (eightSndOwn x W₁' ζ₁' W₂' ζ₂' (τ z.2) m) z
  have hlife := (cImg_congr_of_eq (z := z) (τ := fun z => τ z.2) (τ₀ := fun _ => τ z.2)
    (live := fun t (z : X × Y) => eightSndLive W₂ VL₂ ζ₂ t z.2) (xj := x) (Wj := fun t (z : X × Y) => W₁ t z.1)
    (ζj := fun z : X × Y => ζ₁ z.1) (xk := 0) (Wk := fun t (z : X × Y) => W₂ t z.2) rfl).1
  refine (ENNReal.coe_le_coe.2 hmask).trans (hcap.trans ?_)
  exact hlife.symm.le

end Stop

section Final

/-- **The record facts of the small Eight direction** (the remaining input of `EightRectLawSndC`): the binders of
`EightRectLawSndC` and the good sets `G₁`, `G₂` of the two patches; at every stopping time `τ` of the large curve's
usual augmentation, the masked raw caps, the canonical driver and the forces read, before the cap, only the records
`(S₁ᵐ, τ ∧ S₂ᵐ)` of the patched exits, and the caps exhaust the pre-contact clock almost surely (the inputs `hSm`,
`hstop`, `hgW`, `hgVL`, `hgVR`, `hgS`, `hcov` of `eightSndResStop`). -/
def EightSndRecordStatement (κ : ℝ) : Prop :=
  8 ≤ κ → ∀ x : ℝ, x < 0 →
    ∀ (X Y : Type) (_ : MeasurableSpace X) (_ : MeasurableSpace Y) (_ : StandardBorelSpace X)
      (_ : StandardBorelSpace Y) (P₁ : Measure X) (_ : IsProbabilityMeasure P₁) (P₂ : Measure Y)
      (_ : IsProbabilityMeasure P₂) (𝓕₁ : Filtration ℝ≥0 (inferInstance : MeasurableSpace X))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Y))
      (W₂ : ℝ≥0 → Y → ℝ) (VL₂ : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂ : Fin 0 → ℝ≥0 → Y → ℝ) (B₂ : ℝ≥0 → Y → ℝ)
      (ζ₂ : Y → ℝ≥0∞) (W₁ : ℝ≥0 → X → ℝ) (VL₁ : Fin 1 → ℝ≥0 → X → ℝ) (VR₁ : Fin 2 → ℝ≥0 → X → ℝ)
      (B₁ : ℝ≥0 → X → ℝ) (ζ₁ : X → ℝ≥0∞),
      IsRegMarginal κ ![x] ![] ![0] ![] P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ →
      IsRegMarginal (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ →
      ∀ (W₂' : ℝ≥0 → Y → ℝ) (VL₂' : Fin 1 → ℝ≥0 → Y → ℝ) (VR₂' : Fin 0 → ℝ≥0 → Y → ℝ) (B₂' : ℝ≥0 → Y → ℝ)
        (ζ₂' : Y → ℝ≥0∞) (W₁' : ℝ≥0 → X → ℝ) (VL₁' : Fin 1 → ℝ≥0 → X → ℝ) (VR₁' : Fin 2 → ℝ≥0 → X → ℝ)
        (B₁' : ℝ≥0 → X → ℝ) (ζ₁' : X → ℝ≥0∞),
      IsPatchOf κ ![x] ![] ![0] ![] (fun _ _ _ _ _ => True) P₂ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₂' VL₂' VR₂' B₂' ζ₂' →
      IsPatchOf (kh κ) ![0] ![0, -x] (smallEightRhoL κ) (smallEightRhoR κ) GoodSmallEight P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁
        W₁' VL₁' VR₁' B₁' ζ₁' →
      ∀ (hs₁ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₁ P₁) fun ω => (eightS₁ x W₁' ζ₁' m ω : WithTop ℝ≥0))
        (hs₂ : ∀ m, IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun ω => (eightS₂ x W₂' ζ₂' m ω : WithTop ℝ≥0))
        (μ : Measure (X × Y)), IsProbabilityMeasure μ → μ.map Prod.fst = P₁ → μ.map Prod.snd = P₂ →
        (∀ m, RectDens (hs₁ m).measurableSpace (hs₂ m).measurableSpace P₁ P₂ μ fun ω =>
          ENNReal.ofReal (seedHeightField (eightRec κ (-x) W₁' VL₁' VR₁' W₂' (eightS₁ x W₁' ζ₁') m) ω
            (eightS₁ x W₁' ζ₁' m ω.1) (eightS₂ x W₂' ζ₂' m ω.2))) →
        ∀ (G₁ : Set X) (G₂ : Set Y), MeasurableSet G₁ → MeasurableSet G₂ → P₁ G₁ᶜ = 0 → P₂ G₂ᶜ = 0 →
        (∀ x₀ ∈ G₁, (∀ t, W₁' t x₀ = W₁ t x₀) ∧ (∀ i t, VL₁' i t x₀ = VL₁ i t x₀) ∧
          (∀ i t, VR₁' i t x₀ = VR₁ i t x₀) ∧ (∀ t, B₁' t x₀ = B₁ t x₀) ∧ ζ₁' x₀ = ζ₁ x₀) →
        (∀ y₀ ∈ G₂, (∀ t, W₂' t y₀ = W₂ t y₀) ∧ (∀ i t, VL₂' i t y₀ = VL₂ i t y₀) ∧
          (∀ i t, VR₂' i t y₀ = VR₂ i t y₀) ∧ (∀ t, B₂' t y₀ = B₂ t y₀) ∧ ζ₂' y₀ = ζ₂ y₀) →
        ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕₂ P₂) fun y₀ => (τ y₀ : WithTop ℝ≥0)),
          (∀ m, Measurable[@Prod.instMeasurableSpace X Y
            (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace]
            fun z => maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z) ∧
          (∀ m (s : ℝ≥0) (B : Set Y), MeasurableSet[hτ.measurableSpace] B →
            MeasurableSet[@Prod.instMeasurableSpace X Y
            (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace]
              (Prod.snd ⁻¹' B ∩ {z | s < maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z})) ∧
          (∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y
            (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace] f ∧
            ∀ z, r < maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z →
              rDrv (eightSndLive W₂ VL₂ ζ₂) x W₁ ζ₁ 0 W₂ τ r z = f z) ∧
          (∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y
            (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace] f ∧
            ∀ z, r < maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z →
              eightSndVL x W₁ ζ₁ W₂ VL₂ ζ₂ (τ z.2) i r z = f z) ∧
          (∀ m j r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y
            (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace] f ∧
            ∀ z, r < maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z →
              eightSndVR x W₁ ζ₁ W₂ VL₂ ζ₂ (τ z.2) j r z = f z) ∧
          (∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y
            (hs₁ m).measurableSpace (hτ.min (hs₂ m)).measurableSpace]
            ({z | maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) k z ≤ r} ∩
              {z | r < maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z})) ∧
          ∀ᵐ z ∂μ, eightSndLive W₂ VL₂ ζ₂ (τ z.2) z.2 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime x
              (Strip.extPath (W₁ · z.1)) (ζ₁ z.1) 0 (Strip.extPath (W₂ · z.2)) (τ z.2) →
            ∃ m, A1Ref.imgClk x (Strip.extPath (W₁ · z.1)) 0 (Strip.extPath (W₂ · z.2)) (τ z.2) s ≤
              maskCap G₁ G₂ (eightSndCap x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂') (τ z.2) m z

/-- **Zhan's A.1 (Eight), the small-curve direction, from its record facts**: `EightRectLawSndC κ` follows from
`EightSndRecordStatement κ`. Proved here: the one-sample laws at every frozen time (protected live, protected not live,
unprotected and `σ = 0`) and the deterministic geometry, for the patched marginals and transferred to the original ones
off the null sets of the patches (masked caps); the densities' measurability; `hgζ`; the per-stop records, exit
density, (1.7) and optional sampling. -/
theorem eightRectLawSndC_of_records {κ : ℝ} (hrec : EightSndRecordStatement κ) : EightRectLawSndC κ := by
  intro hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂' VR₂' B₂'
    ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd
  obtain ⟨G₂, hG₂, hG₂0, h₂', hB₂', -, hag₂⟩ := id hp₂
  obtain ⟨G₁, hG₁, hG₁0, h₁', hB₁', hg₁', hag₁⟩ := id hp₁
  have hrec' := hrec hκ8 x hx X Y mX mY hX hY P₁ hP₁ P₂ hP₂ 𝓕₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ h₁ W₂' VL₂'
    VR₂' B₂' ζ₂' W₁' VL₁' VR₁' B₁' ζ₁' hp₂ hp₁ hs₁ hs₂ μ hμ hμ₁ hμ₂ hd G₁ G₂ hG₁ hG₂ hG₁0 hG₂0 hag₁ hag₂
  -- the agreement in the orientation of the per-sample lemmas (original = patched)
  have hagO₁ : ∀ x' ∈ G₁, (∀ t, W₁ t x' = W₁' t x') ∧ ζ₁ x' = ζ₁' x' := fun x' hx' =>
    ⟨fun t => ((hag₁ x' hx').1 t).symm, (hag₁ x' hx').2.2.2.2.symm⟩
  have hagO₂ : ∀ y' ∈ G₂, (∀ t, W₂ t y' = W₂' t y') ∧ (∀ i t, VL₂ i t y' = VL₂' i t y') ∧ ζ₂ y' = ζ₂' y' :=
    fun y' hy' => ⟨fun t => ((hag₂ y' hy').1 t).symm, fun i t => ((hag₂ y' hy').2.1 i t).symm,
      (hag₂ y' hy').2.2.2.2.symm⟩
  have hS₁m : ∀ k, Measurable (eightS₁ x W₁' ζ₁' k) := fun k => measurable_of_isStoppingTime (hs₁ k)
  have hS₂m : ∀ k, Measurable (eightS₂ x W₂' ζ₂' k) := fun k => measurable_of_isStoppingTime (hs₂ k)
  refine hasFamilyLawC_eight_of_inputs hκ8 h₂ h₁ hS₁m hS₂m hG₁ hG₂ hG₂0
    (fun k => measurable_eightSndD hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' k) (fun σ k z hz₁ hz₂ hpos => ?_)
    (fun k => Eventually.of_forall fun y' hy' σ => ?_) (fun τ hτ => ?_)
  · -- the geometry at good samples
    rcases eq_zero_or_pos σ with h0 | hσ
    · subst h0
      exact eightSnd_hgeo_zero hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hagO₁ hagO₂ k hz₁ hz₂ hpos
    · exact eightSnd_hgeo_pos hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hagO₁ hagO₂ hσ k hz₁ hz₂ hpos
  · -- the one-sample laws at good large samples, masked caps
    rcases eq_zero_or_pos σ with h0 | hσ
    · subst h0
      exact eightSnd_hlaw_zero hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hagO₁ hagO₂ hG₁ hG₁0 k hy'
    · exact eightSnd_hlaw_pos hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hagO₁ hagO₂ hG₁ hG₁0 k hy' hσ
  · -- the per-stop inputs: `eightSndResStop` with the record facts
    obtain ⟨hSm, hstop, hgW, hgVL, hgVR, hgS, hcov⟩ := hrec' τ hτ
    exact ⟨eightSndResStop hκ8 hx h₁' hB₁' hg₁' h₂' hB₂' hs₁ hs₂ hd hτ hSm hstop hgW hgVL hgVR hgS
      (eightSnd_hgζ x W₁ ζ₁ W₂ VL₂ ζ₂ W₁' ζ₁' W₂' ζ₂' G₁ G₂ τ) hcov⟩

end Final

end InteractingSLE.ZhanGT4.A1ESnd
