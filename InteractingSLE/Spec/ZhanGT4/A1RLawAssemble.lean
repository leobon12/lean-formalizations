/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawNoise
import InteractingSLE.Spec.ZhanGT4.A1RLawWire

/-!
# Zhan's A.1 under R83: the family law with the compensated residual as the noise

Packet PROVE-A1-RECTLAW2 (R83). The C family input `HasFamilyLawC` (`HasFamilyLawFstC`) is assembled from:

* the image force points `VL σ`, `VR σ`, the caps `S σ m` and the rectangle densities `D σ m` indexed by the frozen
  time `σ`, jointly measurable;
* the deterministic image geometry up to the cap (`SeedImageGeometry` of the canonical image data stopped at the cap)
  at **every** sample with a positive cap or on the live event — the noise is then the compensated residual
  (`exists_residualNoise`), continuous on every cap interval and record-local;
* the **one-sample law of the sections** with the residual as the noise (`IsSeedSampleLaw` under `D σ m (·, y) · P₁`,
  for almost every frozen sample `y` and every frozen time `σ`): the per-sample frozen-curve image law;
* at every stopping time of the usual augmentation, the primitive per-stop inputs `ResStopInput` (the exit-time
  rectangle law (1.7) on the two stopped records, optional sampling in the conditioning coordinate, the stopped-record
  measurability of the data, and the clock exhaustion).

Main results: **`hasFamilyLawC_of_residual`**, **`hasFamilyLawFstC_of_residual`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open A1Canon A1Ref A1Core A1Frozen A1Family A1MultiMark A1RectLaw

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ}

/-! ### The masked canonical driver starts at `0` -/

theorem cImgDrvM_zero {Z : Type*} (live : ℝ≥0 → Z → Prop) (xj : ℝ) (Wj : ℝ≥0 → Z → ℝ) (ζj : Z → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Z → ℝ) (τ : Z → ℝ≥0) (z : Z) : cImgDrvM live xj Wj ζj xk Wk τ 0 z = 0 := by
  classical
  unfold cImgDrvM cImgDrv cImgSrc
  split_ifs <;> simp

/-! ### Conditioning curve on `Y` -/

section Snd

/-- **The primitive per-stop inputs of the residual family** at the stop `τ` (conditioning curve on `Y`; `𝓔` the
events of the stopped σ-algebra of `τ`): the inputs of `FamilyRectC.ofRect` other than those about the noise and the
geometry, for the data read at the frozen time `σ = τ(y)`. -/
structure ResStopInput (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y)) (live : ℝ≥0 → Y → Prop) (xj : ℝ)
    (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ) (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ)
    (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ) (S : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞)
    (τ : Y → ℝ≥0) (𝓔 : Set (Set Y)) where
  /-- The image curve's stopped record on rectangle `m`. -/
  𝓐 : ℕ → MeasurableSpace X
  /-- The conditioning curve's stopped record on rectangle `m`. -/
  𝓑 : ℕ → MeasurableSpace Y
  /-- The conditioning curve's record stopped at `τ ∧ S_kᵐ`. -/
  𝓑' : ℕ → MeasurableSpace Y
  /-- The exit-time rectangle density (`M(S_jᵐ, S_kᵐ)`). -/
  D₀ : ℕ → X × Y → ℝ≥0∞
  hA : ∀ m, 𝓐 m ≤ mX
  hB' : ∀ m, 𝓑' m ≤ 𝓑 m
  hB : ∀ m, 𝓑 m ≤ mY
  hD₀ : ∀ m, Measurable (D₀ m)
  hrect : ∀ m A B, MeasurableSet[𝓐 m] A → MeasurableSet[𝓑 m] B →
    μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ m z ∂(P₁.prod P₂)
  hopt : ∀ m, ∀ᵐ x ∂P₁, ∀ B, MeasurableSet[𝓑' m] B →
    ∫⁻ y in B, D₀ m (x, y) ∂P₂ = ∫⁻ y in B, D (τ y) m (x, y) ∂P₂
  hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] fun z => S (τ z.2) m z
  hstop : ∀ m (s : ℝ≥0) (B : Set Y), B ∈ 𝓔 →
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] (Prod.snd ⁻¹' B ∩ {z | s < S (τ z.2) m z})
  hgW : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] f ∧
    ∀ z, r < S (τ z.2) m z → rDrv live xj Wj ζj xk Wk τ r z = f z
  hgVL : ∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] f ∧
    ∀ z, r < S (τ z.2) m z → VL (τ z.2) i r z = f z
  hgVR : ∀ m j r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] f ∧
    ∀ z, r < S (τ z.2) m z → VR (τ z.2) j r z = f z
  hgS : ∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)]
    ({z | S (τ z.2) k z ≤ r} ∩ {z | r < S (τ z.2) m z})
  hgζ : ∀ m z, (S (τ z.2) m z : ℝ≥0∞) ≤ rLife live xj Wj ζj xk Wk τ z
  hcov : ∀ᵐ z ∂μ, live (τ z.2) z.2 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.1))
      (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) →
    ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) s ≤ S (τ z.2) m z

/-- **The C family input from the per-sample laws with the residual as the noise** (conditioning curve on `Y`). -/
theorem hasFamilyLawC_of_residual {a : ℝ} (ha : 0 < a) {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] {𝓕k : Filtration ℝ≥0 mY} {live : ℝ≥0 → Y → Prop} {xj : ℝ}
    {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ} {ΘL : ℝ≥0 → Y → Fin nL → ℝ}
    {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (S : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2)
    (hS : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2)
    (hD : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2)
    (hgeo : ∀ σ m z, 0 < S σ m z ∨ live σ z.2 → SeedImageGeometry (ΘL σ z.2) (ΘR σ z.2) ρL ρR
      (fun t => rDrv live xj Wj ζj xk Wk (fun _ => σ) (min t (S σ m z)) z)
      (fun i t => VL σ i (min t (S σ m z)) z) (fun j t => VR σ j (min t (S σ m z)) z) (S σ m z))
    (hlaw : ∀ m, ∀ᵐ y ∂P₂, ∀ σ : ℝ≥0, IsSeedSampleLaw (P₁.withDensity fun x => D σ m (x, y))
      (fun t x => rDrv live xj Wj ζj xk Wk (fun _ => σ) t (x, y))
      (fun x => rLife live xj Wj ζj xk Wk (fun _ => σ) (x, y)) (fun i t x => VL σ i t (x, y))
      (fun j t x => VR σ j t (x, y))
      (fun t x => seedCapacityNoise a ρL ρR (fun s => rDrv live xj Wj ζj xk Wk (fun _ => σ) s (x, y))
        (fun i s => VL σ i s (x, y)) (fun j s => VR σ j s (x, y)) t)
      (fun k x => S σ k (x, y)) m)
    (hstop : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
      Nonempty (ResStopInput P₁ P₂ μ live xj Wj ζj xk Wk VL VR S D τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  obtain ⟨N, hNm, hN0, hNc, hNeq⟩ := exists_residualNoise (Z := X × Y) a (xL := fun σ z => ΘL σ z.2)
    (xR := fun σ z => ΘR σ z.2) (ρL := ρL) (ρR := ρR) (W := fun σ t z => rDrv live xj Wj ζj xk Wk (fun _ => σ) t z)
    (VL := VL) (VR := VR) (S := S) hm3 hVL hVR (fun σ z => cImgDrvM_zero _ _ _ _ _ _ _ z)
    (fun σ m z h => hgeo σ m z (Or.inl h))
  set F := FrozenFamilyC.ofSampleLaw (P₁ := P₁) (P₂ := P₂) (live := live) (xj := xj) (Wj := Wj) (ζj := ζj)
    (xk := xk) (Wk := Wk) VL VR N S D hVL hVR hNc hN0 hNm hS hD
    (fun m => (hlaw m).mono fun y hy σ => IsSeedSampleLaw.congr_noise (hy σ) fun x t ht => hNeq σ m (x, y) t ht)
    with hF
  refine ⟨F, fun τ hτ => ?_⟩
  obtain ⟨I⟩ := hstop τ hτ
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hdrv : ∀ (z : X × Y) t, rDrv live xj Wj ζj xk Wk τ t z =
      rDrv live xj Wj ζj xk Wk (fun _ => τ z.2) t z := fun z t =>
    (cImg_congr_of_eq (z := z) (τ := fun z => τ z.2) (τ₀ := fun _ => τ z.2) rfl).2 t
  have hgeoτ : ∀ m z, 0 < S (τ z.2) m z ∨ live (τ z.2) z.2 → SeedImageGeometry (ΘL (τ z.2) z.2) (ΘR (τ z.2) z.2)
      ρL ρR (fun t => rDrv live xj Wj ζj xk Wk τ (min t (S (τ z.2) m z)) z)
      (fun i t => VL (τ z.2) i (min t (S (τ z.2) m z)) z) (fun j t => VR (τ z.2) j (min t (S (τ z.2) m z)) z)
      (S (τ z.2) m z) := fun m z h => by
    simp only [hdrv z]
    exact hgeo (τ z.2) m z h
  have hgN : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (I.𝓐 m) (I.𝓑' m)] f ∧
      ∀ z, r < S (τ z.2) m z → N (τ z.2) r z = f z := fun m r => by
    obtain ⟨f, hf, hfe⟩ := exists_measurable_noise_of_geometry (𝓜 := @Prod.instMeasurableSpace X Y (I.𝓐 m) (I.𝓑' m))
      a (xL := fun z => ΘL (τ z.2) z.2) (xR := fun z => ΘR (τ z.2) z.2) (cap := fun z => S (τ z.2) m z)
      (W := rDrv live xj Wj ζj xk Wk τ) (VL := fun i t z => VL (τ z.2) i t z) (VR := fun j t z => VR (τ z.2) j t z)
      (I.hgW m) (I.hgVL m) (I.hgVR m) (fun z hz => hgeoτ m z (Or.inl hz)) r
    refine ⟨f, hf, fun z hz => ?_⟩
    rw [hNeq (τ z.2) m z r hz.le, ← hfe z hz]
    simp only [hdrv z]
  exact ⟨FamilyRectC.ofRect F I.𝓐 I.𝓑 I.𝓑' I.D₀ I.hA I.hB' I.hB hτm I.hD₀ I.hrect I.hopt
    (fun m t => measurable_stopped_of_before_of_continuousOn
      (𝓜 := @Prod.instMeasurableSpace X Y (I.𝓐 m) (I.𝓑' m)) (N := fun t z => N (τ z.2) t z)
      (cap := fun z => S (τ z.2) m z) (I.hSm m) (hgN m) (fun z => hNc (τ z.2) m z) (fun z => hN0 (τ z.2) z) t)
    I.hSm I.hstop I.hgW I.hgVL I.hgVR hgN I.hgS I.hgζ I.hcov ha
    (fun m => Eventually.of_forall fun z hz => hgeoτ m z (Or.inr hz))
    (fun m => Eventually.of_forall fun z _ t ht => by
      show N (τ z.2) t z = seedCapacityNoise a ρL ρR (fun x => rDrv live xj Wj ζj xk Wk τ x z)
        (fun i t => VL (τ z.2) i t z) (fun j t => VR (τ z.2) j t z) t
      rw [hNeq (τ z.2) m z t ht.le]
      simp only [hdrv z])⟩

end Snd

/-! ### Conditioning curve on `X` -/

section Fst

/-- **The primitive per-stop inputs of the residual family, conditioning curve on `X`** (mirror of `ResStopInput`:
optional sampling in the first coordinate, down to `𝓐' m ≤ 𝓐 m`, the record stopped at `τ ∧ S_kᵐ`). -/
structure ResStopInputFst (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y)) (live : ℝ≥0 → X → Prop) (xj : ℝ)
    (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ) (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ)
    (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ) (S : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞)
    (τ : X → ℝ≥0) (𝓔 : Set (Set X)) where
  /-- The conditioning curve's stopped record on rectangle `m`. -/
  𝓐 : ℕ → MeasurableSpace X
  /-- The conditioning curve's record stopped at `τ ∧ S_kᵐ`. -/
  𝓐' : ℕ → MeasurableSpace X
  /-- The image curve's stopped record on rectangle `m`. -/
  𝓑 : ℕ → MeasurableSpace Y
  /-- The exit-time rectangle density (`M(S_kᵐ, S_jᵐ)`). -/
  D₀ : ℕ → X × Y → ℝ≥0∞
  hA' : ∀ m, 𝓐' m ≤ 𝓐 m
  hA : ∀ m, 𝓐 m ≤ mX
  hB : ∀ m, 𝓑 m ≤ mY
  hD₀ : ∀ m, Measurable (D₀ m)
  hrect : ∀ m A B, MeasurableSet[𝓐 m] A → MeasurableSet[𝓑 m] B →
    μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ m z ∂(P₁.prod P₂)
  hopt : ∀ m, ∀ᵐ y ∂P₂, ∀ A, MeasurableSet[𝓐' m] A →
    ∫⁻ x in A, D₀ m (x, y) ∂P₁ = ∫⁻ x in A, D (τ x) m (x, y) ∂P₁
  hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] fun z => S (τ z.1) m z
  hstop : ∀ m (s : ℝ≥0) (B : Set X), B ∈ 𝓔 →
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] (Prod.fst ⁻¹' B ∩ {z | s < S (τ z.1) m z})
  hgW : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] f ∧
    ∀ z, r < S (τ z.1) m z → rDrvFst live xj Wj ζj xk Wk τ r z = f z
  hgVL : ∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] f ∧
    ∀ z, r < S (τ z.1) m z → VL (τ z.1) i r z = f z
  hgVR : ∀ m j r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] f ∧
    ∀ z, r < S (τ z.1) m z → VR (τ z.1) j r z = f z
  hgS : ∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)]
    ({z | S (τ z.1) k z ≤ r} ∩ {z | r < S (τ z.1) m z})
  hgζ : ∀ m z, (S (τ z.1) m z : ℝ≥0∞) ≤ rLifeFst live xj Wj ζj xk Wk τ z
  hcov : ∀ᵐ z ∂μ, live (τ z.1) z.1 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.2))
      (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) →
    ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) s ≤ S (τ z.1) m z

/-- **The C family input from the per-sample laws with the residual as the noise** (conditioning curve on `X`,
mirror of `hasFamilyLawC_of_residual`). -/
theorem hasFamilyLawFstC_of_residual {a : ℝ} (ha : 0 < a) {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁]
    [SFinite P₂] {μ : Measure (X × Y)} [IsFiniteMeasure μ] {𝓕k : Filtration ℝ≥0 mX} {live : ℝ≥0 → X → Prop}
    {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {ΘL : ℝ≥0 → X → Fin nL → ℝ}
    {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (S : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2)
    (hS : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2)
    (hD : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2)
    (hgeo : ∀ σ m z, 0 < S σ m z ∨ live σ z.1 → SeedImageGeometry (ΘL σ z.1) (ΘR σ z.1) ρL ρR
      (fun t => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) (min t (S σ m z)) z)
      (fun i t => VL σ i (min t (S σ m z)) z) (fun j t => VR σ j (min t (S σ m z)) z) (S σ m z))
    (hlaw : ∀ m, ∀ᵐ x ∂P₁, ∀ σ : ℝ≥0, IsSeedSampleLaw (P₂.withDensity fun y => D σ m (x, y))
      (fun t y => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) t (x, y))
      (fun y => rLifeFst live xj Wj ζj xk Wk (fun _ => σ) (x, y)) (fun i t y => VL σ i t (x, y))
      (fun j t y => VR σ j t (x, y))
      (fun t y => seedCapacityNoise a ρL ρR (fun s => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) s (x, y))
        (fun i s => VL σ i s (x, y)) (fun j s => VR σ j s (x, y)) t)
      (fun k y => S σ k (x, y)) m)
    (hstop : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (ResStopInputFst P₁ P₂ μ live xj Wj ζj xk Wk VL VR S D τ
        {B | MeasurableSet[hτ.measurableSpace] B})) :
    HasFamilyLawFstC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  obtain ⟨N, hNm, hN0, hNc, hNeq⟩ := exists_residualNoise (Z := X × Y) a (xL := fun σ z => ΘL σ z.1)
    (xR := fun σ z => ΘR σ z.1) (ρL := ρL) (ρR := ρR)
    (W := fun σ t z => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) t z)
    (VL := VL) (VR := VR) (S := S) hm3 hVL hVR (fun σ z => cImgDrvM_zero _ _ _ _ _ _ _ z)
    (fun σ m z h => hgeo σ m z (Or.inl h))
  set F := FrozenFamilyFstC.ofSampleLaw (P₁ := P₁) (P₂ := P₂) (live := live) (xj := xj) (Wj := Wj) (ζj := ζj)
    (xk := xk) (Wk := Wk) VL VR N S D hVL hVR hNc hN0 hNm hS hD
    (fun m => (hlaw m).mono fun x hx σ => IsSeedSampleLaw.congr_noise (hx σ) fun y t ht => hNeq σ m (x, y) t ht)
    with hF
  refine ⟨F, fun τ hτ => ?_⟩
  obtain ⟨I⟩ := hstop τ hτ
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hdrv : ∀ (z : X × Y) t, rDrvFst live xj Wj ζj xk Wk τ t z =
      rDrvFst live xj Wj ζj xk Wk (fun _ => τ z.1) t z := fun z t =>
    (cImg_congr_of_eq (z := z) (τ := fun z => τ z.1) (τ₀ := fun _ => τ z.1) rfl).2 t
  have hgeoτ : ∀ m z, 0 < S (τ z.1) m z ∨ live (τ z.1) z.1 → SeedImageGeometry (ΘL (τ z.1) z.1) (ΘR (τ z.1) z.1)
      ρL ρR (fun t => rDrvFst live xj Wj ζj xk Wk τ (min t (S (τ z.1) m z)) z)
      (fun i t => VL (τ z.1) i (min t (S (τ z.1) m z)) z) (fun j t => VR (τ z.1) j (min t (S (τ z.1) m z)) z)
      (S (τ z.1) m z) := fun m z h => by
    simp only [hdrv z]
    exact hgeo (τ z.1) m z h
  have hgN : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (I.𝓐' m) (I.𝓑 m)] f ∧
      ∀ z, r < S (τ z.1) m z → N (τ z.1) r z = f z := fun m r => by
    obtain ⟨f, hf, hfe⟩ := exists_measurable_noise_of_geometry (𝓜 := @Prod.instMeasurableSpace X Y (I.𝓐' m) (I.𝓑 m))
      a (xL := fun z => ΘL (τ z.1) z.1) (xR := fun z => ΘR (τ z.1) z.1) (cap := fun z => S (τ z.1) m z)
      (W := rDrvFst live xj Wj ζj xk Wk τ) (VL := fun i t z => VL (τ z.1) i t z)
      (VR := fun j t z => VR (τ z.1) j t z) (I.hgW m) (I.hgVL m) (I.hgVR m) (fun z hz => hgeoτ m z (Or.inl hz)) r
    refine ⟨f, hf, fun z hz => ?_⟩
    rw [hNeq (τ z.1) m z r hz.le, ← hfe z hz]
    simp only [hdrv z]
  exact ⟨FamilyRectFstC.ofRect F I.𝓐 I.𝓐' I.𝓑 I.D₀ I.hA' I.hA I.hB hτm I.hD₀ I.hrect I.hopt
    (fun m t => measurable_stopped_of_before_of_continuousOn
      (𝓜 := @Prod.instMeasurableSpace X Y (I.𝓐' m) (I.𝓑 m)) (N := fun t z => N (τ z.1) t z)
      (cap := fun z => S (τ z.1) m z) (I.hSm m) (hgN m) (fun z => hNc (τ z.1) m z) (fun z => hN0 (τ z.1) z) t)
    I.hSm I.hstop I.hgW I.hgVL I.hgVR hgN I.hgS I.hgζ I.hcov ha
    (fun m => Eventually.of_forall fun z hz => hgeoτ m z (Or.inr hz))
    (fun m => Eventually.of_forall fun z _ t ht => by
      show N (τ z.1) t z = seedCapacityNoise a ρL ρR (fun x => rDrvFst live xj Wj ζj xk Wk τ x z)
        (fun i t => VL (τ z.1) i t z) (fun j t => VR (τ z.1) j t z) t
      rw [hNeq (τ z.1) m z t ht.le]
      simp only [hdrv z])⟩

end Fst

end InteractingSLE.ZhanGT4.A1RLaw
