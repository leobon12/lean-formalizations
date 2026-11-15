/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1FrozenCore

/-!
# A.1's frozen-curve image law, III: deterministic frozen times give every stopping time

Packet PROVE-A1-FROZEN (R76). Source: Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L341–L353, R38):
"By (D8) and Girsanov, **with the other curve stopped** …"; §A.1.4 (L400–L407): "For a time `I ≤ t̄` known at a
stopping time `R`, the process `M(R + s, I)` … is a local martingale in `s`. Indeed `K₂(I)` is known at `R` …; the
identical calculation (D8), **with the conformal map of `K₂(I)` frozen**, applies"; *Follow-up 5* §1.3 (L203–L222).

The frozen-curve law is a statement about ONE frozen conditioning sample `y` and ONE frozen time `σ` (the hull
`K_k(σ)(y)` is deterministic). At a stopping time `τ` of the conditioning curve, the fibre at `y` only sees the
frozen time `σ = τ(y)`. So it suffices to prove the frozen-curve law at every deterministic frozen time, for almost
every frozen sample, uniformly in the time:

* **`IsFrozenSampleLaw.congr`**, **`IsFrozenSampleLawFst.congr`**: the frozen-sample law only reads the sections of
  the image data at the frozen sample;
* **`FrozenFamily`** (conditioning curve on `Y`): image force points, noise, caps and rectangle densities indexed by
  the deterministic frozen time `σ`, jointly measurable in `(σ, z)`, with the frozen-sample law for almost every `y`
  and **every** `σ` (the image data at `σ` are those of the canonical image at the deterministic stop `σ`);
* **`FrozenFamily.frozen_at`**: the frozen-sample law at an arbitrary function `τ` of the conditioning curve (in
  particular at every stopping time of the usual augmentation), for the data substituted at `σ = τ(y)`;
* **`FrozenFamily.toInput`**, **`isRectImageCore_of_family`**: with A22's per-stop rectangle data ((1.7) and the
  stopped-record conditions), the cover and the per-cap paths, the rectangle core `IsRectImageCore`;
* **`FrozenFamilyFst`**, **`FrozenFamilyFst.frozen_at`**, **`FrozenFamilyFst.toInput`**,
  **`isRectImageCoreFst_of_family`**: the mirror (conditioning curve on `X`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Frozen

open A1Canon A1Ref A1Core

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ}

/-! ### The frozen-sample law reads the sections only -/

section Congr

omit mY in
/-- **The frozen-sample law at `y` only reads the sections of the image data at `y`.** -/
theorem IsFrozenSampleLaw.congr {Q : Measure X} {W W' : ℝ≥0 → X × Y → ℝ} {ζ ζ' : X × Y → ℝ≥0∞}
    {VL VL' : Fin nL → ℝ≥0 → X × Y → ℝ} {VR VR' : Fin nR → ℝ≥0 → X × Y → ℝ} {N N' : ℝ≥0 → X × Y → ℝ}
    {S S' : ℕ → X × Y → ℝ≥0} {m : ℕ} {y : Y} (h : IsFrozenSampleLaw Q W ζ VL VR N S m y)
    (hW : ∀ r x, W' r (x, y) = W r (x, y)) (hζ : ∀ x, ζ' (x, y) = ζ (x, y))
    (hVL : ∀ i r x, VL' i r (x, y) = VL i r (x, y)) (hVR : ∀ j r x, VR' j r (x, y) = VR j r (x, y))
    (hN : ∀ r x, N' r (x, y) = N r (x, y)) (hS : ∀ k x, S' k (x, y) = S k (x, y)) :
    IsFrozenSampleLaw Q W' ζ' VL' VR' N' S' m y := by
  obtain ⟨𝓗, B, hB, hBc, hC, hG, heq⟩ := h
  have eC : ∀ s : ℝ≥0, {x | s < S' m (x, y)} = {x | s < S m (x, y)} := fun s => by
    ext x; simp only [mem_ofPred_eq, hS]
  refine ⟨𝓗, B, hB, hBc, fun s => by rw [eC]; exact hC s, fun s => ?_, ?_⟩
  · rw [eC]
    refine forall_imageGen (p := fun g => MeasurableSet[𝓗 s] ((fun x => (x, y)) ⁻¹' g ∩ {x | s < S m (x, y)}))
      (fun r hr U hU => ?_) (fun r hr U hU i => ?_) (fun r hr U hU j => ?_) (fun r hr U hU => ?_)
      (fun r hr k => ?_) (fun r hr => ?_)
    · convert hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inl rfl⟩⟩ using 2
      ext x; simp only [mem_preimage, hW]
    · convert hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩ using 2
      ext x; simp only [mem_preimage, hVL]
    · convert hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))⟩⟩ using 2
      ext x; simp only [mem_preimage, hVR]
    · convert hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inr rfl))⟩⟩ using 2
      ext x; simp only [mem_preimage, hN]
    · convert hG s _ ⟨r, hr, Or.inr (Or.inl ⟨k, rfl⟩)⟩ using 2
      ext x; simp only [mem_preimage, mem_ofPred_eq, hS]
    · convert hG s _ ⟨r, hr, Or.inr (Or.inr rfl)⟩ using 2
      ext x; simp only [mem_preimage, mem_ofPred_eq, hζ]
  · filter_upwards [heq] with x hx t ht
    rw [hN, hx t (by rwa [← hS])]

omit mX in
/-- **The frozen-sample law at `x` only reads the sections of the image data at `x`** (mirror). -/
theorem IsFrozenSampleLawFst.congr {Q : Measure Y} {W W' : ℝ≥0 → X × Y → ℝ} {ζ ζ' : X × Y → ℝ≥0∞}
    {VL VL' : Fin nL → ℝ≥0 → X × Y → ℝ} {VR VR' : Fin nR → ℝ≥0 → X × Y → ℝ} {N N' : ℝ≥0 → X × Y → ℝ}
    {S S' : ℕ → X × Y → ℝ≥0} {m : ℕ} {x : X} (h : IsFrozenSampleLawFst Q W ζ VL VR N S m x)
    (hW : ∀ r y, W' r (x, y) = W r (x, y)) (hζ : ∀ y, ζ' (x, y) = ζ (x, y))
    (hVL : ∀ i r y, VL' i r (x, y) = VL i r (x, y)) (hVR : ∀ j r y, VR' j r (x, y) = VR j r (x, y))
    (hN : ∀ r y, N' r (x, y) = N r (x, y)) (hS : ∀ k y, S' k (x, y) = S k (x, y)) :
    IsFrozenSampleLawFst Q W' ζ' VL' VR' N' S' m x := by
  obtain ⟨𝓗, B, hB, hBc, hC, hG, heq⟩ := h
  have eC : ∀ s : ℝ≥0, {y | s < S' m (x, y)} = {y | s < S m (x, y)} := fun s => by
    ext y; simp only [mem_ofPred_eq, hS]
  refine ⟨𝓗, B, hB, hBc, fun s => by rw [eC]; exact hC s, fun s => ?_, ?_⟩
  · rw [eC]
    refine forall_imageGen (p := fun g => MeasurableSet[𝓗 s] ((fun y => (x, y)) ⁻¹' g ∩ {y | s < S m (x, y)}))
      (fun r hr U hU => ?_) (fun r hr U hU i => ?_) (fun r hr U hU j => ?_) (fun r hr U hU => ?_)
      (fun r hr k => ?_) (fun r hr => ?_)
    · convert hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inl rfl⟩⟩ using 2
      ext y; simp only [mem_preimage, hW]
    · convert hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩ using 2
      ext y; simp only [mem_preimage, hVL]
    · convert hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))⟩⟩ using 2
      ext y; simp only [mem_preimage, hVR]
    · convert hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inr rfl))⟩⟩ using 2
      ext y; simp only [mem_preimage, hN]
    · convert hG s _ ⟨r, hr, Or.inr (Or.inl ⟨k, rfl⟩)⟩ using 2
      ext y; simp only [mem_preimage, mem_ofPred_eq, hS]
    · convert hG s _ ⟨r, hr, Or.inr (Or.inr rfl)⟩ using 2
      ext y; simp only [mem_preimage, mem_ofPred_eq, hζ]
  · filter_upwards [heq] with y hy t ht
    rw [hN, hy t (by rwa [← hS])]

end Congr

/-! ### Families over the deterministic frozen time, conditioning curve on `Y` -/

section FamSnd

/-- **The frozen-curve image law at every deterministic frozen time** (conditioning curve on `Y`, image curve on
`X`): the image force points, image noise, caps and rectangle densities of the canonical image at the deterministic
stop `σ`, jointly measurable in `(σ, z)`, such that for almost every frozen conditioning sample `y` and **every**
frozen time `σ` the frozen-sample law holds under `D_σ,m(·, y) · P₁`. -/
structure FrozenFamily (P₁ : Measure X) (P₂ : Measure Y) (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ)
    (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ) (nL nR : ℕ) where
  /-- The image force points of the left image marks at the frozen time `σ`. -/
  VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ
  /-- The image force points of the right image marks at the frozen time `σ`. -/
  VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ
  /-- The image noise at the frozen time `σ`. -/
  N : ℝ≥0 → ℝ≥0 → X × Y → ℝ
  /-- The caps at the frozen time `σ`. -/
  S : ℝ≥0 → ℕ → X × Y → ℝ≥0
  /-- The rectangle densities at the frozen time `σ` (`M(S_jᵐ, σ ∧ S_kᵐ)`). -/
  D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞
  measurable_VL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2
  measurable_VR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2
  continuous_N : ∀ σ z, Continuous (N σ · z)
  N_zero : ∀ σ z, N σ 0 z = 0
  measurable_N : ∀ t, Measurable fun p : ℝ≥0 × (X × Y) => N p.1 t p.2
  measurable_S : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2
  measurable_D : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2
  /-- **The frozen-curve image law at every deterministic frozen time.** -/
  frozen : ∀ m, ∀ᵐ y ∂P₂, ∀ σ : ℝ≥0, IsFrozenSampleLaw (P₁.withDensity fun x => D σ m (x, y))
    (rDrv live xj Wj ζj xk Wk fun _ => σ) (rLife live xj Wj ζj xk Wk fun _ => σ) (VL σ) (VR σ) (N σ) (S σ) m y

variable {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ}
  {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}

namespace FrozenFamily

variable (F : FrozenFamily P₁ P₂ live xj Wj ζj xk Wk nL nR) (τ : Y → ℝ≥0)

/-- The left image force points at the stop `τ` (frozen time `τ(y)` on the fibre over `y`). -/
def VLat : Fin nL → ℝ≥0 → X × Y → ℝ := fun i t z => F.VL (τ z.2) i t z

/-- The right image force points at the stop `τ`. -/
def VRat : Fin nR → ℝ≥0 → X × Y → ℝ := fun j t z => F.VR (τ z.2) j t z

/-- The image noise at the stop `τ`. -/
def Nat : ℝ≥0 → X × Y → ℝ := fun t z => F.N (τ z.2) t z

/-- The caps at the stop `τ`. -/
def Sat : ℕ → X × Y → ℝ≥0 := fun m z => F.S (τ z.2) m z

/-- The rectangle densities at the stop `τ`. -/
def Dat : ℕ → X × Y → ℝ≥0∞ := fun m z => F.D (τ z.2) m z

/-- **The frozen-sample law at an arbitrary stop `τ`** (for instance a stopping time of the usual augmentation):
on the fibre over `y` only the frozen time `τ(y)` is seen. -/
theorem frozen_at (m : ℕ) :
    ∀ᵐ y ∂P₂, IsFrozenSampleLaw (P₁.withDensity fun x => F.Dat τ m (x, y)) (rDrv live xj Wj ζj xk Wk τ)
      (rLife live xj Wj ζj xk Wk τ) (F.VLat τ) (F.VRat τ) (F.Nat τ) (F.Sat τ) m y := by
  filter_upwards [F.frozen m] with y hy
  exact (hy (τ y)).congr (fun r x => (cImg_congr_of_eq (z := (x, y)) (τ := fun z => τ z.2)
      (τ₀ := fun _ => τ y) rfl).2 r) (fun x => (cImg_congr_of_eq (z := (x, y)) (τ := fun z => τ z.2)
      (τ₀ := fun _ => τ y) rfl).1) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

variable {τ}

theorem measurable_VLat (hτ : Measurable τ) (i : Fin nL) (t : ℝ≥0) : Measurable (F.VLat τ i t) :=
  (F.measurable_VL i t).comp ((hτ.comp measurable_snd).prodMk measurable_id)

theorem measurable_VRat (hτ : Measurable τ) (j : Fin nR) (t : ℝ≥0) : Measurable (F.VRat τ j t) :=
  (F.measurable_VR j t).comp ((hτ.comp measurable_snd).prodMk measurable_id)

theorem measurable_Nat (hτ : Measurable τ) (t : ℝ≥0) : Measurable (F.Nat τ t) :=
  (F.measurable_N t).comp ((hτ.comp measurable_snd).prodMk measurable_id)

theorem measurable_Sat (hτ : Measurable τ) (m : ℕ) : Measurable (F.Sat τ m) :=
  (F.measurable_S m).comp ((hτ.comp measurable_snd).prodMk measurable_id)

theorem measurable_Dat (hτ : Measurable τ) (m : ℕ) : Measurable (F.Dat τ m) :=
  (F.measurable_D m).comp ((hτ.comp measurable_snd).prodMk measurable_id)

end FrozenFamily

/-- **The per-stop rectangle data for a frozen family** at the stop `τ` (A22's (1.7) with the stopped records, the
stopped-record conditions of the substituted image data, the cover and the per-cap paths). -/
structure FamilyRect (F : FrozenFamily P₁ P₂ live xj Wj ζj xk Wk nL nR) (a : ℝ) (ΘL : ℝ≥0 → Y → Fin nL → ℝ)
    (ΘR : ℝ≥0 → Y → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (μ : Measure (X × Y)) (τ : Y → ℝ≥0)
    (𝓔 : Set (Set Y)) where
  /-- The image curve's stopped record on rectangle `m`. -/
  𝓐 : ℕ → MeasurableSpace X
  /-- The conditioning curve's stopped record on rectangle `m`. -/
  𝓑 : ℕ → MeasurableSpace Y
  le_A : ∀ m, 𝓐 m ≤ mX
  le_B : ∀ m, 𝓑 m ≤ mY
  dens : ∀ m (f : X × Y → ℝ≥0∞), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
    ∫⁻ z, f z ∂μ = ∫⁻ z, f z * F.Dat τ m z ∂(P₁.prod P₂)
  measurable_stopExp : ∀ m (a' : ℝ) (t : ℝ≥0),
    Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (stopExp a' (F.Nat τ) (F.Sat τ m) t)
  trace_stopped : ∀ m (s : ℝ≥0) (B : Set Y), B ∈ 𝓔 →
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Prod.snd ⁻¹' B ∩ {z | s < F.Sat τ m z})
  trace_gen : ∀ m (s : ℝ≥0), ∀ g ∈ imageGen (rDrv live xj Wj ζj xk Wk τ) (rLife live xj Wj ζj xk Wk τ)
      (F.VLat τ) (F.VRat τ) (F.Nat τ) (F.Sat τ) s,
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (g ∩ {z | s < F.Sat τ m z})
  cover : ∀ᵐ z ∂μ, live (τ z.2) z.2 →
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < rLife live xj Wj ζj xk Wk τ z → ∃ m, t ≤ F.Sat τ m z
  path : ∀ m, ∀ᵐ z ∂μ, live (τ z.2) z.2 →
    Sec2.IsSLEPathUpTo a (ΘL (τ z.2) z.2) (ΘR (τ z.2) z.2) ρL ρR (fun t => rDrv live xj Wj ζj xk Wk τ t z)
      (fun i t => F.VLat τ i t z) (fun j t => F.VRat τ j t z) (fun t => F.Nat τ t z)
      (min (F.Sat τ m z : ℝ≥0∞) (rLife live xj Wj ζj xk Wk τ z))

/-- **The rectangle input at the stop `τ` from a frozen family and the per-stop rectangle data.** -/
def FrozenFamily.toInput (F : FrozenFamily P₁ P₂ live xj Wj ζj xk Wk nL nR) {a : ℝ}
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {μ : Measure (X × Y)} {τ : Y → ℝ≥0} {𝓔 : Set (Set Y)} (hτ : Measurable τ)
    (R : FamilyRect F a ΘL ΘR ρL ρR μ τ 𝓔) :
    FrozenRectInput a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ 𝓔 where
  VL := F.VLat τ
  VR := F.VRat τ
  N := F.Nat τ
  S := F.Sat τ
  𝓐 := R.𝓐
  𝓑 := R.𝓑
  D := F.Dat τ
  measurable_VL := F.measurable_VLat hτ
  measurable_VR := F.measurable_VRat hτ
  continuous_N z := F.continuous_N (τ z.2) z
  N_zero z := F.N_zero (τ z.2) z
  measurable_N := F.measurable_Nat hτ
  measurable_S := F.measurable_Sat hτ
  le_A := R.le_A
  le_B := R.le_B
  measurable_D := F.measurable_Dat hτ
  dens := R.dens
  measurable_stopExp := R.measurable_stopExp
  trace_stopped := R.trace_stopped
  trace_gen := R.trace_gen
  frozen := F.frozen_at τ
  cover := R.cover
  path := R.path

/-- **A.1's rectangle core (conditioning curve on `Y`) from the frozen-curve law at deterministic frozen times**:
(m1)–(m4), a `FrozenFamily`, and at every stopping time of the usual augmentation the per-stop rectangle data give
`IsRectImageCore`. -/
theorem isRectImageCore_of_family {a : ℝ} {𝓕k : Filtration ℝ≥0 mY} {μ : Measure (X × Y)}
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hm1 : open scoped Classical in
      IsStronglyProgressive (usualAugmentation 𝓕k P₂) fun t y => {y | live t y}.indicator (fun _ => (1 : ℝ)) y)
    (hm2L : IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘL)
    (hm2R : IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘR)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hm4 : Measurable (fun p : ℝ≥0 × (X × Y) => rLife live xj Wj ζj xk Wk (fun _ => p.1) p.2))
    (F : FrozenFamily P₁ P₂ live xj Wj ζj xk Wk nL nR)
    (hR : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
      Nonempty (FamilyRect F a ΘL ΘR ρL ρR μ τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    IsRectImageCore a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR :=
  isRectImageCore_of_frozen hm1 hm2L hm2R hm3 hm4 fun τ hτ =>
    (hR τ hτ).map (F.toInput (measurable_of_isStoppingTime hτ))

end FamSnd

/-! ### Families over the deterministic frozen time, conditioning curve on `X` -/

section FamFst

/-- **The frozen-curve image law at every deterministic frozen time, conditioning curve on `X`** (image curve on
`Y`): the mirror of `FrozenFamily`. -/
structure FrozenFamilyFst (P₁ : Measure X) (P₂ : Measure Y) (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ)
    (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ) (nL nR : ℕ) where
  /-- The image force points of the left image marks at the frozen time `σ`. -/
  VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ
  /-- The image force points of the right image marks at the frozen time `σ`. -/
  VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ
  /-- The image noise at the frozen time `σ`. -/
  N : ℝ≥0 → ℝ≥0 → X × Y → ℝ
  /-- The caps at the frozen time `σ`. -/
  S : ℝ≥0 → ℕ → X × Y → ℝ≥0
  /-- The rectangle densities at the frozen time `σ` (`M(σ ∧ S_kᵐ, S_jᵐ)`). -/
  D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞
  measurable_VL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2
  measurable_VR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2
  continuous_N : ∀ σ z, Continuous (N σ · z)
  N_zero : ∀ σ z, N σ 0 z = 0
  measurable_N : ∀ t, Measurable fun p : ℝ≥0 × (X × Y) => N p.1 t p.2
  measurable_S : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2
  measurable_D : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2
  /-- **The frozen-curve image law at every deterministic frozen time.** -/
  frozen : ∀ m, ∀ᵐ x ∂P₁, ∀ σ : ℝ≥0, IsFrozenSampleLawFst (P₂.withDensity fun y => D σ m (x, y))
    (rDrvFst live xj Wj ζj xk Wk fun _ => σ) (rLifeFst live xj Wj ζj xk Wk fun _ => σ) (VL σ) (VR σ) (N σ) (S σ)
    m x

variable {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ}
  {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}

namespace FrozenFamilyFst

variable (F : FrozenFamilyFst P₁ P₂ live xj Wj ζj xk Wk nL nR) (τ : X → ℝ≥0)

/-- The left image force points at the stop `τ` (frozen time `τ(x)` on the fibre over `x`). -/
def VLat : Fin nL → ℝ≥0 → X × Y → ℝ := fun i t z => F.VL (τ z.1) i t z

/-- The right image force points at the stop `τ`. -/
def VRat : Fin nR → ℝ≥0 → X × Y → ℝ := fun j t z => F.VR (τ z.1) j t z

/-- The image noise at the stop `τ`. -/
def Nat : ℝ≥0 → X × Y → ℝ := fun t z => F.N (τ z.1) t z

/-- The caps at the stop `τ`. -/
def Sat : ℕ → X × Y → ℝ≥0 := fun m z => F.S (τ z.1) m z

/-- The rectangle densities at the stop `τ`. -/
def Dat : ℕ → X × Y → ℝ≥0∞ := fun m z => F.D (τ z.1) m z

/-- **The frozen-sample law at an arbitrary stop `τ`** (mirror of `FrozenFamily.frozen_at`). -/
theorem frozen_at (m : ℕ) :
    ∀ᵐ x ∂P₁, IsFrozenSampleLawFst (P₂.withDensity fun y => F.Dat τ m (x, y)) (rDrvFst live xj Wj ζj xk Wk τ)
      (rLifeFst live xj Wj ζj xk Wk τ) (F.VLat τ) (F.VRat τ) (F.Nat τ) (F.Sat τ) m x := by
  filter_upwards [F.frozen m] with x hx
  exact (hx (τ x)).congr (fun r y => (cImg_congr_of_eq (z := (x, y)) (τ := fun z => τ z.1)
      (τ₀ := fun _ => τ x) rfl).2 r) (fun y => (cImg_congr_of_eq (z := (x, y)) (τ := fun z => τ z.1)
      (τ₀ := fun _ => τ x) rfl).1) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

variable {τ}

theorem measurable_VLat (hτ : Measurable τ) (i : Fin nL) (t : ℝ≥0) : Measurable (F.VLat τ i t) :=
  (F.measurable_VL i t).comp ((hτ.comp measurable_fst).prodMk measurable_id)

theorem measurable_VRat (hτ : Measurable τ) (j : Fin nR) (t : ℝ≥0) : Measurable (F.VRat τ j t) :=
  (F.measurable_VR j t).comp ((hτ.comp measurable_fst).prodMk measurable_id)

theorem measurable_Nat (hτ : Measurable τ) (t : ℝ≥0) : Measurable (F.Nat τ t) :=
  (F.measurable_N t).comp ((hτ.comp measurable_fst).prodMk measurable_id)

theorem measurable_Sat (hτ : Measurable τ) (m : ℕ) : Measurable (F.Sat τ m) :=
  (F.measurable_S m).comp ((hτ.comp measurable_fst).prodMk measurable_id)

theorem measurable_Dat (hτ : Measurable τ) (m : ℕ) : Measurable (F.Dat τ m) :=
  (F.measurable_D m).comp ((hτ.comp measurable_fst).prodMk measurable_id)

end FrozenFamilyFst

/-- **The per-stop rectangle data for a frozen family, conditioning curve on `X`** (mirror of `FamilyRect`). -/
structure FamilyRectFst (F : FrozenFamilyFst P₁ P₂ live xj Wj ζj xk Wk nL nR) (a : ℝ)
    (ΘL : ℝ≥0 → X → Fin nL → ℝ) (ΘR : ℝ≥0 → X → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (μ : Measure (X × Y)) (τ : X → ℝ≥0) (𝓔 : Set (Set X)) where
  /-- The conditioning curve's stopped record on rectangle `m`. -/
  𝓐 : ℕ → MeasurableSpace X
  /-- The image curve's stopped record on rectangle `m`. -/
  𝓑 : ℕ → MeasurableSpace Y
  le_A : ∀ m, 𝓐 m ≤ mX
  le_B : ∀ m, 𝓑 m ≤ mY
  dens : ∀ m (f : X × Y → ℝ≥0∞), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
    ∫⁻ z, f z ∂μ = ∫⁻ z, f z * F.Dat τ m z ∂(P₁.prod P₂)
  measurable_stopExp : ∀ m (a' : ℝ) (t : ℝ≥0),
    Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (stopExp a' (F.Nat τ) (F.Sat τ m) t)
  trace_stopped : ∀ m (s : ℝ≥0) (B : Set X), B ∈ 𝓔 →
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Prod.fst ⁻¹' B ∩ {z | s < F.Sat τ m z})
  trace_gen : ∀ m (s : ℝ≥0), ∀ g ∈ imageGen (rDrvFst live xj Wj ζj xk Wk τ) (rLifeFst live xj Wj ζj xk Wk τ)
      (F.VLat τ) (F.VRat τ) (F.Nat τ) (F.Sat τ) s,
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (g ∩ {z | s < F.Sat τ m z})
  cover : ∀ᵐ z ∂μ, live (τ z.1) z.1 →
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < rLifeFst live xj Wj ζj xk Wk τ z → ∃ m, t ≤ F.Sat τ m z
  path : ∀ m, ∀ᵐ z ∂μ, live (τ z.1) z.1 →
    Sec2.IsSLEPathUpTo a (ΘL (τ z.1) z.1) (ΘR (τ z.1) z.1) ρL ρR (fun t => rDrvFst live xj Wj ζj xk Wk τ t z)
      (fun i t => F.VLat τ i t z) (fun j t => F.VRat τ j t z) (fun t => F.Nat τ t z)
      (min (F.Sat τ m z : ℝ≥0∞) (rLifeFst live xj Wj ζj xk Wk τ z))

/-- **The rectangle input at the stop `τ` from a frozen family, conditioning curve on `X`.** -/
def FrozenFamilyFst.toInput (F : FrozenFamilyFst P₁ P₂ live xj Wj ζj xk Wk nL nR) {a : ℝ}
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {μ : Measure (X × Y)} {τ : X → ℝ≥0} {𝓔 : Set (Set X)} (hτ : Measurable τ)
    (R : FamilyRectFst F a ΘL ΘR ρL ρR μ τ 𝓔) :
    FrozenRectInputFst a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ 𝓔 where
  VL := F.VLat τ
  VR := F.VRat τ
  N := F.Nat τ
  S := F.Sat τ
  𝓐 := R.𝓐
  𝓑 := R.𝓑
  D := F.Dat τ
  measurable_VL := F.measurable_VLat hτ
  measurable_VR := F.measurable_VRat hτ
  continuous_N z := F.continuous_N (τ z.1) z
  N_zero z := F.N_zero (τ z.1) z
  measurable_N := F.measurable_Nat hτ
  measurable_S := F.measurable_Sat hτ
  le_A := R.le_A
  le_B := R.le_B
  measurable_D := F.measurable_Dat hτ
  dens := R.dens
  measurable_stopExp := R.measurable_stopExp
  trace_stopped := R.trace_stopped
  trace_gen := R.trace_gen
  frozen := F.frozen_at τ
  cover := R.cover
  path := R.path

/-- **A.1's rectangle core (conditioning curve on `X`) from the frozen-curve law at deterministic frozen
times.** -/
theorem isRectImageCoreFst_of_family {a : ℝ} {𝓕k : Filtration ℝ≥0 mX} {μ : Measure (X × Y)}
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hm1 : open scoped Classical in
      IsStronglyProgressive (usualAugmentation 𝓕k P₁) fun t x => {x | live t x}.indicator (fun _ => (1 : ℝ)) x)
    (hm2L : IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘL)
    (hm2R : IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘR)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hm4 : Measurable (fun p : ℝ≥0 × (X × Y) => rLifeFst live xj Wj ζj xk Wk (fun _ => p.1) p.2))
    (F : FrozenFamilyFst P₁ P₂ live xj Wj ζj xk Wk nL nR)
    (hR : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (FamilyRectFst F a ΘL ΘR ρL ρR μ τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    IsRectImageCoreFst a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR :=
  isRectImageCoreFst_of_frozen hm1 hm2L hm2R hm3 hm4 fun τ hτ =>
    (hR τ hτ).map (F.toInput (measurable_of_isStoppingTime hτ))

end FamFst

end InteractingSLE.ZhanGT4.A1Frozen
