/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawFrozen
import InteractingSLE.Spec.ZhanGT4.A1FamilyRect

/-!
# Zhan's A.1 under R83: the C families from one-sample laws and primitive per-rectangle inputs

Packet PROVE-A1-RECTLAW2 (R83). A1-FAMILY's constructors, restated for the C families (image noise continuous before
each cap only):

* **`FrozenFamilyC.ofSampleLaw`**, **`FrozenFamilyFstC.ofSampleLaw`**: a C family from jointly measurable data and the
  one-sample laws `A1Family.IsSeedSampleLaw` of the sections, for almost every frozen sample and every frozen time;
* **`FamilyRectC.ofRect`**, **`FamilyRectFstC.ofRect`**: the per-stop data from (1.7) in the source's form (exit-time
  rectangle law plus optional sampling in the conditioning coordinate), the stopped-record measurability, the clock
  exhaustion and the deterministic image equations with the noise equal to the residual before the cap.

The proofs are A1-FAMILY's, verbatim up to the weakened continuity clause.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open A1Canon A1Ref A1Core A1Frozen A1Family

section FamiliesC

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ}

/-- **A `FrozenFamilyC` from the one-sample laws of the sections** (conditioning curve on `Y`): jointly measurable
data indexed by the frozen time `σ`, a noise from `0` continuous before each cap, and for every cap `m`, almost
every frozen sample `y` and every frozen time `σ` the one-sample law of the sections at `y` of the canonical image at
the stop `σ` under the tilted law `D σ m (·, y) · P₁`. -/
def FrozenFamilyC.ofSampleLaw {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → Y → Prop} {xj : ℝ}
    {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (N : ℝ≥0 → ℝ≥0 → X × Y → ℝ) (S : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2)
    (hNc : ∀ σ m z, ContinuousOn (N σ · z) (Icc 0 (S σ m z))) (hN0 : ∀ σ z, N σ 0 z = 0)
    (hN : ∀ t, Measurable fun p : ℝ≥0 × (X × Y) => N p.1 t p.2)
    (hS : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2)
    (hD : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2)
    (hlaw : ∀ m, ∀ᵐ y ∂P₂, ∀ σ : ℝ≥0, IsSeedSampleLaw (P₁.withDensity fun x => D σ m (x, y))
      (fun t x => rDrv live xj Wj ζj xk Wk (fun _ => σ) t (x, y))
      (fun x => rLife live xj Wj ζj xk Wk (fun _ => σ) (x, y)) (fun i t x => VL σ i t (x, y))
      (fun j t x => VR σ j t (x, y)) (fun t x => N σ t (x, y)) (fun k x => S σ k (x, y)) m) :
    FrozenFamilyC P₁ P₂ live xj Wj ζj xk Wk nL nR where
  VL := VL
  VR := VR
  N := N
  S := S
  D := D
  measurable_VL := hVL
  measurable_VR := hVR
  continuousOn_N := hNc
  N_zero := hN0
  measurable_N := hN
  measurable_S := hS
  measurable_D := hD
  frozen m := (hlaw m).mono fun _ hy σ => A1Family.IsSeedSampleLaw.isFrozenSampleLaw (hy σ)

/-- **A `FrozenFamilyFstC` from the one-sample laws of the sections** (conditioning curve on `X`, mirror). -/
def FrozenFamilyFstC.ofSampleLaw {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → X → Prop} {xj : ℝ}
    {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}
    (VL : ℝ≥0 → Fin nL → ℝ≥0 → X × Y → ℝ) (VR : ℝ≥0 → Fin nR → ℝ≥0 → X × Y → ℝ)
    (N : ℝ≥0 → ℝ≥0 → X × Y → ℝ) (S : ℝ≥0 → ℕ → X × Y → ℝ≥0) (D : ℝ≥0 → ℕ → X × Y → ℝ≥0∞)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × (X × Y) => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × (X × Y) => VR p.1 j t p.2)
    (hNc : ∀ σ m z, ContinuousOn (N σ · z) (Icc 0 (S σ m z))) (hN0 : ∀ σ z, N σ 0 z = 0)
    (hN : ∀ t, Measurable fun p : ℝ≥0 × (X × Y) => N p.1 t p.2)
    (hS : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2)
    (hD : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2)
    (hlaw : ∀ m, ∀ᵐ x ∂P₁, ∀ σ : ℝ≥0, IsSeedSampleLaw (P₂.withDensity fun y => D σ m (x, y))
      (fun t y => rDrvFst live xj Wj ζj xk Wk (fun _ => σ) t (x, y))
      (fun y => rLifeFst live xj Wj ζj xk Wk (fun _ => σ) (x, y)) (fun i t y => VL σ i t (x, y))
      (fun j t y => VR σ j t (x, y)) (fun t y => N σ t (x, y)) (fun k y => S σ k (x, y)) m) :
    FrozenFamilyFstC P₁ P₂ live xj Wj ζj xk Wk nL nR where
  VL := VL
  VR := VR
  N := N
  S := S
  D := D
  measurable_VL := hVL
  measurable_VR := hVR
  continuousOn_N := hNc
  N_zero := hN0
  measurable_N := hN
  measurable_S := hS
  measurable_D := hD
  frozen m := (hlaw m).mono fun _ hx σ => A1Family.IsSeedSampleLaw.isFrozenSampleLawFst (hx σ)

end FamiliesC

section RectSnd

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ} {P₁ : Measure X}
  {P₂ : Measure Y} {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ}
  {Wk : ℝ≥0 → Y → ℝ}

/-- **The per-stop rectangle data from primitive per-rectangle inputs** (conditioning curve on `Y`):

* (1.7) in the source's form: the exit-time rectangle law on the two stopped records `𝓐 m`, `𝓑 m` with density
  `D₀ m` (`M(S_jᵐ, S_kᵐ)`), and optional sampling in the conditioning coordinate down to `𝓑' m ≤ 𝓑 m` (the record
  stopped at `τ ∧ S_kᵐ`) with the family's density at the stop (`M(S_jᵐ, τ ∧ S_kᵐ)`);
* the stopped-record measurability: the noise stopped at the cap and the cap; the events of `𝓔` before the cap; the
  image data before the cap agree with record-measurable functions; the cap comparisons; the cap precedes the
  lifetime;
* the clock exhaustion (caps above the canonical clock at every pre-contact own time);
* the deterministic image equations of the data stopped at the cap, and the noise equal to the residual before the
  cap. -/
def FamilyRectC.ofRect (F : FrozenFamilyC P₁ P₂ live xj Wj ζj xk Wk nL nR) {a : ℝ}
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {μ : Measure (X × Y)} {τ : Y → ℝ≥0} {𝓔 : Set (Set Y)} [SFinite P₁] [SFinite P₂] [IsFiniteMeasure μ]
    (𝓐 : ℕ → MeasurableSpace X) (𝓑 𝓑' : ℕ → MeasurableSpace Y) (D₀ : ℕ → X × Y → ℝ≥0∞)
    (hA : ∀ m, 𝓐 m ≤ mX) (hB' : ∀ m, 𝓑' m ≤ 𝓑 m) (hB : ∀ m, 𝓑 m ≤ mY) (hτ : Measurable τ)
    (hD₀ : ∀ m, Measurable (D₀ m))
    (hrect : ∀ m A B, MeasurableSet[𝓐 m] A → MeasurableSet[𝓑 m] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ m z ∂(P₁.prod P₂))
    (hopt : ∀ m, ∀ᵐ x ∂P₁, ∀ B, MeasurableSet[𝓑' m] B →
      ∫⁻ y in B, D₀ m (x, y) ∂P₂ = ∫⁻ y in B, F.Dat τ m (x, y) ∂P₂)
    (hNs : ∀ m t, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)]
      fun z => F.Nat τ (min t (F.Sat τ m z)) z)
    (hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] (F.Sat τ m))
    (hstop : ∀ m (s : ℝ≥0) (B : Set Y), B ∈ 𝓔 →
      MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] (Prod.snd ⁻¹' B ∩ {z | s < F.Sat τ m z}))
    (hgW : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] f ∧
      ∀ z, r < F.Sat τ m z → rDrv live xj Wj ζj xk Wk τ r z = f z)
    (hgVL : ∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] f ∧
      ∀ z, r < F.Sat τ m z → F.VLat τ i r z = f z)
    (hgVR : ∀ m j r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] f ∧
      ∀ z, r < F.Sat τ m z → F.VRat τ j r z = f z)
    (hgN : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)] f ∧
      ∀ z, r < F.Sat τ m z → F.Nat τ r z = f z)
    (hgS : ∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)]
      ({z | F.Sat τ k z ≤ r} ∩ {z | r < F.Sat τ m z}))
    (hgζ : ∀ m z, (F.Sat τ m z : ℝ≥0∞) ≤ rLife live xj Wj ζj xk Wk τ z)
    (hcov : ∀ᵐ z ∂μ, live (τ z.2) z.2 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.1))
        (ζj z.1) xk (Strip.extPath (Wk · z.2)) (τ z.2) →
      ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.1)) xk (Strip.extPath (Wk · z.2)) (τ z.2) s ≤ F.Sat τ m z)
    (ha : 0 < a)
    (hgeom : ∀ m, ∀ᵐ z ∂μ, live (τ z.2) z.2 → SeedImageGeometry (ΘL (τ z.2) z.2) (ΘR (τ z.2) z.2) ρL ρR
      (fun t => rDrv live xj Wj ζj xk Wk τ (min t (F.Sat τ m z)) z)
      (fun i t => F.VLat τ i (min t (F.Sat τ m z)) z) (fun j t => F.VRat τ j (min t (F.Sat τ m z)) z)
      (F.Sat τ m z))
    (hres : ∀ m, ∀ᵐ z ∂μ, live (τ z.2) z.2 → ∀ t : ℝ≥0, t < F.Sat τ m z →
      F.Nat τ t z = seedCapacityNoise a ρL ρR (rDrv live xj Wj ζj xk Wk τ · z) (fun i t => F.VLat τ i t z)
        (fun j t => F.VRat τ j t z) t) :
    FamilyRectC F a ΘL ΘR ρL ρR μ τ 𝓔 where
  𝓐 := 𝓐
  𝓑 := 𝓑'
  le_A := hA
  le_B m := (hB' m).trans (hB m)
  dens m f hf := dens_of_rect_optional (hA m) (hB' m) (hB m) (hD₀ m) (F.measurable_Dat hτ m) (hrect m) (hopt m) f hf
  measurable_stopExp m a' t := measurable_stopExp_of (𝓜 := @Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m)) t
    (hNs m t) (hSm m) a'
  trace_stopped := hstop
  trace_gen m s := measurableSet_imageGen_inter (𝓜 := @Prod.instMeasurableSpace X Y (𝓐 m) (𝓑' m))
    (hgW m) (hgVL m) (hgVR m) (hgN m) (hgS m) (fun _ => measurableSet_lt measurable_const (hSm m)) (hgζ m) s
  cover := hcov.mono fun _ hz hlive => cover_of_clock hlive (hz hlive)
  path m := ae_path_of_geometry (live := fun z : X × Y => live (τ z.2) z.2) ha m (hgeom m) (hres m)

end RectSnd

section RectFst

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ} {P₁ : Measure X}
  {P₂ : Measure Y} {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ}
  {Wk : ℝ≥0 → X → ℝ}

/-- **The per-stop rectangle data from primitive per-rectangle inputs** (conditioning curve on `X`, mirror of
`FamilyRectC.ofRect`: the optional sampling is in the first coordinate, down to `𝓐' m ≤ 𝓐 m`). -/
def FamilyRectFstC.ofRect (F : FrozenFamilyFstC P₁ P₂ live xj Wj ζj xk Wk nL nR) {a : ℝ}
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {μ : Measure (X × Y)} {τ : X → ℝ≥0} {𝓔 : Set (Set X)} [SFinite P₁] [SFinite P₂] [IsFiniteMeasure μ]
    (𝓐 𝓐' : ℕ → MeasurableSpace X) (𝓑 : ℕ → MeasurableSpace Y) (D₀ : ℕ → X × Y → ℝ≥0∞)
    (hA' : ∀ m, 𝓐' m ≤ 𝓐 m) (hA : ∀ m, 𝓐 m ≤ mX) (hB : ∀ m, 𝓑 m ≤ mY) (hτ : Measurable τ)
    (hD₀ : ∀ m, Measurable (D₀ m))
    (hrect : ∀ m A B, MeasurableSet[𝓐 m] A → MeasurableSet[𝓑 m] B →
      μ (A ×ˢ B) = ∫⁻ z in A ×ˢ B, D₀ m z ∂(P₁.prod P₂))
    (hopt : ∀ m, ∀ᵐ y ∂P₂, ∀ A, MeasurableSet[𝓐' m] A →
      ∫⁻ x in A, D₀ m (x, y) ∂P₁ = ∫⁻ x in A, F.Dat τ m (x, y) ∂P₁)
    (hNs : ∀ m t, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)]
      fun z => F.Nat τ (min t (F.Sat τ m z)) z)
    (hSm : ∀ m, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] (F.Sat τ m))
    (hstop : ∀ m (s : ℝ≥0) (B : Set X), B ∈ 𝓔 →
      MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] (Prod.fst ⁻¹' B ∩ {z | s < F.Sat τ m z}))
    (hgW : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] f ∧
      ∀ z, r < F.Sat τ m z → rDrvFst live xj Wj ζj xk Wk τ r z = f z)
    (hgVL : ∀ m i r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] f ∧
      ∀ z, r < F.Sat τ m z → F.VLat τ i r z = f z)
    (hgVR : ∀ m j r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] f ∧
      ∀ z, r < F.Sat τ m z → F.VRat τ j r z = f z)
    (hgN : ∀ m r, ∃ f : X × Y → ℝ, Measurable[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)] f ∧
      ∀ z, r < F.Sat τ m z → F.Nat τ r z = f z)
    (hgS : ∀ m k r, MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)]
      ({z | F.Sat τ k z ≤ r} ∩ {z | r < F.Sat τ m z}))
    (hgζ : ∀ m z, (F.Sat τ m z : ℝ≥0∞) ≤ rLifeFst live xj Wj ζj xk Wk τ z)
    (hcov : ∀ᵐ z ∂μ, live (τ z.1) z.1 → ∀ s : ℝ≥0, (s : ℝ≥0∞) < A2X.contactTime xj (Strip.extPath (Wj · z.2))
        (ζj z.2) xk (Strip.extPath (Wk · z.1)) (τ z.1) →
      ∃ m, A1Ref.imgClk xj (Strip.extPath (Wj · z.2)) xk (Strip.extPath (Wk · z.1)) (τ z.1) s ≤ F.Sat τ m z)
    (ha : 0 < a)
    (hgeom : ∀ m, ∀ᵐ z ∂μ, live (τ z.1) z.1 → SeedImageGeometry (ΘL (τ z.1) z.1) (ΘR (τ z.1) z.1) ρL ρR
      (fun t => rDrvFst live xj Wj ζj xk Wk τ (min t (F.Sat τ m z)) z)
      (fun i t => F.VLat τ i (min t (F.Sat τ m z)) z) (fun j t => F.VRat τ j (min t (F.Sat τ m z)) z)
      (F.Sat τ m z))
    (hres : ∀ m, ∀ᵐ z ∂μ, live (τ z.1) z.1 → ∀ t : ℝ≥0, t < F.Sat τ m z →
      F.Nat τ t z = seedCapacityNoise a ρL ρR (rDrvFst live xj Wj ζj xk Wk τ · z) (fun i t => F.VLat τ i t z)
        (fun j t => F.VRat τ j t z) t) :
    FamilyRectFstC F a ΘL ΘR ρL ρR μ τ 𝓔 where
  𝓐 := 𝓐'
  𝓑 := 𝓑
  le_A m := (hA' m).trans (hA m)
  le_B := hB
  dens m f hf := dens_of_rect_optional_fst (hA' m) (hA m) (hB m) (hD₀ m) (F.measurable_Dat hτ m) (hrect m)
    (hopt m) f hf
  measurable_stopExp m a' t := measurable_stopExp_of (𝓜 := @Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m)) t
    (hNs m t) (hSm m) a'
  trace_stopped := hstop
  trace_gen m s := measurableSet_imageGen_inter (𝓜 := @Prod.instMeasurableSpace X Y (𝓐' m) (𝓑 m))
    (hgW m) (hgVL m) (hgVR m) (hgN m) (hgS m) (fun _ => measurableSet_lt measurable_const (hSm m)) (hgζ m) s
  cover := hcov.mono fun _ hz hlive => cover_of_clock_fst hlive (hz hlive)
  path m := ae_path_of_geometry (live := fun z : X × Y => live (τ z.1) z.1) ha m (hgeom m) (hres m)

end RectFst

end InteractingSLE.ZhanGT4.A1RLaw
