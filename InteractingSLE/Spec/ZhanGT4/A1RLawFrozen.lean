/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RectLawCore
import InteractingSLE.Spec.ZhanGT4.A1FrozenFamily

/-!
# Zhan's A.1 under R83: the frozen-curve inputs with a noise continuous only before each cap

Packet PROVE-A1-RECTLAW2 (R83). A1-FROZEN's `FrozenRectInput`, `FrozenFamily` and their mirrors ask the image noise to
be continuous on all of `ℝ≥0` at every sample. R83 weakens this to continuity on each cap interval `[0, S m]`, the
clause of A1-RECTLAW's `IsRectImageCoreC`. This file restates A1-FROZEN's inputs with the weakened clause and
re-proves their assembly into the C cores:

* `fib_of_agree_of_continuousOn`, `fib_of_agree_fst_of_continuousOn`: the frozen-sample fibre law for a noise continuous
  before the cap (A1-RECTLAW's `isStoppedBM_of_agree_of_continuousOn`);
* **`FrozenRectInputC`**, **`isRectImageCoreC_of_frozen`**, and the mirrors `FrozenRectInputFstC`,
  **`isRectImageCoreFstC_of_frozen`**;
* **`FrozenFamilyC`**, `FamilyRectC`, **`isRectImageCoreC_of_family`**, and the mirrors `FrozenFamilyFstC`,
  `FamilyRectFstC`, **`isRectImageCoreFstC_of_family`**;
* `FrozenFamily.toC`, `FamilyRect.toC` and mirrors: the old inputs give the new ones.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open A1Canon A1Ref A1Core A1Frozen A1RectLaw

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-! ### The fibre law for a noise continuous before the cap -/

section Fib

/-- **`A1Core.fib_of_agree` for a noise continuous before the cap only.** -/
theorem fib_of_agree_of_continuousOn {P₁ : Measure X} {D : X × Y → ℝ≥0∞} (hD : Measurable D) {y : Y}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    {𝓗' : Filtration ℝ≥0 mX} {B : ℝ≥0 → X → ℝ}
    (hB : IsFilteredBrownianReal 𝓗' B (P₁.withDensity fun x => D (x, y))) (hBc : ∀ x, Continuous (B · x))
    (hNc : ∀ z, ContinuousOn (N · z) (Icc 0 (S z))) (hNa : ∀ t, Measurable[𝓖 t] (N t))
    (hS : IsStoppingTime (sectionFiltration 𝓖 y) fun x => (S (x, y) : WithTop ℝ≥0))
    (hagree : ∀ (s : ℝ≥0) (A : Set X), MeasurableSet[sectionFiltration 𝓖 y s] A →
      MeasurableSet[𝓗' s] (A ∩ {x | s < S (x, y)}))
    (heq : ∀ᵐ x ∂(P₁.withDensity fun x => D (x, y)), ∀ t, t ≤ S (x, y) → B t x = N t (x, y)) :
    ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₁ =
        ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₁ := by
  have : IsProbabilityMeasure (P₁.withDensity fun x => D (x, y)) := hB.isProbabilityMeasure'
  have hNy : ∀ t, Measurable[sectionFiltration 𝓖 y t] fun x => N t (x, y) := fun t =>
    (hNa t).comp (comap_measurable fun x => (x, y))
  exact fib_of_isStoppedBM_withDensity hD
    (isStoppedBM_of_agree_of_continuousOn hB hBc (fun x => hNc (x, y)) hNy hS hagree heq)

/-- The mirror of `fib_of_agree_of_continuousOn` (frozen conditioning sample `x ∈ X`, image curve on `Y`). -/
theorem fib_of_agree_fst_of_continuousOn {P₂ : Measure Y} {D : X × Y → ℝ≥0∞} (hD : Measurable D) {x : X}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    {𝓗' : Filtration ℝ≥0 mY} {B : ℝ≥0 → Y → ℝ}
    (hB : IsFilteredBrownianReal 𝓗' B (P₂.withDensity fun y => D (x, y))) (hBc : ∀ y, Continuous (B · y))
    (hNc : ∀ z, ContinuousOn (N · z) (Icc 0 (S z))) (hNa : ∀ t, Measurable[𝓖 t] (N t))
    (hS : IsStoppingTime (sectionFiltrationFst 𝓖 x) fun y => (S (x, y) : WithTop ℝ≥0))
    (hagree : ∀ (s : ℝ≥0) (A : Set Y), MeasurableSet[sectionFiltrationFst 𝓖 x s] A →
      MeasurableSet[𝓗' s] (A ∩ {y | s < S (x, y)}))
    (heq : ∀ᵐ y ∂(P₂.withDensity fun y => D (x, y)), ∀ t, t ≤ S (x, y) → B t y = N t (x, y)) :
    ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₂ =
        ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₂ := by
  have : IsProbabilityMeasure (P₂.withDensity fun y => D (x, y)) := hB.isProbabilityMeasure'
  have hNx : ∀ t, Measurable[sectionFiltrationFst 𝓖 x t] fun y => N t (x, y) := fun t =>
    (hNa t).comp (comap_measurable fun y => (x, y))
  exact fib_of_isStoppedBM_withDensity_fst hD
    (isStoppedBM_of_agree_of_continuousOn hB hBc (fun y => hNc (x, y)) hNx hS hagree heq)

end Fib
/-! ### Conditioning curve on `Y` -/

section Snd

/-- **The frozen-curve rectangle input at the stop `τ`** (conditioning curve on `Y`, image curve on `X`; `𝓔` the
events of the stopped σ-algebra of `τ`). The image data are the masked canonical image `rDrv … τ`, `rLife … τ`
and the fields `VL`, `VR`, `N`; the caps `S m`; the rectangle data `𝓐 m`, `𝓑 m`, `D m` (A22's seeded density,
(1.7)). -/
structure FrozenRectInputC (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
    (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ)
    (ΘL : ℝ≥0 → Y → Fin nL → ℝ) (ΘR : ℝ≥0 → Y → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (τ : Y → ℝ≥0) (𝓔 : Set (Set Y)) where
  /-- The image force points of the left image marks. -/
  VL : Fin nL → ℝ≥0 → X × Y → ℝ
  /-- The image force points of the right image marks. -/
  VR : Fin nR → ℝ≥0 → X × Y → ℝ
  /-- The image noise. -/
  N : ℝ≥0 → X × Y → ℝ
  /-- The caps (images of the rectangle exits). -/
  S : ℕ → X × Y → ℝ≥0
  /-- The image curve's stopped record on rectangle `m`. -/
  𝓐 : ℕ → MeasurableSpace X
  /-- The conditioning curve's stopped record on rectangle `m`. -/
  𝓑 : ℕ → MeasurableSpace Y
  /-- The rectangle density (`M(S_jᵐ, τ ∧ S_kᵐ)`). -/
  D : ℕ → X × Y → ℝ≥0∞
  measurable_VL : ∀ i t, Measurable (VL i t)
  measurable_VR : ∀ j t, Measurable (VR j t)
  continuousOn_N : ∀ m z, ContinuousOn (N · z) (Icc 0 (S m z))
  N_zero : ∀ z, N 0 z = 0
  measurable_N : ∀ t, Measurable (N t)
  measurable_S : ∀ m, Measurable (S m)
  le_A : ∀ m, 𝓐 m ≤ mX
  le_B : ∀ m, 𝓑 m ≤ mY
  measurable_D : ∀ m, Measurable (D m)
  /-- (1.7). -/
  dens : ∀ m (f : X × Y → ℝ≥0∞), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
    ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D m z ∂(P₁.prod P₂)
  /-- The stopped Wald exponentials of the noise read the two stopped records. -/
  measurable_stopExp : ∀ m (a' : ℝ) (t : ℝ≥0),
    Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (stopExp a' N (S m) t)
  /-- Before the cap, the events of `𝓔` are events of the conditioning curve's stopped record. -/
  trace_stopped : ∀ m (s : ℝ≥0) (B : Set Y), B ∈ 𝓔 →
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Prod.snd ⁻¹' B ∩ {z | s < S m z})
  /-- Before the cap, the image data read the two stopped records. -/
  trace_gen : ∀ m (s : ℝ≥0), ∀ g ∈ imageGen (rDrv live xj Wj ζj xk Wk τ) (rLife live xj Wj ζj xk Wk τ) VL VR N S s,
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (g ∩ {z | s < S m z})
  /-- **The frozen-curve image law** (conditional Girsanov with the conditioning curve frozen at `y`). -/
  frozen : ∀ m, ∀ᵐ y ∂P₂, IsFrozenSampleLaw (P₁.withDensity fun x => D m (x, y)) (rDrv live xj Wj ζj xk Wk τ)
    (rLife live xj Wj ζj xk Wk τ) VL VR N S m y
  /-- The caps cover the image lifetime (countable protected-rectangle exhaustion). -/
  cover : ∀ᵐ z ∂μ, live (τ z.2) z.2 →
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < rLife live xj Wj ζj xk Wk τ z → ∃ m, t ≤ S m z
  /-- Before each cap the image is a local path of the image word with noise `N`. -/
  path : ∀ m, ∀ᵐ z ∂μ, live (τ z.2) z.2 →
    Sec2.IsSLEPathUpTo a (ΘL (τ z.2) z.2) (ΘR (τ z.2) z.2) ρL ρR (fun t => rDrv live xj Wj ζj xk Wk τ t z)
      (fun i t => VL i t z) (fun j t => VR j t z) (fun t => N t z)
      (min (S m z : ℝ≥0∞) (rLife live xj Wj ζj xk Wk τ z))

variable {a : ℝ} {nL nR : ℕ} {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓕k : Filtration ℝ≥0 mY}
  {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}
  {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The frozen-sample fibre law** from the frozen-curve image law of a `FrozenRectInputC` (by `fib_of_agree`). -/
theorem FrozenRectInputC.fibre {τ : Y → ℝ≥0} {𝓔 : Set (Set Y)}
    (I : FrozenRectInputC a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ 𝓔) (m : ℕ) :
    ∀ᵐ y ∂P₂, ∀ (a' : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y),
      MeasurableSet[imageFilt (rDrv live xj Wj ζj xk Wk τ) (rLife live xj Wj ζj xk Wk τ) I.VL I.VR I.N I.S s] A →
      ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a' I.N (I.S m) t z)) (x, y) * I.D m (x, y) ∂P₁ =
        ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a' I.N (I.S m) s z)) (x, y) * I.D m (x, y) ∂P₁ := by
  have hS𝓖 := isStoppingTime_imageFilt (W := rDrv live xj Wj ζj xk Wk τ) (ζ := rLife live xj Wj ζj xk Wk τ)
    (VL := I.VL) (VR := I.VR) (N := I.N) I.measurable_S m
  filter_upwards [I.frozen m] with y ⟨𝓗, B, hB, hBc, hC, hgen, heq⟩
  have hS : IsStoppingTime (sectionFiltration (imageFilt (rDrv live xj Wj ζj xk Wk τ)
      (rLife live xj Wj ζj xk Wk τ) I.VL I.VR I.N I.S) y) fun x => (I.S m (x, y) : WithTop ℝ≥0) :=
    fun t => ⟨_, hS𝓖 t, rfl⟩
  exact fib_of_agree_of_continuousOn (I.measurable_D m) hB hBc (I.continuousOn_N m)
    (measurable_imageFilt_N I.measurable_N) hS
    (fun s A hA => measurableSet_section_inter (hC s) (hgen s) hA) heq

/-- **A.1's rectangle core (conditioning curve on `Y`) from frozen-curve inputs**: the measurability clauses
(m1)–(m4) and, at every stopping time of the usual augmentation, a `FrozenRectInputC` give `IsRectImageCore`. -/
theorem isRectImageCoreC_of_frozen
    (hm1 : open scoped Classical in
      IsStronglyProgressive (usualAugmentation 𝓕k P₂) fun t y => {y | live t y}.indicator (fun _ => (1 : ℝ)) y)
    (hm2L : IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘL)
    (hm2R : IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘR)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hm4 : Measurable (fun p : ℝ≥0 × (X × Y) => rLife live xj Wj ζj xk Wk (fun _ => p.1) p.2))
    (hin : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
      Nonempty (FrozenRectInputC a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ
        {B | MeasurableSet[hτ.measurableSpace] B})) :
    IsRectImageCoreC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  refine ⟨hm1, hm2L, hm2R, hm3, hm4, fun τ hτ => ?_⟩
  obtain ⟨I⟩ := hin τ hτ
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hW : ∀ t, Measurable (rDrv live xj Wj ζj xk Wk τ t) := measurable_cImgDrvM_of hm3 (hτm.comp measurable_snd)
  have hζ : Measurable (rLife live xj Wj ζj xk Wk τ) := measurable_cImgLifeM_of hm4 (hτm.comp measurable_snd)
  set 𝓖 := imageFilt (rDrv live xj Wj ζj xk Wk τ) (rLife live xj Wj ζj xk Wk τ) I.VL I.VR I.N I.S with h𝓖
  have hle : 𝓖 ≤ supFiltration (hτ.measurableSpace.comap Prod.snd) (comap_snd_le (stoppedSigma_le hτ)) 𝓖 :=
    fun t => le_sup_right
  have hlt : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {z | (t : ℝ≥0∞) < rLife live xj Wj ζj xk Wk τ z} :=
    measurableSet_imageFilt_lt hζ
  refine ⟨𝓖, I.VL, I.VR, I.N, I.S, I.𝓐, I.𝓑, I.D,
    adaptedBefore_mono (adaptedBefore_of_measurable (measurable_imageFilt_W hW) hlt) hle,
    fun i => adaptedBefore_mono (adaptedBefore_of_measurable (measurable_imageFilt_VL I.measurable_VL i) hlt) hle,
    fun j => adaptedBefore_mono (adaptedBefore_of_measurable (measurable_imageFilt_VR I.measurable_VR j) hlt) hle,
    I.measurable_VL, I.measurable_VR, I.continuousOn_N, I.N_zero, measurable_imageFilt_N I.measurable_N,
    isStoppingTime_imageFilt I.measurable_S, I.le_A, I.le_B, I.measurable_D, I.dens, I.measurable_stopExp,
    fun m s B A hB hA => ?_, fun m => I.fibre m, ?_⟩
  · have hC := I.trace_stopped m s B hB
    have e : Prod.snd ⁻¹' B ∩ A ∩ {z | s < I.S m z} = A ∩ (Prod.snd ⁻¹' B ∩ {z | s < I.S m z}) := by
      ext z; simp only [mem_inter_iff]; tauto
    rw [e]
    refine measurableSet_inter_of_generateFrom hC (fun g hg => ?_) (measurableSet_generateFrom_of_imageFilt hA)
    have e' : g ∩ (Prod.snd ⁻¹' B ∩ {z | s < I.S m z}) =
        (g ∩ {z | s < I.S m z}) ∩ (Prod.snd ⁻¹' B ∩ {z | s < I.S m z}) := by
      ext z; simp only [mem_inter_iff]; tauto
    rw [e']
    exact (I.trace_gen m s g hg).inter hC
  · filter_upwards [I.cover, ae_all_iff.2 I.path] with z hcov hpath hlive
    exact ⟨hcov hlive, isSLEPathUpTo_of_caps (hcov hlive) fun m => hpath m hlive⟩

end Snd

/-! ### Conditioning curve on `X` -/

section Fst

/-- **The frozen-curve rectangle input at the stop `τ`, conditioning curve on `X`** (image curve on `Y`; `𝓔` the
events of the stopped σ-algebra of `τ`): the mirror of `FrozenRectInputC`. -/
structure FrozenRectInputFstC (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
    (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ)
    (ΘL : ℝ≥0 → X → Fin nL → ℝ) (ΘR : ℝ≥0 → X → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (τ : X → ℝ≥0) (𝓔 : Set (Set X)) where
  /-- The image force points of the left image marks. -/
  VL : Fin nL → ℝ≥0 → X × Y → ℝ
  /-- The image force points of the right image marks. -/
  VR : Fin nR → ℝ≥0 → X × Y → ℝ
  /-- The image noise. -/
  N : ℝ≥0 → X × Y → ℝ
  /-- The caps (images of the rectangle exits). -/
  S : ℕ → X × Y → ℝ≥0
  /-- The conditioning curve's stopped record on rectangle `m`. -/
  𝓐 : ℕ → MeasurableSpace X
  /-- The image curve's stopped record on rectangle `m`. -/
  𝓑 : ℕ → MeasurableSpace Y
  /-- The rectangle density (`M(τ ∧ S_kᵐ, S_jᵐ)`). -/
  D : ℕ → X × Y → ℝ≥0∞
  measurable_VL : ∀ i t, Measurable (VL i t)
  measurable_VR : ∀ j t, Measurable (VR j t)
  continuousOn_N : ∀ m z, ContinuousOn (N · z) (Icc 0 (S m z))
  N_zero : ∀ z, N 0 z = 0
  measurable_N : ∀ t, Measurable (N t)
  measurable_S : ∀ m, Measurable (S m)
  le_A : ∀ m, 𝓐 m ≤ mX
  le_B : ∀ m, 𝓑 m ≤ mY
  measurable_D : ∀ m, Measurable (D m)
  /-- (1.7). -/
  dens : ∀ m (f : X × Y → ℝ≥0∞), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
    ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D m z ∂(P₁.prod P₂)
  /-- The stopped Wald exponentials of the noise read the two stopped records. -/
  measurable_stopExp : ∀ m (a' : ℝ) (t : ℝ≥0),
    Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (stopExp a' N (S m) t)
  /-- Before the cap, the events of `𝓔` are events of the conditioning curve's stopped record. -/
  trace_stopped : ∀ m (s : ℝ≥0) (B : Set X), B ∈ 𝓔 →
    MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Prod.fst ⁻¹' B ∩ {z | s < S m z})
  /-- Before the cap, the image data read the two stopped records. -/
  trace_gen : ∀ m (s : ℝ≥0),
    ∀ g ∈ imageGen (rDrvFst live xj Wj ζj xk Wk τ) (rLifeFst live xj Wj ζj xk Wk τ) VL VR N S s,
      MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (g ∩ {z | s < S m z})
  /-- **The frozen-curve image law** (conditional Girsanov with the conditioning curve frozen at `x`). -/
  frozen : ∀ m, ∀ᵐ x ∂P₁, IsFrozenSampleLawFst (P₂.withDensity fun y => D m (x, y))
    (rDrvFst live xj Wj ζj xk Wk τ) (rLifeFst live xj Wj ζj xk Wk τ) VL VR N S m x
  /-- The caps cover the image lifetime (countable protected-rectangle exhaustion). -/
  cover : ∀ᵐ z ∂μ, live (τ z.1) z.1 →
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < rLifeFst live xj Wj ζj xk Wk τ z → ∃ m, t ≤ S m z
  /-- Before each cap the image is a local path of the image word with noise `N`. -/
  path : ∀ m, ∀ᵐ z ∂μ, live (τ z.1) z.1 →
    Sec2.IsSLEPathUpTo a (ΘL (τ z.1) z.1) (ΘR (τ z.1) z.1) ρL ρR (fun t => rDrvFst live xj Wj ζj xk Wk τ t z)
      (fun i t => VL i t z) (fun j t => VR j t z) (fun t => N t z)
      (min (S m z : ℝ≥0∞) (rLifeFst live xj Wj ζj xk Wk τ z))

variable {a : ℝ} {nL nR : ℕ} {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓕k : Filtration ℝ≥0 mX}
  {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}
  {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The frozen-sample fibre law** from the frozen-curve image law of a `FrozenRectInputFstC`
(by `fib_of_agree_fst`). -/
theorem FrozenRectInputFstC.fibre {τ : X → ℝ≥0} {𝓔 : Set (Set X)}
    (I : FrozenRectInputFstC a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ 𝓔) (m : ℕ) :
    ∀ᵐ x ∂P₁, ∀ (a' : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y),
      MeasurableSet[imageFilt (rDrvFst live xj Wj ζj xk Wk τ) (rLifeFst live xj Wj ζj xk Wk τ) I.VL I.VR I.N I.S s]
        A →
      ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a' I.N (I.S m) t z)) (x, y) * I.D m (x, y) ∂P₂ =
        ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a' I.N (I.S m) s z)) (x, y) * I.D m (x, y) ∂P₂ := by
  have hS𝓖 := isStoppingTime_imageFilt (W := rDrvFst live xj Wj ζj xk Wk τ)
    (ζ := rLifeFst live xj Wj ζj xk Wk τ) (VL := I.VL) (VR := I.VR) (N := I.N) I.measurable_S m
  filter_upwards [I.frozen m] with x ⟨𝓗, B, hB, hBc, hC, hgen, heq⟩
  have hS : IsStoppingTime (sectionFiltrationFst (imageFilt (rDrvFst live xj Wj ζj xk Wk τ)
      (rLifeFst live xj Wj ζj xk Wk τ) I.VL I.VR I.N I.S) x) fun y => (I.S m (x, y) : WithTop ℝ≥0) :=
    fun t => ⟨_, hS𝓖 t, rfl⟩
  exact fib_of_agree_fst_of_continuousOn (I.measurable_D m) hB hBc (I.continuousOn_N m)
    (measurable_imageFilt_N I.measurable_N) hS
    (fun s A hA => measurableSet_sectionFst_inter (hC s) (hgen s) hA) heq

/-- **A.1's rectangle core (conditioning curve on `X`) from frozen-curve inputs**: the measurability clauses
(m1)–(m4) and, at every stopping time of the usual augmentation, a `FrozenRectInputFstC` give
`IsRectImageCoreFst`. -/
theorem isRectImageCoreFstC_of_frozen
    (hm1 : open scoped Classical in
      IsStronglyProgressive (usualAugmentation 𝓕k P₁) fun t x => {x | live t x}.indicator (fun _ => (1 : ℝ)) x)
    (hm2L : IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘL)
    (hm2R : IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘR)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hm4 : Measurable (fun p : ℝ≥0 × (X × Y) => rLifeFst live xj Wj ζj xk Wk (fun _ => p.1) p.2))
    (hin : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (FrozenRectInputFstC a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ
        {B | MeasurableSet[hτ.measurableSpace] B})) :
    IsRectImageCoreFstC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  refine ⟨hm1, hm2L, hm2R, hm3, hm4, fun τ hτ => ?_⟩
  obtain ⟨I⟩ := hin τ hτ
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hW : ∀ t, Measurable (rDrvFst live xj Wj ζj xk Wk τ t) :=
    measurable_cImgDrvM_of hm3 (hτm.comp measurable_fst)
  have hζ : Measurable (rLifeFst live xj Wj ζj xk Wk τ) := measurable_cImgLifeM_of hm4 (hτm.comp measurable_fst)
  set 𝓖 := imageFilt (rDrvFst live xj Wj ζj xk Wk τ) (rLifeFst live xj Wj ζj xk Wk τ) I.VL I.VR I.N I.S with h𝓖
  have hle : 𝓖 ≤ supFiltration (hτ.measurableSpace.comap Prod.fst) (comap_fst_le (stoppedSigma_le hτ)) 𝓖 :=
    fun t => le_sup_right
  have hlt : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {z | (t : ℝ≥0∞) < rLifeFst live xj Wj ζj xk Wk τ z} :=
    measurableSet_imageFilt_lt hζ
  refine ⟨𝓖, I.VL, I.VR, I.N, I.S, I.𝓐, I.𝓑, I.D,
    adaptedBefore_mono (adaptedBefore_of_measurable (measurable_imageFilt_W hW) hlt) hle,
    fun i => adaptedBefore_mono (adaptedBefore_of_measurable (measurable_imageFilt_VL I.measurable_VL i) hlt) hle,
    fun j => adaptedBefore_mono (adaptedBefore_of_measurable (measurable_imageFilt_VR I.measurable_VR j) hlt) hle,
    I.measurable_VL, I.measurable_VR, I.continuousOn_N, I.N_zero, measurable_imageFilt_N I.measurable_N,
    isStoppingTime_imageFilt I.measurable_S, I.le_A, I.le_B, I.measurable_D, I.dens, I.measurable_stopExp,
    fun m s B A hB hA => ?_, fun m => I.fibre m, ?_⟩
  · have hC := I.trace_stopped m s B hB
    have e : Prod.fst ⁻¹' B ∩ A ∩ {z | s < I.S m z} = A ∩ (Prod.fst ⁻¹' B ∩ {z | s < I.S m z}) := by
      ext z; simp only [mem_inter_iff]; tauto
    rw [e]
    refine measurableSet_inter_of_generateFrom hC (fun g hg => ?_) (measurableSet_generateFrom_of_imageFilt hA)
    have e' : g ∩ (Prod.fst ⁻¹' B ∩ {z | s < I.S m z}) =
        (g ∩ {z | s < I.S m z}) ∩ (Prod.fst ⁻¹' B ∩ {z | s < I.S m z}) := by
      ext z; simp only [mem_inter_iff]; tauto
    rw [e']
    exact (I.trace_gen m s g hg).inter hC
  · filter_upwards [I.cover, ae_all_iff.2 I.path] with z hcov hpath hlive
    exact ⟨hcov hlive, isSLEPathUpTo_of_caps (hcov hlive) fun m => hpath m hlive⟩

end Fst

/-! ### Families over the deterministic frozen time, conditioning curve on `Y` -/

section FamSnd

variable {nL nR : ℕ}

/-- **The frozen-curve image law at every deterministic frozen time** (conditioning curve on `Y`, image curve on
`X`): the image force points, image noise, caps and rectangle densities of the canonical image at the deterministic
stop `σ`, jointly measurable in `(σ, z)`, such that for almost every frozen conditioning sample `y` and **every**
frozen time `σ` the frozen-sample law holds under `D_σ,m(·, y) · P₁`. -/
structure FrozenFamilyC (P₁ : Measure X) (P₂ : Measure Y) (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ)
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
  continuousOn_N : ∀ σ m z, ContinuousOn (N σ · z) (Icc 0 (S σ m z))
  N_zero : ∀ σ z, N σ 0 z = 0
  measurable_N : ∀ t, Measurable fun p : ℝ≥0 × (X × Y) => N p.1 t p.2
  measurable_S : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => S p.1 m p.2
  measurable_D : ∀ m, Measurable fun p : ℝ≥0 × (X × Y) => D p.1 m p.2
  /-- **The frozen-curve image law at every deterministic frozen time.** -/
  frozen : ∀ m, ∀ᵐ y ∂P₂, ∀ σ : ℝ≥0, IsFrozenSampleLaw (P₁.withDensity fun x => D σ m (x, y))
    (rDrv live xj Wj ζj xk Wk fun _ => σ) (rLife live xj Wj ζj xk Wk fun _ => σ) (VL σ) (VR σ) (N σ) (S σ) m y

variable {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ}
  {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}

namespace FrozenFamilyC

variable (F : FrozenFamilyC P₁ P₂ live xj Wj ζj xk Wk nL nR) (τ : Y → ℝ≥0)

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

end FrozenFamilyC

/-- **The per-stop rectangle data for a frozen family** at the stop `τ` (A22's (1.7) with the stopped records, the
stopped-record conditions of the substituted image data, the cover and the per-cap paths). -/
structure FamilyRectC (F : FrozenFamilyC P₁ P₂ live xj Wj ζj xk Wk nL nR) (a : ℝ) (ΘL : ℝ≥0 → Y → Fin nL → ℝ)
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
def FrozenFamilyC.toInput (F : FrozenFamilyC P₁ P₂ live xj Wj ζj xk Wk nL nR) {a : ℝ}
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {μ : Measure (X × Y)} {τ : Y → ℝ≥0} {𝓔 : Set (Set Y)} (hτ : Measurable τ)
    (R : FamilyRectC F a ΘL ΘR ρL ρR μ τ 𝓔) :
    FrozenRectInputC a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ 𝓔 where
  VL := F.VLat τ
  VR := F.VRat τ
  N := F.Nat τ
  S := F.Sat τ
  𝓐 := R.𝓐
  𝓑 := R.𝓑
  D := F.Dat τ
  measurable_VL := F.measurable_VLat hτ
  measurable_VR := F.measurable_VRat hτ
  continuousOn_N m z := F.continuousOn_N (τ z.2) m z
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
(m1)–(m4), a `FrozenFamilyC`, and at every stopping time of the usual augmentation the per-stop rectangle data give
`IsRectImageCore`. -/
theorem isRectImageCoreC_of_family {a : ℝ} {𝓕k : Filtration ℝ≥0 mY} {μ : Measure (X × Y)}
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hm1 : open scoped Classical in
      IsStronglyProgressive (usualAugmentation 𝓕k P₂) fun t y => {y | live t y}.indicator (fun _ => (1 : ℝ)) y)
    (hm2L : IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘL)
    (hm2R : IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘR)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hm4 : Measurable (fun p : ℝ≥0 × (X × Y) => rLife live xj Wj ζj xk Wk (fun _ => p.1) p.2))
    (F : FrozenFamilyC P₁ P₂ live xj Wj ζj xk Wk nL nR)
    (hR : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
      Nonempty (FamilyRectC F a ΘL ΘR ρL ρR μ τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    IsRectImageCoreC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR :=
  isRectImageCoreC_of_frozen hm1 hm2L hm2R hm3 hm4 fun τ hτ =>
    (hR τ hτ).map (F.toInput (measurable_of_isStoppingTime hτ))

end FamSnd

/-! ### Families over the deterministic frozen time, conditioning curve on `X` -/

section FamFst

variable {nL nR : ℕ}

/-- **The frozen-curve image law at every deterministic frozen time, conditioning curve on `X`** (image curve on
`Y`): the mirror of `FrozenFamilyC`. -/
structure FrozenFamilyFstC (P₁ : Measure X) (P₂ : Measure Y) (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ)
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
  continuousOn_N : ∀ σ m z, ContinuousOn (N σ · z) (Icc 0 (S σ m z))
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

namespace FrozenFamilyFstC

variable (F : FrozenFamilyFstC P₁ P₂ live xj Wj ζj xk Wk nL nR) (τ : X → ℝ≥0)

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

/-- **The frozen-sample law at an arbitrary stop `τ`** (mirror of `FrozenFamilyC.frozen_at`). -/
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

end FrozenFamilyFstC

/-- **The per-stop rectangle data for a frozen family, conditioning curve on `X`** (mirror of `FamilyRectC`). -/
structure FamilyRectFstC (F : FrozenFamilyFstC P₁ P₂ live xj Wj ζj xk Wk nL nR) (a : ℝ)
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
def FrozenFamilyFstC.toInput (F : FrozenFamilyFstC P₁ P₂ live xj Wj ζj xk Wk nL nR) {a : ℝ}
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {μ : Measure (X × Y)} {τ : X → ℝ≥0} {𝓔 : Set (Set X)} (hτ : Measurable τ)
    (R : FamilyRectFstC F a ΘL ΘR ρL ρR μ τ 𝓔) :
    FrozenRectInputFstC a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ 𝓔 where
  VL := F.VLat τ
  VR := F.VRat τ
  N := F.Nat τ
  S := F.Sat τ
  𝓐 := R.𝓐
  𝓑 := R.𝓑
  D := F.Dat τ
  measurable_VL := F.measurable_VLat hτ
  measurable_VR := F.measurable_VRat hτ
  continuousOn_N m z := F.continuousOn_N (τ z.1) m z
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
theorem isRectImageCoreFstC_of_family {a : ℝ} {𝓕k : Filtration ℝ≥0 mX} {μ : Measure (X × Y)}
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hm1 : open scoped Classical in
      IsStronglyProgressive (usualAugmentation 𝓕k P₁) fun t x => {x | live t x}.indicator (fun _ => (1 : ℝ)) x)
    (hm2L : IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘL)
    (hm2R : IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘR)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hm4 : Measurable (fun p : ℝ≥0 × (X × Y) => rLifeFst live xj Wj ζj xk Wk (fun _ => p.1) p.2))
    (F : FrozenFamilyFstC P₁ P₂ live xj Wj ζj xk Wk nL nR)
    (hR : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (FamilyRectFstC F a ΘL ΘR ρL ρR μ τ {B | MeasurableSet[hτ.measurableSpace] B})) :
    IsRectImageCoreFstC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR :=
  isRectImageCoreFstC_of_frozen hm1 hm2L hm2R hm3 hm4 fun τ hτ =>
    (hR τ hτ).map (F.toInput (measurable_of_isStoppingTime hτ))

end FamFst

/-! ### The old inputs give the new ones -/

section ToC

variable {nL nR : ℕ}

/-- **A frozen family with a globally continuous noise is a C family.** -/
def FrozenFamily.toC {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ}
    {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ} (F : FrozenFamily P₁ P₂ live xj Wj ζj xk Wk nL nR) :
    FrozenFamilyC P₁ P₂ live xj Wj ζj xk Wk nL nR where
  VL := F.VL
  VR := F.VR
  N := F.N
  S := F.S
  D := F.D
  measurable_VL := F.measurable_VL
  measurable_VR := F.measurable_VR
  continuousOn_N σ _ z := (F.continuous_N σ z).continuousOn
  N_zero := F.N_zero
  measurable_N := F.measurable_N
  measurable_S := F.measurable_S
  measurable_D := F.measurable_D
  frozen := F.frozen

/-- **The per-stop data of an old frozen family are per-stop data of its C family.** -/
def FamilyRect.toC {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ}
    {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ} {F : FrozenFamily P₁ P₂ live xj Wj ζj xk Wk nL nR} {a : ℝ}
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {μ : Measure (X × Y)} {τ : Y → ℝ≥0} {𝓔 : Set (Set Y)} (R : FamilyRect F a ΘL ΘR ρL ρR μ τ 𝓔) :
    FamilyRectC (FrozenFamily.toC F) a ΘL ΘR ρL ρR μ τ 𝓔 where
  𝓐 := R.𝓐
  𝓑 := R.𝓑
  le_A := R.le_A
  le_B := R.le_B
  dens := R.dens
  measurable_stopExp := R.measurable_stopExp
  trace_stopped := R.trace_stopped
  trace_gen := R.trace_gen
  cover := R.cover
  path := R.path

/-- **A frozen family (conditioning curve on `X`) with a globally continuous noise is a C family.** -/
def FrozenFamilyFst.toC {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ}
    {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} (F : FrozenFamilyFst P₁ P₂ live xj Wj ζj xk Wk nL nR) :
    FrozenFamilyFstC P₁ P₂ live xj Wj ζj xk Wk nL nR where
  VL := F.VL
  VR := F.VR
  N := F.N
  S := F.S
  D := F.D
  measurable_VL := F.measurable_VL
  measurable_VR := F.measurable_VR
  continuousOn_N σ _ z := (F.continuous_N σ z).continuousOn
  N_zero := F.N_zero
  measurable_N := F.measurable_N
  measurable_S := F.measurable_S
  measurable_D := F.measurable_D
  frozen := F.frozen

/-- **The per-stop data of an old frozen family (conditioning curve on `X`) are per-stop data of its C family.** -/
def FamilyRectFst.toC {P₁ : Measure X} {P₂ : Measure Y} {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ}
    {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {F : FrozenFamilyFst P₁ P₂ live xj Wj ζj xk Wk nL nR} {a : ℝ}
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {μ : Measure (X × Y)} {τ : X → ℝ≥0} {𝓔 : Set (Set X)} (R : FamilyRectFst F a ΘL ΘR ρL ρR μ τ 𝓔) :
    FamilyRectFstC (FrozenFamilyFst.toC F) a ΘL ΘR ρL ρR μ τ 𝓔 where
  𝓐 := R.𝓐
  𝓑 := R.𝓑
  le_A := R.le_A
  le_B := R.le_B
  dens := R.dens
  measurable_stopExp := R.measurable_stopExp
  trace_stopped := R.trace_stopped
  trace_gen := R.trace_gen
  cover := R.cover
  path := R.path

end ToC

end InteractingSLE.ZhanGT4.A1RLaw
