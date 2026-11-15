/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1FrozenGen
import InteractingSLE.Spec.ZhanGT4.A1CoreInputs

/-!
# A.1's frozen-curve image law, II: the rectangle cores from frozen conditioning samples

Packet PROVE-A1-FROZEN (R76). Source: Astra, *Follow-up 5* §1.3 (`source/external/AstraIG1/ig1_followup5.txt`
L203–L222, R73): "If `τ` is bounded by the large-curve protection time, optional sampling gives the density
`M(s, τ)`. For bounded stopped-record tests, its identity is (1.7) … Conditional Girsanov gives the image SDE.
Countable protected-rectangle exhaustion gives the law up to first contact." *Follow-up proofs* §A.1.3
(`ig1_followup_proofs.txt` L341–L353, R38): "By (D8) and Girsanov, **with the other curve stopped**, the new drift of
`W_j` is …".

The frozen-curve clauses of `A1Core.IsRectImageCore` are per frozen conditioning sample: for `P₂`-almost every `y`
the conditioning curve is a fixed deterministic path, `τ(y)` a fixed number, and the image law is a one-curve
statement about the image curve under its marginal law tilted by `D_m(·, y)` (= `M(S_jᵐ, τ(y) ∧ S_kᵐ(y))`).
Stopping times enter only through measurability, which (1.7) carries. This file assembles the rectangle cores from:

* **`IsFrozenSampleLaw`**, **`IsFrozenSampleLawFst`**: the frozen-curve image law at one frozen conditioning
  sample and one cap — the one-curve statement the seeded frozen-hull line must supply;
* **`FrozenRectInput … τ 𝓔`** (conditioning curve on `Y`): at the stop `τ` with stopped σ-algebra `𝓔`, the image
  force points `VL`, `VR`, the image noise `N` (continuous, from `0`), the caps `S m`, the rectangle data
  `𝓐 m`, `𝓑 m`, `D m` with (1.7), the stopped-record (trace) conditions of the image data before each cap, and
  * `frozen`: for each cap and `P₂`-almost every frozen sample `y`, under `D_m(·, y) · P₁`, a Brownian motion of a
    filtration of the image curve in which the sections at `y` of the image data are adapted before the cap agrees
    with the image noise up to the cap (conditional Girsanov at the frozen hull, (D10), time change and Lévy);
  * `cover`, `path`: almost surely the caps cover the image lifetime, and before each cap (capped by the lifetime)
    the image is a local `SLE_a(ρ)` path of the image word with noise `N`;
* **`isRectImageCore_of_frozen`**: the measurability clauses (m1)–(m4) and an input at every stopping time of the
  usual augmentation give `IsRectImageCore`: the filtration is the image-data filtration `imageFilt` (so adaptedness
  and the caps' stopping-time property are by construction), the stopped-record clauses come from the generators
  (`measurableSet_inter_of_generateFrom`), the fibre law from `A1Core.fib_of_agree` with the frozen-sample filtration
  clauses reduced to the generators (`measurableSet_section_inter`), and the path clause from the countable cap
  exhaustion (`isSLEPathUpTo_of_caps`);
* **`FrozenRectInputFst`**, **`isRectImageCoreFst_of_frozen`**: the mirror (conditioning curve on `X`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Frozen

open A1Canon A1Ref A1Core

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-! ### The frozen-sample law -/

section Sample

variable {nL nR : ℕ}

/-- **The frozen-curve image law at a frozen conditioning sample `y`, for the cap `S m`** (conditional Girsanov
with the conditioning curve frozen at `y`, A.1.3): under the image curve's law `Q` (the marginal tilted by the
rectangle density at `y`), a continuous Brownian motion `B` of a filtration `𝓗` of the image curve agrees with the
image noise up to the cap, and in `𝓗` the cap event `{s < S m}` and, before the cap, the sections at `y` of the
image data (the generators `imageGen` of the image-data filtration) are measurable at `s`. -/
def IsFrozenSampleLaw (Q : Measure X) (W : ℝ≥0 → X × Y → ℝ) (ζ : X × Y → ℝ≥0∞) (VL : Fin nL → ℝ≥0 → X × Y → ℝ)
    (VR : Fin nR → ℝ≥0 → X × Y → ℝ) (N : ℝ≥0 → X × Y → ℝ) (S : ℕ → X × Y → ℝ≥0) (m : ℕ) (y : Y) : Prop :=
  ∃ (𝓗 : Filtration ℝ≥0 mX) (B : ℝ≥0 → X → ℝ),
    IsFilteredBrownianReal 𝓗 B Q ∧ (∀ x, Continuous (B · x)) ∧
    (∀ s : ℝ≥0, MeasurableSet[𝓗 s] {x | s < S m (x, y)}) ∧
    (∀ s : ℝ≥0, ∀ g ∈ imageGen W ζ VL VR N S s,
      MeasurableSet[𝓗 s] ((fun x => (x, y)) ⁻¹' g ∩ {x | s < S m (x, y)})) ∧
    ∀ᵐ x ∂Q, ∀ t, t ≤ S m (x, y) → B t x = N t (x, y)

/-- **The frozen-curve image law at a frozen conditioning sample `x`** (the mirror: image curve on `Y`). -/
def IsFrozenSampleLawFst (Q : Measure Y) (W : ℝ≥0 → X × Y → ℝ) (ζ : X × Y → ℝ≥0∞)
    (VL : Fin nL → ℝ≥0 → X × Y → ℝ) (VR : Fin nR → ℝ≥0 → X × Y → ℝ) (N : ℝ≥0 → X × Y → ℝ)
    (S : ℕ → X × Y → ℝ≥0) (m : ℕ) (x : X) : Prop :=
  ∃ (𝓗 : Filtration ℝ≥0 mY) (B : ℝ≥0 → Y → ℝ),
    IsFilteredBrownianReal 𝓗 B Q ∧ (∀ y, Continuous (B · y)) ∧
    (∀ s : ℝ≥0, MeasurableSet[𝓗 s] {y | s < S m (x, y)}) ∧
    (∀ s : ℝ≥0, ∀ g ∈ imageGen W ζ VL VR N S s,
      MeasurableSet[𝓗 s] ((fun y => (x, y)) ⁻¹' g ∩ {y | s < S m (x, y)})) ∧
    ∀ᵐ y ∂Q, ∀ t, t ≤ S m (x, y) → B t y = N t (x, y)

end Sample

/-! ### Conditioning curve on `Y` -/

section Snd

/-- **The frozen-curve rectangle input at the stop `τ`** (conditioning curve on `Y`, image curve on `X`; `𝓔` the
events of the stopped σ-algebra of `τ`). The image data are the masked canonical image `rDrv … τ`, `rLife … τ`
and the fields `VL`, `VR`, `N`; the caps `S m`; the rectangle data `𝓐 m`, `𝓑 m`, `D m` (A22's seeded density,
(1.7)). -/
structure FrozenRectInput (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
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
  continuous_N : ∀ z, Continuous (N · z)
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

/-- **The frozen-sample fibre law** from the frozen-curve image law of a `FrozenRectInput` (by `fib_of_agree`). -/
theorem FrozenRectInput.fibre {τ : Y → ℝ≥0} {𝓔 : Set (Set Y)}
    (I : FrozenRectInput a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ 𝓔) (m : ℕ) :
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
  exact fib_of_agree (I.measurable_D m) hB hBc I.continuous_N (measurable_imageFilt_N I.measurable_N) hS
    (fun s A hA => measurableSet_section_inter (hC s) (hgen s) hA) heq

/-- **A.1's rectangle core (conditioning curve on `Y`) from frozen-curve inputs**: the measurability clauses
(m1)–(m4) and, at every stopping time of the usual augmentation, a `FrozenRectInput` give `IsRectImageCore`. -/
theorem isRectImageCore_of_frozen
    (hm1 : open scoped Classical in
      IsStronglyProgressive (usualAugmentation 𝓕k P₂) fun t y => {y | live t y}.indicator (fun _ => (1 : ℝ)) y)
    (hm2L : IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘL)
    (hm2R : IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘR)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hm4 : Measurable (fun p : ℝ≥0 × (X × Y) => rLife live xj Wj ζj xk Wk (fun _ => p.1) p.2))
    (hin : ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
      Nonempty (FrozenRectInput a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ
        {B | MeasurableSet[hτ.measurableSpace] B})) :
    IsRectImageCore a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
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
    I.measurable_VL, I.measurable_VR, I.continuous_N, I.N_zero, measurable_imageFilt_N I.measurable_N,
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
events of the stopped σ-algebra of `τ`): the mirror of `FrozenRectInput`. -/
structure FrozenRectInputFst (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
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
  continuous_N : ∀ z, Continuous (N · z)
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

/-- **The frozen-sample fibre law** from the frozen-curve image law of a `FrozenRectInputFst`
(by `fib_of_agree_fst`). -/
theorem FrozenRectInputFst.fibre {τ : X → ℝ≥0} {𝓔 : Set (Set X)}
    (I : FrozenRectInputFst a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ 𝓔) (m : ℕ) :
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
  exact fib_of_agree_fst (I.measurable_D m) hB hBc I.continuous_N (measurable_imageFilt_N I.measurable_N) hS
    (fun s A hA => measurableSet_sectionFst_inter (hC s) (hgen s) hA) heq

/-- **A.1's rectangle core (conditioning curve on `X`) from frozen-curve inputs**: the measurability clauses
(m1)–(m4) and, at every stopping time of the usual augmentation, a `FrozenRectInputFst` give
`IsRectImageCoreFst`. -/
theorem isRectImageCoreFst_of_frozen
    (hm1 : open scoped Classical in
      IsStronglyProgressive (usualAugmentation 𝓕k P₁) fun t x => {x | live t x}.indicator (fun _ => (1 : ℝ)) x)
    (hm2L : IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘL)
    (hm2R : IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘR)
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2)
    (hm4 : Measurable (fun p : ℝ≥0 × (X × Y) => rLifeFst live xj Wj ζj xk Wk (fun _ => p.1) p.2))
    (hin : ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
      Nonempty (FrozenRectInputFst a P₁ P₂ μ live xj Wj ζj xk Wk ΘL ΘR ρL ρR τ
        {B | MeasurableSet[hτ.measurableSpace] B})) :
    IsRectImageCoreFst a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
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
    I.measurable_VL, I.measurable_VR, I.continuous_N, I.N_zero, measurable_imageFilt_N I.measurable_N,
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

end InteractingSLE.ZhanGT4.A1Frozen
