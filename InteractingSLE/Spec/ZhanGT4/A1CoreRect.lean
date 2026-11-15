/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CoreFibre
import InteractingSLE.Spec.ZhanGT4.A1CoreFactor
import InteractingSLE.Spec.ZhanGT4.A1CanonCore

/-!
# A.1's rectangle core in density form: the conditional image law from (1.7) and frozen-hull fibres

Packet PROVE-A1CORE. Source: Astra, *Follow-up 5* §1.3 (`source/external/AstraIG1/ig1_followup5.txt` L203–L222,
R73): "On each protected rectangle, that construction supplies a continuous joint density `M(s, t)` … These are true
martingales in the usual marginal filtrations. If `τ` is bounded by the large-curve protection time, optional
sampling gives the density `M(s, τ)`. For bounded stopped-record tests, its identity is (1.7) … Conditional Girsanov
gives the image SDE. Countable protected-rectangle exhaustion gives the law up to first contact. The unchanged
marginal laws preserve their completed null sets."

A1CANON's `A1Canon.IsCanonImageCore` asks, at every stopping time of the usual augmentation of the conditioning
curve's filtration **on the coupling space**, for an image noise that is a Brownian motion stopped at each rectangle
cap **under the coupling**. Here the coupling lives on the product `X × Y` of the two curves' path spaces with
marginals `P₁`, `P₂`, and the source's form is:

* **`IsRectImageCore`** (conditioning curve on `Y`) / **`IsRectImageCoreFst`** (conditioning curve on `X`): the
  measurability clauses of `IsCanonImageCore` unchanged; and at every stopping time `τ` of the usual augmentation of
  the conditioning curve's **own** filtration under its **marginal** law: for each rectangle `m` a density `D m`
  (`M(S_jᵐ, τ ∧ S_kᵐ)`) with the identity (1.7) `∫ f dμ = ∫ f D_m d(P₁ ⊗ P₂)` on the σ-algebra of the two stopped
  records, and, for almost every frozen conditioning sample, the **frozen-hull fibre law**: under the image curve's law
  tilted by `D_m`, the image noise stopped at the cap has the martingale property (conditional Girsanov at a frozen
  hull); plus the adaptedness and local path conditions of the canonical image at `τ`;
* **`isCanonImageCore_of_rect`**, **`isCanonImageCore_of_rect_fst`**: these imply `IsCanonImageCore` for the usual
  augmentation of the pulled-back filtration under the coupling (factorization of the coupling's stopping times through
  the marginal, `exists_factor_stoppingTime_map`; conditional Girsanov assembled, `isStoppedBM_of_density`; the null
  augmentation).

Tools for the inputs: `lintegral_eq_of_rect` and `rect_of_optional` give (1.7) from the exit-time rectangle law and
optional sampling; `fib_of_isStoppedBM_withDensity` gives the fibre law from a stopped Brownian motion under the
tilted law (the output form of the frozen-hull Girsanov theorems `DualHyp.exists_condLaw₁`, A12).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Core

open A1Canon A1Ref

/-- The stopped σ-algebra of a stopping time is a sub-σ-algebra. -/
theorem stoppedSigma_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓕 τ) : hτ.measurableSpace ≤ mΩ :=
  hτ.measurableSpace_le

section Rect

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- The masked canonical image lifetime on `X × Y`: image curve on `X` (start `xj`, driver `Wj`, lifetime `ζj`),
conditioning curve on `Y` (start `xk`, driver `Wk`, live event `live`), at the stop `τ` of the conditioning curve. -/
abbrev rLife (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ)
    (τ : Y → ℝ≥0) : X × Y → ℝ≥0∞ :=
  cImgLifeM (fun t z => live t z.2) xj (fun t z => Wj t z.1) (fun z => ζj z.1) xk (fun t z => Wk t z.2)
    fun z => τ z.2

/-- The masked canonical image driver on `X × Y` (image curve on `X`, conditioning curve on `Y`). -/
abbrev rDrv (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → Y → ℝ)
    (τ : Y → ℝ≥0) : ℝ≥0 → X × Y → ℝ :=
  cImgDrvM (fun t z => live t z.2) xj (fun t z => Wj t z.1) (fun z => ζj z.1) xk (fun t z => Wk t z.2)
    fun z => τ z.2

/-- The masked canonical image lifetime on `X × Y` with the roles exchanged (image curve on `Y`, conditioning curve
on `X`). -/
abbrev rLifeFst (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ)
    (τ : X → ℝ≥0) : X × Y → ℝ≥0∞ :=
  cImgLifeM (fun t z => live t z.1) xj (fun t z => Wj t z.2) (fun z => ζj z.2) xk (fun t z => Wk t z.1)
    fun z => τ z.1

/-- The masked canonical image driver on `X × Y` with the roles exchanged. -/
abbrev rDrvFst (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ)
    (τ : X → ℝ≥0) : ℝ≥0 → X × Y → ℝ :=
  cImgDrvM (fun t z => live t z.1) xj (fun t z => Wj t z.2) (fun z => ζj z.2) xk (fun t z => Wk t z.1)
    fun z => τ z.1

/-- **A.1's rectangle core in density form, conditioning curve on `Y`** (follow-up 5 §1.3). The image curve lives on
`X` (law `P₁`), the conditioning curve on `Y` (law `P₂`, filtration `𝓕k`), `μ` is a coupling. Clauses:

* (m1)–(m2) for the conditioning curve alone: its live event and image words are progressively measurable for the
  usual augmentation of `𝓕k` under `P₂`; (m3)–(m4): the masked canonical image is measurable jointly in the
  (deterministic) stop and the sample;
* at every stopping time `τ` of the usual augmentation of `𝓕k` under `P₂`, with `𝓔 = 𝓕ᵏ_τ`: a filtration `𝓖` of
  `X × Y` (the image data), image force points `VL'`, `VR'`, a continuous `𝓖`-adapted image noise `N` from `0`, caps
  `S m` (`𝓖`-stopping times), and per rectangle `m` sub-σ-algebras `𝓐 m` (image curve's stopped record), `𝓑 m`
  (conditioning curve's stopped record at `τ`) and a density `D m` (`M(S_jᵐ, τ ∧ S_kᵐ)`) with
  * (1.7): `∫ f dμ = ∫ f D_m d(P₁ ⊗ P₂)` for `𝓐 m ⊗ 𝓑 m`-measurable `f ≥ 0` (`dens_of_rect_optional`);
  * the stopped Wald exponentials of `N` at `S m` and the sets `snd⁻¹ B ∩ A ∩ {s < S m}` (`B ∈ 𝓔`, `A ∈ 𝓖_s`) are
    `𝓐 m ⊗ 𝓑 m`-measurable (before the cap the noise reads the two stopped records only);
  * the frozen-hull fibre law: for `P₂`-almost every `y`, under `D_m(·, y) · P₁` the stopped Wald exponentials have
    the martingale property for the sections of `𝓖` (`fib_of_agree`, `fib_of_isStoppedBM_withDensity`);
* the canonical image at `τ ∘ snd` and the force points are adapted before the image lifetime to `snd⁻¹ 𝓔 ∨ 𝓖`, the
  force points are measurable, and almost surely on the live event the caps cover the image lifetime and the image is
  a local `SLE_a(ρ)` path of the image word with noise `N`. -/
def IsRectImageCore (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
    (𝓕k : Filtration ℝ≥0 mY) (live : ℝ≥0 → Y → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → Y → ℝ) (ΘL : ℝ≥0 → Y → Fin nL → ℝ) (ΘR : ℝ≥0 → Y → Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  (open scoped Classical in
    IsStronglyProgressive (usualAugmentation 𝓕k P₂) fun t y => {y | live t y}.indicator (fun _ => (1 : ℝ)) y) ∧
  IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘL ∧ IsStronglyProgressive (usualAugmentation 𝓕k P₂) ΘR ∧
  (∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrv live xj Wj ζj xk Wk (fun _ => p.1) t p.2) ∧
  Measurable (fun p : ℝ≥0 × (X × Y) => rLife live xj Wj ζj xk Wk (fun _ => p.1) p.2) ∧
  ∀ (τ : Y → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₂) fun y => (τ y : WithTop ℝ≥0)),
    ∃ (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))) (VL' : Fin nL → ℝ≥0 → X × Y → ℝ)
      (VR' : Fin nR → ℝ≥0 → X × Y → ℝ) (N : ℝ≥0 → X × Y → ℝ) (S : ℕ → X × Y → ℝ≥0)
      (𝓐 : ℕ → MeasurableSpace X) (𝓑 : ℕ → MeasurableSpace Y) (D : ℕ → X × Y → ℝ≥0∞),
      AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.snd) (comap_snd_le (stoppedSigma_le hτ)) 𝓖)
        (rLife live xj Wj ζj xk Wk τ) (rDrv live xj Wj ζj xk Wk τ) ∧
      (∀ i, AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.snd)
        (comap_snd_le (stoppedSigma_le hτ)) 𝓖) (rLife live xj Wj ζj xk Wk τ) (VL' i)) ∧
      (∀ i, AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.snd)
        (comap_snd_le (stoppedSigma_le hτ)) 𝓖) (rLife live xj Wj ζj xk Wk τ) (VR' i)) ∧
      (∀ i t, Measurable (VL' i t)) ∧ (∀ i t, Measurable (VR' i t)) ∧
      (∀ z, Continuous (N · z)) ∧ (∀ z, N 0 z = 0) ∧ (∀ t, Measurable[𝓖 t] (N t)) ∧
      (∀ m, IsStoppingTime 𝓖 fun z => (S m z : WithTop ℝ≥0)) ∧
      (∀ m, 𝓐 m ≤ mX) ∧ (∀ m, 𝓑 m ≤ mY) ∧ (∀ m, Measurable (D m)) ∧
      (∀ m (f : X × Y → ℝ≥0∞), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
        ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D m z ∂(P₁.prod P₂)) ∧
      (∀ m (a' : ℝ) (t : ℝ≥0), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (stopExp a' N (S m) t)) ∧
      (∀ m (s : ℝ≥0) (B : Set Y) (A : Set (X × Y)), MeasurableSet[hτ.measurableSpace] B →
        MeasurableSet[𝓖 s] A →
        MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S m z})) ∧
      (∀ m, ∀ᵐ y ∂P₂, ∀ (a' : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
        ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a' N (S m) t z)) (x, y) * D m (x, y) ∂P₁ =
          ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a' N (S m) s z)) (x, y) * D m (x, y) ∂P₁) ∧
      ∀ᵐ z ∂μ, live (τ z.2) z.2 →
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < rLife live xj Wj ζj xk Wk τ z → ∃ m, t ≤ S m z) ∧
        Sec2.IsSLEPathUpTo a (ΘL (τ z.2) z.2) (ΘR (τ z.2) z.2) ρL ρR (fun t => rDrv live xj Wj ζj xk Wk τ t z)
          (fun i t => VL' i t z) (fun i t => VR' i t z) (fun t => N t z) (rLife live xj Wj ζj xk Wk τ z)

/-- **A.1's rectangle core in density form, conditioning curve on `X`**: the mirror of `IsRectImageCore` (the image
curve on `Y`, fibres over frozen conditioning samples `x ∈ X`). -/
def IsRectImageCoreFst (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
    (𝓕k : Filtration ℝ≥0 mX) (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → Y → ℝ) (ζj : Y → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (ΘL : ℝ≥0 → X → Fin nL → ℝ) (ΘR : ℝ≥0 → X → Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  (open scoped Classical in
    IsStronglyProgressive (usualAugmentation 𝓕k P₁) fun t x => {x | live t x}.indicator (fun _ => (1 : ℝ)) x) ∧
  IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘL ∧ IsStronglyProgressive (usualAugmentation 𝓕k P₁) ΘR ∧
  (∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × (X × Y) => rDrvFst live xj Wj ζj xk Wk (fun _ => p.1) t p.2) ∧
  Measurable (fun p : ℝ≥0 × (X × Y) => rLifeFst live xj Wj ζj xk Wk (fun _ => p.1) p.2) ∧
  ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime (usualAugmentation 𝓕k P₁) fun x => (τ x : WithTop ℝ≥0)),
    ∃ (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))) (VL' : Fin nL → ℝ≥0 → X × Y → ℝ)
      (VR' : Fin nR → ℝ≥0 → X × Y → ℝ) (N : ℝ≥0 → X × Y → ℝ) (S : ℕ → X × Y → ℝ≥0)
      (𝓐 : ℕ → MeasurableSpace X) (𝓑 : ℕ → MeasurableSpace Y) (D : ℕ → X × Y → ℝ≥0∞),
      AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.fst) (comap_fst_le (stoppedSigma_le hτ)) 𝓖)
        (rLifeFst live xj Wj ζj xk Wk τ) (rDrvFst live xj Wj ζj xk Wk τ) ∧
      (∀ i, AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.fst)
        (comap_fst_le (stoppedSigma_le hτ)) 𝓖) (rLifeFst live xj Wj ζj xk Wk τ) (VL' i)) ∧
      (∀ i, AdaptedBefore (supFiltration (hτ.measurableSpace.comap Prod.fst)
        (comap_fst_le (stoppedSigma_le hτ)) 𝓖) (rLifeFst live xj Wj ζj xk Wk τ) (VR' i)) ∧
      (∀ i t, Measurable (VL' i t)) ∧ (∀ i t, Measurable (VR' i t)) ∧
      (∀ z, Continuous (N · z)) ∧ (∀ z, N 0 z = 0) ∧ (∀ t, Measurable[𝓖 t] (N t)) ∧
      (∀ m, IsStoppingTime 𝓖 fun z => (S m z : WithTop ℝ≥0)) ∧
      (∀ m, 𝓐 m ≤ mX) ∧ (∀ m, 𝓑 m ≤ mY) ∧ (∀ m, Measurable (D m)) ∧
      (∀ m (f : X × Y → ℝ≥0∞), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
        ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D m z ∂(P₁.prod P₂)) ∧
      (∀ m (a' : ℝ) (t : ℝ≥0), Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (stopExp a' N (S m) t)) ∧
      (∀ m (s : ℝ≥0) (B : Set X) (A : Set (X × Y)), MeasurableSet[hτ.measurableSpace] B →
        MeasurableSet[𝓖 s] A →
        MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S m z})) ∧
      (∀ m, ∀ᵐ x ∂P₁, ∀ (a' : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
        ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a' N (S m) t z)) (x, y) * D m (x, y) ∂P₂ =
          ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a' N (S m) s z)) (x, y) * D m (x, y) ∂P₂) ∧
      ∀ᵐ z ∂μ, live (τ z.1) z.1 →
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < rLifeFst live xj Wj ζj xk Wk τ z → ∃ m, t ≤ S m z) ∧
        Sec2.IsSLEPathUpTo a (ΘL (τ z.1) z.1) (ΘR (τ z.1) z.1) ρL ρR (fun t => rDrvFst live xj Wj ζj xk Wk τ t z)
          (fun i t => VL' i t z) (fun i t => VR' i t z) (fun t => N t z) (rLifeFst live xj Wj ζj xk Wk τ z)

end Rect

/-! ### The reduction to A1CANON's rectangle core -/

section Reduce

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **Progressive processes of the marginal pull back to progressive processes of the coupling** (usual
augmentations, `comap_usualAugmentation_le_map`). -/
theorem isStronglyProgressive_comap_usualAugmentation {Z W β : Type*} [MeasurableSpace Z] [mW : MeasurableSpace W]
    [TopologicalSpace β] {μ : Measure Z} {π : Z → W} (hπ : Measurable π) {𝓕 : Filtration ℝ≥0 mW}
    {u : ℝ≥0 → W → β} (h : IsStronglyProgressive (usualAugmentation 𝓕 (μ.map π)) u) :
    IsStronglyProgressive (usualAugmentation (Coupling.filtrationComap 𝓕 hπ) μ) fun t z => u t (π z) :=
  isStronglyProgressive_mono (isStronglyProgressive_comap h hπ) fun t => comap_usualAugmentation_le_map hπ t

open scoped Classical in
theorem indicator_comp_eq {Z W : Type*} (π : Z → W) (live : ℝ≥0 → W → Prop) :
    (fun t z => {z | live t (π z)}.indicator (fun _ => (1 : ℝ)) z) =
      fun t z => {w | live t w}.indicator (fun _ => (1 : ℝ)) (π z) := by
  funext t z
  by_cases h : live t (π z)
  · rw [Set.indicator_of_mem (show z ∈ {z | live t (π z)} from h),
      Set.indicator_of_mem (show π z ∈ {w | live t w} from h)]
  · rw [Set.indicator_of_notMem (show z ∉ {z | live t (π z)} from h),
      Set.indicator_of_notMem (show π z ∉ {w | live t w} from h)]

/-- The masked canonical image at a measurable stop is measurable (from the joint measurability (m3)–(m4)). -/
theorem measurable_cImgLifeM_of {Z : Type*} [MeasurableSpace Z] {live : ℝ≥0 → Z → Prop} {xj : ℝ}
    {Wj : ℝ≥0 → Z → ℝ} {ζj : Z → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Z → ℝ}
    (hm4 : Measurable fun p : ℝ≥0 × Z => imgLifeAt live xj Wj ζj xk Wk p.1 p.2) {τ : Z → ℝ≥0}
    (hτ : Measurable τ) : Measurable (cImgLifeM live xj Wj ζj xk Wk τ) :=
  hm4.comp (hτ.prodMk measurable_id)

theorem measurable_cImgDrvM_of {Z : Type*} [MeasurableSpace Z] {live : ℝ≥0 → Z → Prop} {xj : ℝ}
    {Wj : ℝ≥0 → Z → ℝ} {ζj : Z → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Z → ℝ}
    (hm3 : ∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × Z => imgDrvAt live xj Wj ζj xk Wk p.1 t p.2) {τ : Z → ℝ≥0}
    (hτ : Measurable τ) (t : ℝ≥0) : Measurable (cImgDrvM live xj Wj ζj xk Wk τ t) :=
  (hm3 t).comp (hτ.prodMk measurable_id)

/-- The canonical image at two stops that agree at a sample agrees there. -/
theorem cImg_congr_of_eq {Z : Type*} {live : ℝ≥0 → Z → Prop} {xj : ℝ} {Wj : ℝ≥0 → Z → ℝ} {ζj : Z → ℝ≥0∞}
    {xk : ℝ} {Wk : ℝ≥0 → Z → ℝ} {τ τ₀ : Z → ℝ≥0} {z : Z} (hz : τ z = τ₀ z) :
    cImgLifeM live xj Wj ζj xk Wk τ z = cImgLifeM live xj Wj ζj xk Wk τ₀ z ∧
      ∀ t, cImgDrvM live xj Wj ζj xk Wk τ t z = cImgDrvM live xj Wj ζj xk Wk τ₀ t z := by
  refine ⟨?_, fun t => ?_⟩
  · rw [cImgLifeM_eq_imgLifeAt, cImgLifeM_eq_imgLifeAt, hz]
  · rw [cImgDrvM_eq_imgDrvAt, cImgDrvM_eq_imgDrvAt, hz]

/-- **The density form gives A1CANON's rectangle core** (conditioning curve on `Y`): `IsRectImageCore` for the
coupling `μ` with second marginal `P₂` implies `IsCanonImageCore` for the usual augmentation of `snd⁻¹ 𝓕k` under `μ`.
At a stopping time `τ` of that augmentation: `τ = τ' ∘ snd` a.e. with `τ'` a stopping time of the marginal's usual
augmentation (`exists_factor_stoppingTime_map`); the filtration is the null augmentation of `snd⁻¹ 𝓕ᵏ_{τ'} ∨ 𝓖`; the
caps are stopped Brownian motions by `isStoppedBM_of_density`. -/
theorem isCanonImageCore_of_rect {a : ℝ} {nL nR : ℕ} {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁]
    {μ : Measure (X × Y)} [IsProbabilityMeasure μ] (hμ : μ.map Prod.snd = P₂) {𝓕k : Filtration ℝ≥0 mY}
    {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}
    {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h : IsRectImageCore a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) :
    IsCanonImageCore a μ (usualAugmentation (Coupling.filtrationComap 𝓕k measurable_snd) μ)
      (fun t z => live t z.2) xj (fun t z => Wj t z.1) (fun z => ζj z.1) xk (fun t z => Wk t z.2)
      (fun t z => ΘL t z.2) (fun t z => ΘR t z.2) ρL ρR := by
  subst hμ
  obtain ⟨hm1, hm2L, hm2R, hm3, hm4, hcore⟩ := h
  refine ⟨?_, isStronglyProgressive_comap_usualAugmentation measurable_snd hm2L,
    isStronglyProgressive_comap_usualAugmentation measurable_snd hm2R, hm3, hm4, fun τ hτ => ?_⟩
  · rw [indicator_comp_eq Prod.snd live]
    exact isStronglyProgressive_comap_usualAugmentation measurable_snd hm1
  obtain ⟨τ', hτ', hae, hEf⟩ := exists_factor_stoppingTime_map measurable_snd hτ
  obtain ⟨𝓖, VL', VR', N, S, 𝓐, 𝓑, D, hW, hVL, hVR, hVLm, hVRm, hNc, hN0, hNa, hS, h𝓐, h𝓑, hD, hdens,
    hX, hC, hfib, hpath⟩ := hcore τ' hτ'
  set 𝓗₀ := supFiltration (hτ'.measurableSpace.comap Prod.snd) (comap_snd_le (stoppedSigma_le hτ')) 𝓖 with h𝓗₀
  set 𝓗 := Ito.nullAugmented 𝓗₀ μ with h𝓗
  have hle : 𝓗₀ ≤ 𝓗 := fun t => Ito.le_nullAugmented 𝓗₀ μ t
  have h𝓖 : 𝓖 ≤ 𝓗 := fun t => (le_supFiltration _ 𝓖 t).trans (hle t)
  have hN : ∀ t, Ito.nullSets μ ≤ 𝓗 t := fun t => le_sup_right
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hLm := measurable_cImgLifeM_of hm4 hτm
  have hset : ∀ (X' : ℝ≥0 → X × Y → ℝ), (∀ t, Measurable (X' t)) → ∀ (t : ℝ≥0) (A : Set ℝ), MeasurableSet A →
      MeasurableSet {z | (t : ℝ≥0∞) < cImgLifeM (fun t z => live t z.2) xj (fun t z => Wj t z.1)
        (fun z => ζj z.1) xk (fun t z => Wk t z.2) τ z ∧ X' t z ∈ A} :=
    fun X' hX' t A hA => (measurableSet_lt measurable_const hLm).inter (hX' t hA)
  have hagree := fun (z : X × Y) (hz : τ z = τ' z.2) =>
    cImg_congr_of_eq (live := fun t (z : X × Y) => live t z.2) (xj := xj)
      (Wj := fun t (z : X × Y) => Wj t z.1) (ζj := fun z : X × Y => ζj z.1) (xk := xk)
      (Wk := fun t (z : X × Y) => Wk t z.2) (τ₀ := fun z : X × Y => τ' z.2) hz
  refine ⟨𝓗, VL', VR', N, S, ?_, ?_, fun i => ?_, fun i => ?_, hVLm, hVRm, hNc, hN0,
    fun t => (hNa t).mono (h𝓖 t) le_rfl, fun m t => h𝓖 t _ (hS m t), fun m => ?_, ?_⟩
  · intro E hE
    obtain ⟨E', hE', hEE'⟩ := hEf E hE
    exact measurableSet_of_ae_eq_of_nullSets_le (𝓗.le 0) (hN 0) (stoppedSigma_le hτ E hE)
      (hle 0 _ ((le_sup_left : hτ'.measurableSpace.comap Prod.snd ≤ _) _ ⟨E', hE', rfl⟩)) hEE'
  · refine adaptedBefore_of_ae_eq hN (adaptedBefore_mono hW hle)
      (hset _ (measurable_cImgDrvM_of hm3 hτm)) ?_
    filter_upwards [hae] with z hz
    exact hagree z hz
  · refine adaptedBefore_of_ae_eq hN (adaptedBefore_mono (hVL i) hle) (hset _ (hVLm i)) ?_
    filter_upwards [hae] with z hz
    exact ⟨(hagree z hz).1, fun t => rfl⟩
  · refine adaptedBefore_of_ae_eq hN (adaptedBefore_mono (hVR i) hle) (hset _ (hVRm i)) ?_
    filter_upwards [hae] with z hz
    exact ⟨(hagree z hz).1, fun t => rfl⟩
  · exact IsStoppedBM.nullAugmented (isStoppedBM_of_density (hD m) (hdens m) (h𝓐 m) (h𝓑 m)
      (stoppedSigma_le hτ') hNc hN0 hNa (hS m) (hX m) (hC m) (hfib m))
  · filter_upwards [hae, hpath] with z hz hp hlive
    obtain ⟨e1, e2⟩ := hagree z hz
    have e2' : (fun t => cImgDrvM (fun t (z : X × Y) => live t z.2) xj (fun t (z : X × Y) => Wj t z.1)
        (fun z : X × Y => ζj z.1) xk (fun t (z : X × Y) => Wk t z.2) τ t z) =
        fun t => rDrv live xj Wj ζj xk Wk τ' t z := funext e2
    rw [hz] at hlive
    rw [e1, e2', hz]
    exact hp hlive

/-- **The density form gives A1CANON's rectangle core** (conditioning curve on `X`): the mirror of
`isCanonImageCore_of_rect`. -/
theorem isCanonImageCore_of_rect_fst {a : ℝ} {nL nR : ℕ} {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₂]
    {μ : Measure (X × Y)} [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P₁) {𝓕k : Filtration ℝ≥0 mX}
    {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}
    {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (h : IsRectImageCoreFst a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) :
    IsCanonImageCore a μ (usualAugmentation (Coupling.filtrationComap 𝓕k measurable_fst) μ)
      (fun t z => live t z.1) xj (fun t z => Wj t z.2) (fun z => ζj z.2) xk (fun t z => Wk t z.1)
      (fun t z => ΘL t z.1) (fun t z => ΘR t z.1) ρL ρR := by
  subst hμ
  obtain ⟨hm1, hm2L, hm2R, hm3, hm4, hcore⟩ := h
  refine ⟨?_, isStronglyProgressive_comap_usualAugmentation measurable_fst hm2L,
    isStronglyProgressive_comap_usualAugmentation measurable_fst hm2R, hm3, hm4, fun τ hτ => ?_⟩
  · rw [indicator_comp_eq Prod.fst live]
    exact isStronglyProgressive_comap_usualAugmentation measurable_fst hm1
  obtain ⟨τ', hτ', hae, hEf⟩ := exists_factor_stoppingTime_map measurable_fst hτ
  obtain ⟨𝓖, VL', VR', N, S, 𝓐, 𝓑, D, hW, hVL, hVR, hVLm, hVRm, hNc, hN0, hNa, hS, h𝓐, h𝓑, hD, hdens,
    hX, hC, hfib, hpath⟩ := hcore τ' hτ'
  set 𝓗₀ := supFiltration (hτ'.measurableSpace.comap Prod.fst) (comap_fst_le (stoppedSigma_le hτ')) 𝓖 with h𝓗₀
  set 𝓗 := Ito.nullAugmented 𝓗₀ μ with h𝓗
  have hle : 𝓗₀ ≤ 𝓗 := fun t => Ito.le_nullAugmented 𝓗₀ μ t
  have h𝓖 : 𝓖 ≤ 𝓗 := fun t => (le_supFiltration _ 𝓖 t).trans (hle t)
  have hN : ∀ t, Ito.nullSets μ ≤ 𝓗 t := fun t => le_sup_right
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hLm := measurable_cImgLifeM_of hm4 hτm
  have hset : ∀ (X' : ℝ≥0 → X × Y → ℝ), (∀ t, Measurable (X' t)) → ∀ (t : ℝ≥0) (A : Set ℝ), MeasurableSet A →
      MeasurableSet {z | (t : ℝ≥0∞) < cImgLifeM (fun t z => live t z.1) xj (fun t z => Wj t z.2)
        (fun z => ζj z.2) xk (fun t z => Wk t z.1) τ z ∧ X' t z ∈ A} :=
    fun X' hX' t A hA => (measurableSet_lt measurable_const hLm).inter (hX' t hA)
  have hagree := fun (z : X × Y) (hz : τ z = τ' z.1) =>
    cImg_congr_of_eq (live := fun t (z : X × Y) => live t z.1) (xj := xj)
      (Wj := fun t (z : X × Y) => Wj t z.2) (ζj := fun z : X × Y => ζj z.2) (xk := xk)
      (Wk := fun t (z : X × Y) => Wk t z.1) (τ₀ := fun z : X × Y => τ' z.1) hz
  refine ⟨𝓗, VL', VR', N, S, ?_, ?_, fun i => ?_, fun i => ?_, hVLm, hVRm, hNc, hN0,
    fun t => (hNa t).mono (h𝓖 t) le_rfl, fun m t => h𝓖 t _ (hS m t), fun m => ?_, ?_⟩
  · intro E hE
    obtain ⟨E', hE', hEE'⟩ := hEf E hE
    exact measurableSet_of_ae_eq_of_nullSets_le (𝓗.le 0) (hN 0) (stoppedSigma_le hτ E hE)
      (hle 0 _ ((le_sup_left : hτ'.measurableSpace.comap Prod.fst ≤ _) _ ⟨E', hE', rfl⟩)) hEE'
  · refine adaptedBefore_of_ae_eq hN (adaptedBefore_mono hW hle)
      (hset _ (measurable_cImgDrvM_of hm3 hτm)) ?_
    filter_upwards [hae] with z hz
    exact hagree z hz
  · refine adaptedBefore_of_ae_eq hN (adaptedBefore_mono (hVL i) hle) (hset _ (hVLm i)) ?_
    filter_upwards [hae] with z hz
    exact ⟨(hagree z hz).1, fun t => rfl⟩
  · refine adaptedBefore_of_ae_eq hN (adaptedBefore_mono (hVR i) hle) (hset _ (hVRm i)) ?_
    filter_upwards [hae] with z hz
    exact ⟨(hagree z hz).1, fun t => rfl⟩
  · exact IsStoppedBM.nullAugmented (isStoppedBM_of_density_fst (hD m) (hdens m) (h𝓐 m) (h𝓑 m)
      (stoppedSigma_le hτ') hNc hN0 hNa (hS m) (hX m) (hC m) (hfib m))
  · filter_upwards [hae, hpath] with z hz hp hlive
    obtain ⟨e1, e2⟩ := hagree z hz
    have e2' : (fun t => cImgDrvM (fun t (z : X × Y) => live t z.1) xj (fun t (z : X × Y) => Wj t z.2)
        (fun z : X × Y => ζj z.2) xk (fun t (z : X × Y) => Wk t z.1) τ t z) =
        fun t => rDrvFst live xj Wj ζj xk Wk τ' t z := funext e2
    rw [hz] at hlive
    rw [e1, e2', hz]
    exact hp hlive

end Reduce

end InteractingSLE.ZhanGT4.A1Core
