/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CanonStopBM
import InteractingSLE.Spec.ZhanGT4.A1CanonFactor
import InteractingSLE.Spec.ZhanGT4.A1RefCond
import InteractingSLE.Spec.ZhanGT4.A1DualComap

/-!
# A.1's conditional image law from its rectangle core

Packet PROVE-ZHAN-A1CANON. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.5 (L345–L425, R38), follow-up 4 §2.5
(L841–L847, R71), follow-up 5 §1.3 (L203–L222, R73).

`A1Ref.IsCanonImageLaw` asks, at every stopping time `τ` of curve `k`, for a Brownian motion `B'` of a filtration
`𝓖 ⊇ 𝓕ᵏ_τ` driving the canonical image of curve `j`. The source supplies the image law only inside each protected
rectangle — the image noise is a Brownian motion up to the image of the rectangle exit — and obtains the law up to
first contact by "countable protected-rectangle exhaustion". This file isolates that rectangle content as
`IsCanonImageCore` and proves the exhaustion, the continuation of the noise after the contact by an independent
Brownian motion, and the passage to the usual augmentation of the reference space `X × Y`:

* `IsCanonImageCore`: measurability of the live event, the image words and the canonical image (jointly in the stop),
  and, at every stopping time `τ` of `𝓕k`, a filtration `𝓗 ⊇ 𝓕ᵏ_τ`, image force points, a continuous image noise `N`
  and countably many caps `S m` (`𝓗`-stopping times) with `N` an `𝓗`-Brownian motion stopped at each cap
  (`IsStoppedBM`), the caps covering the image lifetime, and the local path conditions with `N` as the noise;
* **`isCanonImageLaw_prod_of_core`**: the core on `(X, μ)` for `usualAugmentation 𝓕 μ` gives `IsCanonImageLaw` on
  `(X × Y, μ ⊗ ν)` for `usualAugmentation (𝓕 ∘ fst) (μ ⊗ ν)` and the pulled-back processes, for any probability space
  `Y` carrying a Brownian motion with continuous paths from `0`.

The tools: `isStronglyProgressive_comap`, `isStronglyProgressive_mono`, `adaptedBefore_mono`,
`adaptedBefore_of_ae_eq` (null modifications in a filtration containing the null sets), `isSLEPathUpTo_congr_noise`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Canon

open A1Ref

/-! ### Generic tools -/

section Tools

/-- Pullback of a progressively measurable process. -/
theorem isStronglyProgressive_comap {X Z β : Type*} [mX : MeasurableSpace X] [MeasurableSpace Z]
    [TopologicalSpace β] {𝓕 : Filtration ℝ≥0 mX} {u : ℝ≥0 → X → β} (h : IsStronglyProgressive 𝓕 u)
    {π : Z → X} (hπ : Measurable π) :
    IsStronglyProgressive (Coupling.filtrationComap 𝓕 hπ) fun t z => u t (π z) := by
  intro i
  have hg : Measurable[@Prod.instMeasurableSpace _ _ _ ((𝓕 i).comap π),
      @Prod.instMeasurableSpace _ _ _ (𝓕 i)] fun p : Set.Iic i × Z => (p.1, π p.2) :=
    @Measurable.prodMk _ _ _ (_) (_) (_) _ _ (@measurable_fst _ _ _ ((𝓕 i).comap π))
      ((comap_measurable π).comp (@measurable_snd _ _ _ ((𝓕 i).comap π)))
  exact (h i).comp_measurable hg

/-- A progressively measurable process is progressively measurable for every larger filtration. -/
theorem isStronglyProgressive_mono {Ω β : Type*} {mΩ : MeasurableSpace Ω} [TopologicalSpace β]
    {𝓕 𝓖 : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → β} (h : IsStronglyProgressive 𝓕 u) (hle : 𝓕 ≤ 𝓖) :
    IsStronglyProgressive 𝓖 u := fun i =>
  (h i).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (hle i)))

/-- `AdaptedBefore` for a larger filtration. -/
theorem adaptedBefore_mono {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 𝓖 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞}
    {X : ℝ≥0 → Ω → ℝ} (h : AdaptedBefore 𝓕 ζ X) (hle : 𝓕 ≤ 𝓖) : AdaptedBefore 𝓖 ζ X :=
  fun t A hA => hle t _ (h t A hA)

/-- **Null modifications of a process adapted before its lifetime**, in a filtration containing the null sets: a
process measurable before its lifetime and almost surely equal (lifetime and values before it) to one adapted
before its lifetime is adapted before its lifetime. -/
theorem adaptedBefore_of_ae_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
    (hN : ∀ t, Ito.nullSets P ≤ 𝓖 t) {ζ ζ₀ : Ω → ℝ≥0∞} {X X₀ : ℝ≥0 → Ω → ℝ} (h₀ : AdaptedBefore 𝓖 ζ₀ X₀)
    (hm : ∀ (t : ℝ≥0) (A : Set ℝ), MeasurableSet A → MeasurableSet {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A})
    (hae : ∀ᵐ ω ∂P, ζ ω = ζ₀ ω ∧ ∀ t : ℝ≥0, X t ω = X₀ t ω) : AdaptedBefore 𝓖 ζ X := by
  intro t A hA
  refine measurableSet_of_ae_eq_of_nullSets_le (𝓖.le t) (hN t) (hm t A hA) (h₀ t A hA) ?_
  filter_upwards [hae] with ω hω
  simp only [hω.1, hω.2 t]

/-- The local path conditions read the noise only before the lifetime. -/
theorem isSLEPathUpTo_congr_noise {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b b' : ℝ≥0 → ℝ}
    {ζ : ℝ≥0∞} (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ)
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → b t = b' t) : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b' ζ :=
  { h with w_eq := fun {t} ht => by rw [← hb t ht]; exact h.w_eq ht }

end Tools

/-! ### The canonical image at a deterministic stop -/

section At

variable {X : Type*} [mX : MeasurableSpace X]

/-- The masked canonical image driver at the deterministic stop `s` (`cImgDrvM` with `τ ≡ s`). -/
def imgDrvAt (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (s t : ℝ≥0) (x : X) : ℝ :=
  cImgDrvM live xj Wj ζj xk Wk (fun _ => s) t x

/-- The masked canonical image lifetime at the deterministic stop `s`. -/
def imgLifeAt (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (s : ℝ≥0) (x : X) : ℝ≥0∞ :=
  cImgLifeM live xj Wj ζj xk Wk (fun _ => s) x

omit mX in
theorem cImgDrvM_eq_imgDrvAt (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (τ : X → ℝ≥0) (t : ℝ≥0) (x : X) :
    cImgDrvM live xj Wj ζj xk Wk τ t x = imgDrvAt live xj Wj ζj xk Wk (τ x) t x := rfl

omit mX in
theorem cImgLifeM_eq_imgLifeAt (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ)
    (Wk : ℝ≥0 → X → ℝ) (τ : X → ℝ≥0) (x : X) :
    cImgLifeM live xj Wj ζj xk Wk τ x = imgLifeAt live xj Wj ζj xk Wk (τ x) x := rfl

omit mX in
/-- The canonical image of pulled-back processes is the pulled-back canonical image. -/
theorem cImgDrvM_comp {Z : Type*} (π : Z → X) (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ)
    (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ) (τ : Z → ℝ≥0) (t : ℝ≥0) (z : Z) :
    cImgDrvM (fun t z => live t (π z)) xj (fun t z => Wj t (π z)) (fun z => ζj (π z)) xk
        (fun t z => Wk t (π z)) τ t z = imgDrvAt live xj Wj ζj xk Wk (τ z) t (π z) := rfl

omit mX in
theorem cImgLifeM_comp {Z : Type*} (π : Z → X) (live : ℝ≥0 → X → Prop) (xj : ℝ) (Wj : ℝ≥0 → X → ℝ)
    (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ) (τ : Z → ℝ≥0) (z : Z) :
    cImgLifeM (fun t z => live t (π z)) xj (fun t z => Wj t (π z)) (fun z => ζj (π z)) xk
        (fun t z => Wk t (π z)) τ z = imgLifeAt live xj Wj ζj xk Wk (τ z) (π z) := rfl

end At

/-! ### The rectangle core -/

section Core

variable {X : Type*} [mX : MeasurableSpace X]

/-- **The rectangle core of A.1's conditional image law** (A.1.3: the image law inside one protected rectangle;
follow-up 5 (1.7): at usual-augmentation stopping times of curve `k`, by optional sampling of the joint density).

Measurability: the live event and the image words are progressively measurable for `𝓕k`, and the masked canonical
image driver and lifetime are measurable jointly in the (deterministic) stop and the sample.

At every stopping time `τ` of `𝓕k`: a filtration `𝓗` with `𝓕ᵏ_τ ≤ 𝓗 0` to which the masked canonical image driver
`W' = cImgDrvM … τ` is adapted before the masked image lifetime `ζ' = cImgLifeM … τ`, measurable image force points
`VL'`, `VR'` adapted before `ζ'`, a continuous `𝓗`-adapted image noise `N` from `0`, and caps `S m` (`𝓗`-stopping
times, e.g. the images of the rectangle exits, `0` off the live event) such that `N` is an `𝓗`-Brownian motion stopped
at every cap (`IsStoppedBM`; from a rectangle's own Brownian motion by `isStoppedBM_of_agree`), and almost surely on
the live event the caps cover `[0, ζ')` and the image is a local `SLE_a(ρ)` path of the image word before `ζ'` with
noise `N`. -/
def IsCanonImageCore (a : ℝ) {nL nR : ℕ} (P : Measure X) (𝓕k : Filtration ℝ≥0 mX) (live : ℝ≥0 → X → Prop)
    (xj : ℝ) (Wj : ℝ≥0 → X → ℝ) (ζj : X → ℝ≥0∞) (xk : ℝ) (Wk : ℝ≥0 → X → ℝ)
    (ΘL : ℝ≥0 → X → Fin nL → ℝ) (ΘR : ℝ≥0 → X → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  (open scoped Classical in IsStronglyProgressive 𝓕k fun t x => {x | live t x}.indicator (fun _ => (1 : ℝ)) x) ∧
  IsStronglyProgressive 𝓕k ΘL ∧ IsStronglyProgressive 𝓕k ΘR ∧
  (∀ t : ℝ≥0, Measurable fun p : ℝ≥0 × X => imgDrvAt live xj Wj ζj xk Wk p.1 t p.2) ∧
  Measurable (fun p : ℝ≥0 × X => imgLifeAt live xj Wj ζj xk Wk p.1 p.2) ∧
  ∀ (τ : X → ℝ≥0) (hτ : IsStoppingTime 𝓕k fun x => (τ x : WithTop ℝ≥0)),
    ∃ (𝓗 : Filtration ℝ≥0 mX) (VL' : Fin nL → ℝ≥0 → X → ℝ) (VR' : Fin nR → ℝ≥0 → X → ℝ) (N : ℝ≥0 → X → ℝ)
      (S : ℕ → X → ℝ≥0),
      hτ.measurableSpace ≤ 𝓗 0 ∧
      AdaptedBefore 𝓗 (cImgLifeM live xj Wj ζj xk Wk τ) (cImgDrvM live xj Wj ζj xk Wk τ) ∧
      (∀ i, AdaptedBefore 𝓗 (cImgLifeM live xj Wj ζj xk Wk τ) (VL' i)) ∧
      (∀ i, AdaptedBefore 𝓗 (cImgLifeM live xj Wj ζj xk Wk τ) (VR' i)) ∧
      (∀ i t, Measurable (VL' i t)) ∧ (∀ i t, Measurable (VR' i t)) ∧
      (∀ x, Continuous (N · x)) ∧ (∀ x, N 0 x = 0) ∧ (∀ t, Measurable[𝓗 t] (N t)) ∧
      (∀ m, IsStoppingTime 𝓗 fun x => (S m x : WithTop ℝ≥0)) ∧ (∀ m, IsStoppedBM P 𝓗 N (S m)) ∧
      ∀ᵐ x ∂P, live (τ x) x →
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < cImgLifeM live xj Wj ζj xk Wk τ x → ∃ m, t ≤ S m x) ∧
        Sec2.IsSLEPathUpTo a (ΘL (τ x) x) (ΘR (τ x) x) ρL ρR (fun t => cImgDrvM live xj Wj ζj xk Wk τ t x)
          (fun i t => VL' i t x) (fun i t => VR' i t x) (fun t => N t x) (cImgLifeM live xj Wj ζj xk Wk τ x)

end Core

/-! ### The transfer to the reference space `X × Y` -/

section Transfer

/-- A stopping time with finite values is measurable. -/
theorem measurable_of_isStoppingTime {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m} {τ : Ω → ℝ≥0}
    (h : IsStoppingTime 𝓕 fun ω => (τ ω : WithTop ℝ≥0)) : Measurable τ := by
  refine measurable_of_Iic fun x => ?_
  have e : τ ⁻¹' Iic x = {ω | (τ ω : WithTop ℝ≥0) ≤ x} := by
    ext ω; simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_ofPred_eq, WithTop.coe_le_coe]
  rw [e]
  exact 𝓕.le x _ (h x)

theorem stoppedValue_coe {Ω β : Type*} (u : ℝ≥0 → Ω → β) (τ : Ω → ℝ≥0) :
    stoppedValue u (fun ω => (τ ω : WithTop ℝ≥0)) = fun ω => u (τ ω) ω := by
  funext ω
  simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {𝓕 : Filtration ℝ≥0 mX}

omit [IsProbabilityMeasure μ] in
/-- Progressive measurability for `usualAugmentation 𝓕 μ` pulls back to the usual augmentation of the pullback. -/
theorem isStronglyProgressive_fst {β : Type*} [TopologicalSpace β] {u : ℝ≥0 → X → β}
    (h : IsStronglyProgressive (usualAugmentation 𝓕 μ) u) :
    IsStronglyProgressive (usualAugmentation (Coupling.filtrationComap 𝓕
      (measurable_fst : Measurable (Prod.fst : X × Y → X))) (μ.prod ν)) fun t ω => u t ω.1 :=
  isStronglyProgressive_mono (isStronglyProgressive_comap h measurable_fst) fun t => comap_usualAugmentation_le 𝓕 t

/-- **A.1's conditional image law on the reference space from its rectangle core.** If `IsCanonImageCore` holds on
`(X, μ)` for the usual augmentation of `𝓕`, then on `X × Y` with `μ ⊗ ν` (`Y` carrying a Brownian motion `β` with
continuous paths from `0`) the pulled-back processes satisfy `IsCanonImageLaw` for the usual augmentation of the
pulled-back filtration: at a stopping time `τ`, factor it as `τ' ∘ fst` up to a null set
(`exists_factor_stoppingTime`), patch the caps of the core at `τ'` and continue the image noise by `β`
(`isFilteredBrownianReal_capNoise`), and take the usual augmentation of `𝓗 ⊗ 𝓦` as the filtration. -/
theorem isCanonImageLaw_prod_of_core {a : ℝ} {nL nR : ℕ} {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ}
    {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ} {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hcore : IsCanonImageCore a μ (usualAugmentation 𝓕 μ) live xj Wj ζj xk Wk ΘL ΘR ρL ρR)
    {𝓦 : Filtration ℝ≥0 mY} {β : ℝ≥0 → Y → ℝ} (hβ : IsFilteredBrownianReal 𝓦 β ν)
    (hβc : ∀ y, Continuous (β · y)) (hβ0 : ∀ y, β 0 y = 0) :
    IsCanonImageLaw a (μ.prod ν) (usualAugmentation (Coupling.filtrationComap 𝓕
        (measurable_fst : Measurable (Prod.fst : X × Y → X))) (μ.prod ν))
      (fun t ω => live t ω.1) xj (fun t ω => Wj t ω.1) (fun ω => ζj ω.1) xk (fun t ω => Wk t ω.1)
      (fun t ω => ΘL t ω.1) (fun t ω => ΘR t ω.1) ρL ρR := by
  classical
  obtain ⟨hliveP, hΘLP, hΘRP, hDm, hLm, hcore⟩ := hcore
  intro τ hτ
  set P := μ.prod ν with hP
  set 𝓕' := Coupling.filtrationComap 𝓕 (measurable_fst : Measurable (Prod.fst : X × Y → X)) with h𝓕'
  have hmap : P.map Prod.fst = μ := by rw [hP, Measure.map_fst_prod, measure_univ, one_smul]
  obtain ⟨τ', hτ', hae, hE⟩ := exists_factor_stoppingTime hτ
  obtain ⟨𝓗, VL', VR', N, S, h𝓔, hWa, hVLa, hVRa, hVLm, hVRm, hNc, hN0, hNa, hSst, hSbm, hpath⟩ := hcore τ' hτ'
  obtain ⟨hB, -, hBeq⟩ := isFilteredBrownianReal_capNoise hSbm hSst hNc hN0 hβ hβc hβ0
  set 𝓖 := usualAugmentation (WholeField.prodFiltration 𝓗 𝓦) P with h𝓖
  have h𝓖N : ∀ t, Ito.nullSets P ≤ 𝓖 t := Ito.nullSets_le_usualAugmentation _ _
  have hcomap : Coupling.filtrationComap 𝓗 (measurable_fst : Measurable (Prod.fst : X × Y → X)) ≤ 𝓖 := fun t =>
    (WholeField.comap_fst_le_prodFiltration 𝓗 𝓦 t).trans (Ito.le_usualAugmentation _ _ t)
  have hτm : Measurable τ := measurable_of_isStoppingTime hτ
  have hg : Measurable fun ω : X × Y => ((τ ω, ω.1) : ℝ≥0 × X) := hτm.prodMk measurable_fst
  have hlifem : Measurable fun ω : X × Y => imgLifeAt live xj Wj ζj xk Wk (τ ω) ω.1 := hLm.comp hg
  have hlt : ∀ t : ℝ≥0, MeasurableSet {ω : X × Y | (t : ℝ≥0∞) < imgLifeAt live xj Wj ζj xk Wk (τ ω) ω.1} :=
    fun t => measurableSet_lt measurable_const hlifem
  have hlife : ∀ᵐ ω ∂P, imgLifeAt live xj Wj ζj xk Wk (τ ω) ω.1 = cImgLifeM live xj Wj ζj xk Wk τ' ω.1 := by
    filter_upwards [hae] with ω hω
    rw [cImgLifeM_eq_imgLifeAt, hω]
  refine ⟨𝓖, fun i t ω => VL' i t ω.1, fun i t ω => VR' i t ω.1,
    WholeField.complNoise (fun u x => N (WholeField.annClock (capMax S) u x) x)
      (WholeField.annClock (capMax S)) β, ?_, ?_, ?_, ?_, Ito.isFilteredBrownianReal_usualAugmentation hB,
    ?_, ?_, ?_, ?_⟩
  · -- `𝓕ᵏ_τ ≤ 𝓖₀`
    intro E hEm
    obtain ⟨E', hE', hEE'⟩ := hE E hEm
    have hEmeas : MeasurableSet E := (iSup_le fun t => (usualAugmentation 𝓕' P).le t) _ hEm.1
    exact measurableSet_of_ae_eq_of_nullSets_le (𝓖.le 0) (h𝓖N 0) hEmeas (hcomap 0 _ ⟨E', h𝓔 _ hE', rfl⟩) hEE'
  · -- the live event
    have h1 := measurable_stoppedValue (isStronglyProgressive_fst (ν := ν) hliveP) hτ
    rw [stoppedValue_coe] at h1
    have e : {ω : X × Y | live (τ ω) ω.1} =
        (fun ω : X × Y => {x | live (τ ω) x}.indicator (fun _ => (1 : ℝ)) ω.1) ⁻¹' {1} := by
      ext ω
      by_cases hω : live (τ ω) ω.1 <;> simp [Set.indicator, hω]
    rw [e]
    exact h1 (measurableSet_singleton 1)
  · have h1 := measurable_stoppedValue (isStronglyProgressive_fst (ν := ν) hΘLP) hτ
    rwa [stoppedValue_coe] at h1
  · have h1 := measurable_stoppedValue (isStronglyProgressive_fst (ν := ν) hΘRP) hτ
    rwa [stoppedValue_coe] at h1
  · -- the canonical image driver
    refine adaptedBefore_of_ae_eq h𝓖N (ζ₀ := fun ω => cImgLifeM live xj Wj ζj xk Wk τ' ω.1)
      (X₀ := fun t ω => cImgDrvM live xj Wj ζj xk Wk τ' t ω.1)
      (adaptedBefore_mono (A1Dual.adaptedBefore_comap measurable_fst hWa) hcomap) (fun t A hA => ?_) ?_
    · exact (hlt t).inter (((hDm t).comp hg) hA)
    · filter_upwards [hae] with ω hω
      refine ⟨?_, fun t => ?_⟩
      · rw [cImgLifeM_comp, cImgLifeM_eq_imgLifeAt, hω]
      · rw [cImgDrvM_comp, cImgDrvM_eq_imgDrvAt, hω]
  · intro i
    refine adaptedBefore_of_ae_eq h𝓖N (ζ₀ := fun ω => cImgLifeM live xj Wj ζj xk Wk τ' ω.1)
      (X₀ := fun t ω => VL' i t ω.1) (adaptedBefore_mono (A1Dual.adaptedBefore_comap measurable_fst (hVLa i)) hcomap)
      (fun t A hA => (hlt t).inter (((hVLm i t).comp measurable_fst) hA)) ?_
    filter_upwards [hlife] with ω hω
    exact ⟨by rw [cImgLifeM_comp]; exact hω, fun _ => rfl⟩
  · intro i
    refine adaptedBefore_of_ae_eq h𝓖N (ζ₀ := fun ω => cImgLifeM live xj Wj ζj xk Wk τ' ω.1)
      (X₀ := fun t ω => VR' i t ω.1) (adaptedBefore_mono (A1Dual.adaptedBefore_comap measurable_fst (hVRa i)) hcomap)
      (fun t A hA => (hlt t).inter (((hVRm i t).comp measurable_fst) hA)) ?_
    filter_upwards [hlife] with ω hω
    exact ⟨by rw [cImgLifeM_comp]; exact hω, fun _ => rfl⟩
  · -- the local path conditions, almost surely on the live event
    have hpath' := A1Dual.ae_comp_of_map_eq measurable_fst hmap hpath
    filter_upwards [hae, hpath'] with ω hω hp hlive
    have hlive' : live (τ' ω.1) ω.1 := by
      have h0 : live (τ ω) ω.1 := hlive
      rwa [hω] at h0
    obtain ⟨hcov, hsle⟩ := hp hlive'
    have e1 : (fun t => cImgDrvM (fun t ω => live t ω.1) xj (fun t ω => Wj t ω.1) (fun ω => ζj ω.1) xk
        (fun t ω => Wk t ω.1) τ t ω) = fun t => cImgDrvM live xj Wj ζj xk Wk τ' t ω.1 := by
      funext t
      rw [cImgDrvM_comp, cImgDrvM_eq_imgDrvAt, hω]
    have e2 : cImgLifeM (fun t ω => live t ω.1) xj (fun t ω => Wj t ω.1) (fun ω => ζj ω.1) xk
        (fun t ω => Wk t ω.1) τ ω = cImgLifeM live xj Wj ζj xk Wk τ' ω.1 := by
      rw [cImgLifeM_comp, cImgLifeM_eq_imgLifeAt, hω]
    show Sec2.IsSLEPathUpTo a (ΘL (τ ω) ω.1) (ΘR (τ ω) ω.1) ρL ρR _ _ _ _ _
    rw [e1, e2, hω]
    refine isSLEPathUpTo_congr_noise hsle fun t ht => ?_
    obtain ⟨m, hm⟩ := hcov t ht
    exact (hBeq ω t m hm).symm

end Transfer

end InteractingSLE.ZhanGT4.A1Canon
