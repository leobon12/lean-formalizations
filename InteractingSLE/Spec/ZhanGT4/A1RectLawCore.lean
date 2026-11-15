/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RectLawMask
import InteractingSLE.Spec.ZhanGT4.A1CoreRect

/-!
# Zhan's A.1: the rectangle core with a noise continuous only before the caps

Packet PROVE-A1-RECTLAW (proposed repair of the global-continuity clause; see the handoff). A1CORE's
`IsRectImageCore` asks the image noise to be continuous on all of `ℝ≥0` at every sample, which, together with its
record clauses and the cover of the image lifetime by the caps, cannot be met by the record-local compensated residual
in general. `IsRectImageCoreC` is the same statement with the noise continuous only before each cap. It still gives
A1CANON's `IsCanonImageCore`:

* `isStoppedBM_of_density_of_continuousOn`: conditional Girsanov assembled (`isStoppedBM_of_density`) for a noise
  continuous before the cap only (apply it to the noise stopped at the cap);
* `IsSLEPathUpTo.congr_noise`: a local path only reads the noise before its horizon;
* `IsRectImageCore.toC`: the old statement implies the new one;
* **`isCanonImageCore_of_rectC`**: `IsRectImageCoreC ⇒ IsCanonImageCore` (with an auxiliary continuous Brownian motion
  `β`): at the stop, the noise is replaced by the masked continuous noise `exists_continuous_noise_of_isStoppedBM`
  (equal to it before every cap almost surely), which lives in the null-augmented filtration already used by
  `isCanonImageCore_of_rect`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RectLaw

open A1Canon A1Ref A1Core

/-! ### Conditional Girsanov for a noise continuous before the cap -/

section Density

variable {X Y : Type*} {𝓐 : MeasurableSpace X} {𝓑 𝓔 : MeasurableSpace Y} [mX : MeasurableSpace X]
  [mY : MeasurableSpace Y]

/-- **`isStoppedBM_of_density` for a noise continuous before the cap only.** -/
theorem isStoppedBM_of_density_of_continuousOn {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] {D : X × Y → ℝ≥0∞} (hD : Measurable D)
    (hdens : ∀ f : X × Y → ℝ≥0∞, Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] f →
      ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D z ∂(P₁.prod P₂))
    (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY) (h𝓔 : 𝓔 ≤ mY)
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    (hNc : ∀ z, ContinuousOn (N · z) (Icc 0 (S z))) (hN0 : ∀ z, N 0 z = 0) (hNa : ∀ t, Measurable[𝓖 t] (N t))
    (hS : IsStoppingTime 𝓖 fun z => (S z : WithTop ℝ≥0))
    (hX : ∀ (a : ℝ) (t : ℝ≥0), Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (stopExp a N S t))
    (hC : ∀ (s : ℝ≥0) (B : Set Y) (A : Set (X × Y)), MeasurableSet[𝓔] B → MeasurableSet[𝓖 s] A →
      MeasurableSet[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (Prod.snd ⁻¹' B ∩ A ∩ {z | s < S z}))
    (hfib : ∀ᵐ y ∂P₂, ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₁ =
        ∫⁻ x, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₁) :
    IsStoppedBM μ (supFiltration (𝓔.comap Prod.snd) (comap_snd_le h𝓔) 𝓖) N S := by
  have e : ∀ a, stopExp a (stoppedAt N S) S = stopExp a N S := fun a => stopExp_stoppedAt a S
  have h := isStoppedBM_of_density (N := stoppedAt N S) hD hdens h𝓐 h𝓑 h𝓔 (continuous_stoppedAt hNc)
    (fun z => by simp only [stoppedAt, zero_min, hN0]) (measurable_stopped_of_continuousOn hNa hS hNc) hS
    (fun a t => by rw [e]; exact hX a t) hC (by simp only [e]; exact hfib)
  intro a
  rw [← e]
  exact h a

end Density

/-! ### Local paths only read the noise before the horizon -/

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A local `SLE_a(ρ)` path reads its noise only before the horizon.** -/
theorem IsSLEPathUpTo.congr_noise {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b b' : ℝ≥0 → ℝ} {τ : ℝ≥0∞} (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    (hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → b' t = b t) : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b' τ where
  w_zero := h.w_zero
  vL_zero := h.vL_zero
  vR_zero := h.vR_zero
  continuousOn_w := h.continuousOn_w
  continuousOn_vL := h.continuousOn_vL
  continuousOn_vR := h.continuousOn_vR
  antitone_vL := h.antitone_vL
  vL_le_w := h.vL_le_w
  w_le_vR := h.w_le_vR
  monotone_vR := h.monotone_vR
  integrable_gapL := h.integrable_gapL
  integrable_gapR := h.integrable_gapR
  w_eq := fun {t} ht => by rw [hb t ht]; exact h.w_eq ht
  vL_eq := h.vL_eq
  vR_eq := h.vR_eq
  volume_collisionL := h.volume_collisionL
  volume_collisionR := h.volume_collisionR
  not_threshold := h.not_threshold

end Path

/-! ### The rectangle core with a noise continuous before the caps -/

section Rect

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **A.1's rectangle core in density form, noise continuous before each cap** (conditioning curve on `Y`): A1CORE's
`IsRectImageCore` with `∀ z, Continuous (N · z)` replaced by `∀ m z, ContinuousOn (N · z) (Icc 0 (S m z))`. -/
def IsRectImageCoreC (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
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
      (∀ m z, ContinuousOn (N · z) (Icc 0 (S m z))) ∧ (∀ z, N 0 z = 0) ∧ (∀ t, Measurable[𝓖 t] (N t)) ∧
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

variable {a : ℝ} {nL nR : ℕ} {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓕k : Filtration ℝ≥0 mY}
  {live : ℝ≥0 → Y → Prop} {xj : ℝ} {Wj : ℝ≥0 → X → ℝ} {ζj : X → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → Y → ℝ}
  {ΘL : ℝ≥0 → Y → Fin nL → ℝ} {ΘR : ℝ≥0 → Y → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The old rectangle core implies the new one** (global continuity gives continuity before each cap). -/
theorem IsRectImageCore.toC (h : IsRectImageCore a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) :
    IsRectImageCoreC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  obtain ⟨h1, h2, h3, h4, h5, h⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun τ hτ => ?_⟩
  obtain ⟨𝓖, VL', VR', N, S, 𝓐, 𝓑, D, hW, hVL, hVR, hVLm, hVRm, hNc, hrest⟩ := h τ hτ
  exact ⟨𝓖, VL', VR', N, S, 𝓐, 𝓑, D, hW, hVL, hVR, hVLm, hVRm, fun _ z => (hNc z).continuousOn, hrest⟩

/-- **The rectangle core with a noise continuous before the caps gives A1CANON's rectangle core** (conditioning curve
on `Y`; `isCanonImageCore_of_rect` for `IsRectImageCoreC`). At a stopping time of the coupling's filtration the noise
of the rectangle core is a stopped Brownian motion at every cap (`isStoppedBM_of_density_of_continuousOn`); it is
replaced by the masked continuous noise of `exists_continuous_noise_of_isStoppedBM` (null augmentation, equal to it
before every cap almost surely, hence on the whole image life on the live event, where the caps cover it). -/
theorem isCanonImageCore_of_rectC [SFinite P₁] [IsProbabilityMeasure μ] (hμ : μ.map Prod.snd = P₂)
    (h : IsRectImageCoreC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓦 : Filtration ℝ≥0 m₀} {β : ℝ≥0 → Ω₀ → ℝ}
    (hβ : IsFilteredBrownianReal 𝓦 β P₀) (hβc : ∀ w, Continuous (β · w)) (hβ0 : ∀ w, β 0 w = 0) :
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
  -- the stopped Brownian motions at the caps and the masked continuous noise
  have hS₀ : ∀ m, IsStoppingTime 𝓗₀ fun z => (S m z : WithTop ℝ≥0) := fun m t =>
    le_supFiltration _ 𝓖 t _ (hS m t)
  have hNa₀ : ∀ t, Measurable[𝓗₀ t] (N t) := fun t => (hNa t).mono (le_supFiltration _ 𝓖 t) le_rfl
  have hbm : ∀ m, IsStoppedBM μ 𝓗₀ N (S m) := fun m =>
    isStoppedBM_of_density_of_continuousOn (hD m) (hdens m) (h𝓐 m) (h𝓑 m) (stoppedSigma_le hτ') (hNc m) hN0
      hNa (hS m) (hX m) (hC m) (hfib m)
  obtain ⟨N', hN'c, hN'0, hN'a, hN'bm, hN'eq⟩ :=
    exists_continuous_noise_of_isStoppedBM hS₀ hNa₀ hNc hN0 hbm hβ hβc hβ0
  refine ⟨𝓗, VL', VR', N', S, ?_, ?_, fun i => ?_, fun i => ?_, hVLm, hVRm, hN'c, hN'0, hN'a,
    fun m t => h𝓖 t _ (hS m t), hN'bm, ?_⟩
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
  · filter_upwards [hae, hpath, hN'eq] with z hz hp heq hlive
    obtain ⟨e1, e2⟩ := hagree z hz
    have e2' : (fun t => cImgDrvM (fun t (z : X × Y) => live t z.2) xj (fun t (z : X × Y) => Wj t z.1)
        (fun z : X × Y => ζj z.1) xk (fun t (z : X × Y) => Wk t z.2) τ t z) =
        fun t => rDrv live xj Wj ζj xk Wk τ' t z := funext e2
    rw [hz] at hlive
    rw [e1, e2', hz]
    obtain ⟨hcov, hpz⟩ := hp hlive
    refine ⟨hcov, IsSLEPathUpTo.congr_noise hpz fun t ht => ?_⟩
    obtain ⟨m, hm⟩ := hcov t ht
    exact heq m t hm

end Rect

/-! ### The mirror: conditioning curve on `X` -/

section DensityFst

variable {X Y : Type*} {𝓐 𝓔 : MeasurableSpace X} {𝓑 : MeasurableSpace Y} [mX : MeasurableSpace X]
  [mY : MeasurableSpace Y]

/-- **`isStoppedBM_of_density_fst` for a noise continuous before the cap only.** -/
theorem isStoppedBM_of_density_fst_of_continuousOn {P₁ : Measure X} {P₂ : Measure Y} [SFinite P₁] [SFinite P₂]
    {μ : Measure (X × Y)} [IsFiniteMeasure μ] {D : X × Y → ℝ≥0∞} (hD : Measurable D)
    (hdens : ∀ f : X × Y → ℝ≥0∞, Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] f →
      ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D z ∂(P₁.prod P₂))
    (h𝓐 : 𝓐 ≤ mX) (h𝓑 : 𝓑 ≤ mY) (h𝓔 : 𝓔 ≤ mX)
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (X × Y))} {N : ℝ≥0 → X × Y → ℝ} {S : X × Y → ℝ≥0}
    (hNc : ∀ z, ContinuousOn (N · z) (Icc 0 (S z))) (hN0 : ∀ z, N 0 z = 0) (hNa : ∀ t, Measurable[𝓖 t] (N t))
    (hS : IsStoppingTime 𝓖 fun z => (S z : WithTop ℝ≥0))
    (hX : ∀ (a : ℝ) (t : ℝ≥0), Measurable[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (stopExp a N S t))
    (hC : ∀ (s : ℝ≥0) (B : Set X) (A : Set (X × Y)), MeasurableSet[𝓔] B → MeasurableSet[𝓖 s] A →
      MeasurableSet[@Prod.instMeasurableSpace X Y 𝓐 𝓑] (Prod.fst ⁻¹' B ∩ A ∩ {z | s < S z}))
    (hfib : ∀ᵐ x ∂P₁, ∀ (a : ℝ) (s t : ℝ≥0), s ≤ t → ∀ A : Set (X × Y), MeasurableSet[𝓖 s] A →
      ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S t z)) (x, y) * D (x, y) ∂P₂ =
        ∫⁻ y, A.indicator (fun z => ENNReal.ofReal (stopExp a N S s z)) (x, y) * D (x, y) ∂P₂) :
    IsStoppedBM μ (supFiltration (𝓔.comap Prod.fst) (comap_fst_le h𝓔) 𝓖) N S := by
  have e : ∀ a, stopExp a (stoppedAt N S) S = stopExp a N S := fun a => stopExp_stoppedAt a S
  have h := isStoppedBM_of_density_fst (N := stoppedAt N S) hD hdens h𝓐 h𝓑 h𝓔 (continuous_stoppedAt hNc)
    (fun z => by simp only [stoppedAt, zero_min, hN0]) (measurable_stopped_of_continuousOn hNa hS hNc) hS
    (fun a t => by rw [e]; exact hX a t) hC (by simp only [e]; exact hfib)
  intro a
  rw [← e]
  exact h a

end DensityFst

section RectFst

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y]

/-- **The mirror of `IsRectImageCoreC`** (A1CORE's `IsRectImageCoreFst` with the noise continuous before each cap
only). -/
def IsRectImageCoreFstC (a : ℝ) {nL nR : ℕ} (P₁ : Measure X) (P₂ : Measure Y) (μ : Measure (X × Y))
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
      (∀ m z, ContinuousOn (N · z) (Icc 0 (S m z))) ∧ (∀ z, N 0 z = 0) ∧ (∀ t, Measurable[𝓖 t] (N t)) ∧
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

variable {a : ℝ} {nL nR : ℕ} {P₁ : Measure X} {P₂ : Measure Y} {μ : Measure (X × Y)} {𝓕k : Filtration ℝ≥0 mX}
  {live : ℝ≥0 → X → Prop} {xj : ℝ} {Wj : ℝ≥0 → Y → ℝ} {ζj : Y → ℝ≥0∞} {xk : ℝ} {Wk : ℝ≥0 → X → ℝ}
  {ΘL : ℝ≥0 → X → Fin nL → ℝ} {ΘR : ℝ≥0 → X → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The old mirror rectangle core implies the new one.** -/
theorem IsRectImageCoreFst.toC (h : IsRectImageCoreFst a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) :
    IsRectImageCoreFstC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR := by
  obtain ⟨h1, h2, h3, h4, h5, h⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun τ hτ => ?_⟩
  obtain ⟨𝓖, VL', VR', N, S, 𝓐, 𝓑, D, hW, hVL, hVR, hVLm, hVRm, hNc, hrest⟩ := h τ hτ
  exact ⟨𝓖, VL', VR', N, S, 𝓐, 𝓑, D, hW, hVL, hVR, hVLm, hVRm, fun _ z => (hNc z).continuousOn, hrest⟩

/-- **The mirror rectangle core with a noise continuous before the caps gives A1CANON's rectangle core**
(`isCanonImageCore_of_rect_fst` for `IsRectImageCoreFstC`). -/
theorem isCanonImageCore_of_rectC_fst [SFinite P₂] [IsProbabilityMeasure μ] (hμ : μ.map Prod.fst = P₁)
    (h : IsRectImageCoreFstC a P₁ P₂ μ 𝓕k live xj Wj ζj xk Wk ΘL ΘR ρL ρR) {Ω₀ : Type*} [m₀ : MeasurableSpace Ω₀]
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓦 : Filtration ℝ≥0 m₀} {β : ℝ≥0 → Ω₀ → ℝ}
    (hβ : IsFilteredBrownianReal 𝓦 β P₀) (hβc : ∀ w, Continuous (β · w)) (hβ0 : ∀ w, β 0 w = 0) :
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
  have hS₀ : ∀ m, IsStoppingTime 𝓗₀ fun z => (S m z : WithTop ℝ≥0) := fun m t =>
    le_supFiltration _ 𝓖 t _ (hS m t)
  have hNa₀ : ∀ t, Measurable[𝓗₀ t] (N t) := fun t => (hNa t).mono (le_supFiltration _ 𝓖 t) le_rfl
  have hbm : ∀ m, IsStoppedBM μ 𝓗₀ N (S m) := fun m =>
    isStoppedBM_of_density_fst_of_continuousOn (hD m) (hdens m) (h𝓐 m) (h𝓑 m) (stoppedSigma_le hτ') (hNc m)
      hN0 hNa (hS m) (hX m) (hC m) (hfib m)
  obtain ⟨N', hN'c, hN'0, hN'a, hN'bm, hN'eq⟩ :=
    exists_continuous_noise_of_isStoppedBM hS₀ hNa₀ hNc hN0 hbm hβ hβc hβ0
  refine ⟨𝓗, VL', VR', N', S, ?_, ?_, fun i => ?_, fun i => ?_, hVLm, hVRm, hN'c, hN'0, hN'a,
    fun m t => h𝓖 t _ (hS m t), hN'bm, ?_⟩
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
  · filter_upwards [hae, hpath, hN'eq] with z hz hp heq hlive
    obtain ⟨e1, e2⟩ := hagree z hz
    have e2' : (fun t => cImgDrvM (fun t (z : X × Y) => live t z.1) xj (fun t (z : X × Y) => Wj t z.2)
        (fun z : X × Y => ζj z.2) xk (fun t (z : X × Y) => Wk t z.1) τ t z) =
        fun t => rDrvFst live xj Wj ζj xk Wk τ' t z := funext e2
    rw [hz] at hlive
    rw [e1, e2', hz]
    obtain ⟨hcov, hpz⟩ := hp hlive
    refine ⟨hcov, IsSLEPathUpTo.congr_noise hpz fun t ht => ?_⟩
    obtain ⟨m, hm⟩ := hcov t ht
    exact heq m t hm

end RectFst

end InteractingSLE.ZhanGT4.A1RectLaw
