/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1FrozenFamily
import InteractingSLE.Spec.ZhanGT4.DualSeedLawEvolution
import InteractingSLE.Spec.ZhanGT4.DualTimeChangeBM

/-!
# A.1's frozen-curve image law, IV: the image noise, the per-cap paths, and the frozen-sample transfer

Packet PROVE-A1-FROZEN (R76). Source: Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L341–L353, R38):
the mapped driver satisfies (D10) under the tilted law, and "the time change `du = A²_{j,1} dt_j`, Lévy's
characterization, and uniqueness in law of the integrated force system identify the claimed conditional image law";
follow-up 4 §2.5 (R71: seeds). Tools for the inputs of `FrozenRectInput` / `FamilyRect`:

* **`noise_eq_seedCapacityNoise`**: the image noise is pinned — in a local `SLE_a(ρ)` path the noise is the
  compensated residual `(W − Σ∫ρ/(W − V))/√a` (A22's `seedCapacityNoise`) before the lifetime;
* **`ae_path_of_geometry`**: the per-cap path clause from the deterministic image equations of the image data stopped
  at the cap (`SeedImageGeometry`, A22) and the noise equal to the residual before the cap;
* **`ae_of_dens`**, **`ae_of_dens_fst`**: an event of the two stopped records that holds, for almost every frozen
  conditioning sample, almost surely under the frozen tilted law, holds almost surely under the coupling ((1.7) and
  Tonelli) — the transfer of frozen-sample statements to the coupling;
* **`isFrozenSampleLaw_of_seedCapacityBrownian`**, **`isFrozenSampleLawFst_of_seedCapacityBrownian`**: the seeded
  frozen-hull output form of A22 (`SeedCapacityBrownian`: a Brownian motion of a filtration `𝓗` equal to the residual
  of the image data up to the cap, `exists_SeedCapacityBrownian_actual_coordinates`) gives the frozen-sample law, once
  `𝓗` sees the image data before the cap and the image noise is the residual up to the cap;
  `measurable_timeChangeFilt_of_progressive`: own-time progressive data read at the inverse capacity clock are adapted
  to A22's time-changed filtration (how the generator clauses are checked for the seeded image data).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Frozen

open A1Canon A1Ref A1Core

/-! ### The image noise and the per-cap paths -/

section Noise

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The noise of a local path is the compensated residual** before the horizon (`0 < a`). -/
theorem noise_eq_seedCapacityNoise (ha : 0 < a) {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) : b t = seedCapacityNoise a ρL ρR w vL vR t := by
  have hs : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  unfold seedCapacityNoise
  rw [h.w_eq ht, eq_div_iff hs]
  ring

/-- **The per-cap path clause from the deterministic image equations**: almost surely on the live event, if the
image data stopped at the cap `S m` satisfy `SeedImageGeometry` up to the cap and the noise is the compensated
residual before the cap, the image is a local `SLE_a(ρ)` path before the cap capped by the lifetime. -/
theorem ae_path_of_geometry {Z : Type*} [MeasurableSpace Z] {μ : Measure Z} (ha : 0 < a) {live : Z → Prop}
    {ΘL : Z → Fin nL → ℝ} {ΘR : Z → Fin nR → ℝ} {W : ℝ≥0 → Z → ℝ} {ζ : Z → ℝ≥0∞}
    {VL : Fin nL → ℝ≥0 → Z → ℝ} {VR : Fin nR → ℝ≥0 → Z → ℝ} {N : ℝ≥0 → Z → ℝ} {S : ℕ → Z → ℝ≥0} (m : ℕ)
    (hg : ∀ᵐ z ∂μ, live z → SeedImageGeometry (ΘL z) (ΘR z) ρL ρR (fun t => W (min t (S m z)) z)
      (fun i t => VL i (min t (S m z)) z) (fun j t => VR j (min t (S m z)) z) (S m z))
    (hN : ∀ᵐ z ∂μ, live z → ∀ t : ℝ≥0, t < S m z →
      N t z = seedCapacityNoise a ρL ρR (W · z) (fun i t => VL i t z) (fun j t => VR j t z) t) :
    ∀ᵐ z ∂μ, live z → Sec2.IsSLEPathUpTo a (ΘL z) (ΘR z) ρL ρR (W · z) (fun i t => VL i t z)
      (fun j t => VR j t z) (N · z) (min (S m z : ℝ≥0∞) (ζ z)) := by
  filter_upwards [hg, hN] with z hgz hNz hlive
  exact (isSLEPathUpTo_of_geometry ha (hgz hlive) (hNz hlive)).mono (min_le_left _ _)

end Noise

/-! ### From frozen samples to the coupling -/

section Transfer

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {P₁ : Measure X} {P₂ : Measure Y}
  {μ : Measure (X × Y)} {𝓐 : ℕ → MeasurableSpace X} {𝓑 : ℕ → MeasurableSpace Y} {D : ℕ → X × Y → ℝ≥0∞} {m : ℕ}

/-- **Frozen-sample almost sure events are coupling almost sure** (fibres over the conditioning sample `y`): by
(1.7) and Tonelli, `μ(Gᶜ) = ∫ ∫ 1_{Gᶜ}(x, y) D(x, y) dP₁(x) dP₂(y) = 0`. -/
theorem ae_of_dens [SFinite P₁] [SFinite P₂] (hA : 𝓐 m ≤ mX) (hB : 𝓑 m ≤ mY) (hD : Measurable (D m))
    (hdens : ∀ f : X × Y → ℝ≥0∞, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
      ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D m z ∂(P₁.prod P₂))
    {G : Set (X × Y)} (hG : MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] G)
    (h : ∀ᵐ y ∂P₂, ∀ᵐ x ∂(P₁.withDensity fun x => D m (x, y)), (x, y) ∈ G) : ∀ᵐ z ∂μ, z ∈ G := by
  have hle : @Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m) ≤ @Prod.instMeasurableSpace X Y mX mY :=
    sup_le_sup (MeasurableSpace.comap_mono hA) (MeasurableSpace.comap_mono hB)
  have hGc : MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] Gᶜ := hG.compl
  have hf : Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Gᶜ.indicator (1 : X × Y → ℝ≥0∞)) :=
    measurable_const.indicator hGc
  have hf' : Measurable (Gᶜ.indicator (1 : X × Y → ℝ≥0∞)) := hf.mono hle le_rfl
  rw [ae_iff]
  change μ Gᶜ = 0
  rw [← lintegral_indicator_one (hle _ hGc), hdens _ hf,
    lintegral_prod_symm (fun z => Gᶜ.indicator (1 : X × Y → ℝ≥0∞) z * D m z) (hf'.mul hD).aemeasurable]
  refine (lintegral_congr_ae ?_).trans (lintegral_zero (μ := P₂))
  filter_upwards [h] with y hy
  have hDy : Measurable fun x => D m (x, y) := hD.comp measurable_prodMk_right
  have hgy : Measurable fun x => Gᶜ.indicator (1 : X × Y → ℝ≥0∞) (x, y) := hf'.comp measurable_prodMk_right
  calc ∫⁻ x, Gᶜ.indicator 1 (x, y) * D m (x, y) ∂P₁
      = ∫⁻ x, ((fun x => D m (x, y)) * fun x => Gᶜ.indicator (1 : X × Y → ℝ≥0∞) (x, y)) x ∂P₁ := by
        refine lintegral_congr fun x => ?_
        simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ x, Gᶜ.indicator (1 : X × Y → ℝ≥0∞) (x, y) ∂(P₁.withDensity fun x => D m (x, y)) :=
        (lintegral_withDensity_eq_lintegral_mul P₁ hDy hgy).symm
    _ = ∫⁻ _, 0 ∂(P₁.withDensity fun x => D m (x, y)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hy] with x hx
        simp only [indicator_of_notMem (show (x, y) ∉ Gᶜ from not_not.2 hx)]
    _ = 0 := lintegral_zero

/-- **Frozen-sample almost sure events are coupling almost sure** (fibres over the conditioning sample `x`). -/
theorem ae_of_dens_fst [SFinite P₁] [SFinite P₂] (hA : 𝓐 m ≤ mX) (hB : 𝓑 m ≤ mY) (hD : Measurable (D m))
    (hdens : ∀ f : X × Y → ℝ≥0∞, Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] f →
      ∫⁻ z, f z ∂μ = ∫⁻ z, f z * D m z ∂(P₁.prod P₂))
    {G : Set (X × Y)} (hG : MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] G)
    (h : ∀ᵐ x ∂P₁, ∀ᵐ y ∂(P₂.withDensity fun y => D m (x, y)), (x, y) ∈ G) : ∀ᵐ z ∂μ, z ∈ G := by
  have hle : @Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m) ≤ @Prod.instMeasurableSpace X Y mX mY :=
    sup_le_sup (MeasurableSpace.comap_mono hA) (MeasurableSpace.comap_mono hB)
  have hGc : MeasurableSet[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] Gᶜ := hG.compl
  have hf : Measurable[@Prod.instMeasurableSpace X Y (𝓐 m) (𝓑 m)] (Gᶜ.indicator (1 : X × Y → ℝ≥0∞)) :=
    measurable_const.indicator hGc
  have hf' : Measurable (Gᶜ.indicator (1 : X × Y → ℝ≥0∞)) := hf.mono hle le_rfl
  rw [ae_iff]
  change μ Gᶜ = 0
  rw [← lintegral_indicator_one (hle _ hGc), hdens _ hf,
    lintegral_prod (fun z => Gᶜ.indicator (1 : X × Y → ℝ≥0∞) z * D m z) (hf'.mul hD).aemeasurable]
  refine (lintegral_congr_ae ?_).trans (lintegral_zero (μ := P₁))
  filter_upwards [h] with x hx
  have hDx : Measurable fun y => D m (x, y) := hD.comp measurable_prodMk_left
  have hgx : Measurable fun y => Gᶜ.indicator (1 : X × Y → ℝ≥0∞) (x, y) := hf'.comp measurable_prodMk_left
  calc ∫⁻ y, Gᶜ.indicator 1 (x, y) * D m (x, y) ∂P₂
      = ∫⁻ y, ((fun y => D m (x, y)) * fun y => Gᶜ.indicator (1 : X × Y → ℝ≥0∞) (x, y)) y ∂P₂ := by
        refine lintegral_congr fun y => ?_
        simp only [Pi.mul_apply, mul_comm]
    _ = ∫⁻ y, Gᶜ.indicator (1 : X × Y → ℝ≥0∞) (x, y) ∂(P₂.withDensity fun y => D m (x, y)) :=
        (lintegral_withDensity_eq_lintegral_mul P₂ hDx hgx).symm
    _ = ∫⁻ _, 0 ∂(P₂.withDensity fun y => D m (x, y)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hx] with y hy
        simp only [indicator_of_notMem (show (x, y) ∉ Gᶜ from not_not.2 hy)]
    _ = 0 := lintegral_zero

end Transfer

/-! ### The seeded frozen-hull output -/

section Seeded

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {nL nR : ℕ} {a : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → X × Y → ℝ} {ζ : X × Y → ℝ≥0∞}
  {VL : Fin nL → ℝ≥0 → X × Y → ℝ} {VR : Fin nR → ℝ≥0 → X × Y → ℝ} {N : ℝ≥0 → X × Y → ℝ}
  {S : ℕ → X × Y → ℝ≥0} {m : ℕ}

omit mY in
/-- **The seeded frozen-hull output gives the frozen-sample law** (conditioning sample `y`): a capacity Brownian
motion of `𝓗` under `Q` equal to the residual of the image data at `y` up to the cap (A22's `SeedCapacityBrownian`),
a filtration `𝓗` that sees the cap event and, before the cap, the image data at `y`, and the image noise equal to the
residual up to the cap. -/
theorem isFrozenSampleLaw_of_seedCapacityBrownian {y : Y} {Q : Measure X} {𝓗 : Filtration ℝ≥0 mX}
    {Bh : ℝ≥0 → X → ℝ}
    (hB : SeedCapacityBrownian a ρL ρR Q 𝓗 (fun t x => W t (x, y)) (fun i t x => VL i t (x, y))
      (fun j t x => VR j t (x, y)) (fun x => S m (x, y)) Bh)
    (hBc : ∀ x, Continuous (Bh · x)) (hC : ∀ s : ℝ≥0, MeasurableSet[𝓗 s] {x | s < S m (x, y)})
    (hG : ∀ s : ℝ≥0, ∀ g ∈ imageGen W ζ VL VR N S s,
      MeasurableSet[𝓗 s] ((fun x => (x, y)) ⁻¹' g ∩ {x | s < S m (x, y)}))
    (hN : ∀ x t, t ≤ S m (x, y) → N t (x, y) = seedCapacityNoise a ρL ρR (fun t => W t (x, y))
      (fun i t => VL i t (x, y)) (fun j t => VR j t (x, y)) t) :
    IsFrozenSampleLaw Q W ζ VL VR N S m y :=
  ⟨𝓗, Bh, hB.1, hBc, hC, hG, ae_of_all _ fun x t ht => by rw [hB.2 x t ht, hN x t ht]⟩

omit mX in
/-- **The seeded frozen-hull output gives the frozen-sample law** (conditioning sample `x`, mirror). -/
theorem isFrozenSampleLawFst_of_seedCapacityBrownian {x : X} {Q : Measure Y} {𝓗 : Filtration ℝ≥0 mY}
    {Bh : ℝ≥0 → Y → ℝ}
    (hB : SeedCapacityBrownian a ρL ρR Q 𝓗 (fun t y => W t (x, y)) (fun i t y => VL i t (x, y))
      (fun j t y => VR j t (x, y)) (fun y => S m (x, y)) Bh)
    (hBc : ∀ y, Continuous (Bh · y)) (hC : ∀ s : ℝ≥0, MeasurableSet[𝓗 s] {y | s < S m (x, y)})
    (hG : ∀ s : ℝ≥0, ∀ g ∈ imageGen W ζ VL VR N S s,
      MeasurableSet[𝓗 s] ((fun y => (x, y)) ⁻¹' g ∩ {y | s < S m (x, y)}))
    (hN : ∀ y t, t ≤ S m (x, y) → N t (x, y) = seedCapacityNoise a ρL ρR (fun t => W t (x, y))
      (fun i t => VL i t (x, y)) (fun j t => VR j t (x, y)) t) :
    IsFrozenSampleLawFst Q W ζ VL VR N S m x :=
  ⟨𝓗, Bh, hB.1, hBc, hC, hG, ae_of_all _ fun y t ht => by rw [hB.2 y t ht, hN y t ht]⟩

omit mY in
/-- **Own-time progressive data read at the inverse capacity clock are adapted to the time-changed filtration** (the
filtration `Zhan.Retarget.timeChangeFilt` of A22's capacity Brownian motion, `isFilteredBrownianReal_timeChange`):
the form in which the generator clauses of the frozen-sample law are checked for the seeded image data. -/
theorem measurable_timeChangeFilt_of_progressive {𝓕 : Filtration ℝ≥0 mX} {C : X → ℝ≥0 → ℝ}
    (hCc : ∀ x, Continuous (C x)) (hCm : ∀ x, Monotone (C x)) (hmeas : ∀ r : ℝ≥0, Measurable[𝓕 r] fun x => C x r)
    {Z : ℝ≥0 → X → ℝ} (hZ : IsStronglyProgressive 𝓕 Z) (u : ℝ≥0) :
    Measurable[Zhan.Retarget.timeChangeFilt 𝓕 (isStoppingTime_invClock hCc hCm hmeas) (invClock_mono hCc hCm) u]
      fun x => Z (invClockT C u x) x :=
  measurable_stoppedValue hZ (isStoppingTime_invClock hCc hCm hmeas u)

end Seeded

end InteractingSLE.ZhanGT4.A1Frozen
