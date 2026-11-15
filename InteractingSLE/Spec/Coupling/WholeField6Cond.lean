/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField6QLC
import InteractingSLE.Spec.Coupling.WholeField4Announce
import InteractingSLE.Spec.Sec7.TwoForceMain2Batch

/-!
# The pocket kernel at the birth and after it: conditional-expectation steps of C.4

Packet PROVE-WHOLEFIELD6 (follow-up note C.4, `ig1_followup_proofs.txt` L1651–1704; R39 Aux. 48–49,
`ig1_additional_proofs.txt` L3166–3200).

A pocket born at a driving stop `T` (announced by driving stops `ρₙ ↑ T`) is handled by three steps, assembled in
`ae_condExp_eq_of_birth`:

1. **at the announcing stops** the kernel identity `E[Z | 𝓕_{ρₙ}] = Φₙ` is known (frozen kernel, or an induction
   hypothesis on fewer pockets), eventually on the relevant event;
2. **at the birth**, Lévy's upward theorem along `𝓕_{ρₙ}` and quasi-left continuity
   (`stopping_le_iSup_of_tendsto`) give `E[Z | 𝓕_T] = lim E[Z | 𝓕_{ρₙ}] = lim Φₙ`;
3. **after the birth**, a germ observable is frozen ((WF7a), `condExp_histGerm_eq_complex`): for `T ≤ σ`,
   `E[Z | 𝓕_σ] = E[Z | 𝓕_T]` on the event where `Z` is an observable of the germ at `T`.

The active field at a later time is added by `ae_condExp_mul_eq_on` (pull-out of a kernel known on an event).

## Main results

* `ae_condExp_stopping_eq_of_le`: on `{T ≤ σ}`, `E[Y | 𝓕_σ] = Y` for `𝓕_T`-measurable `Y`;
* `ae_condExp_mul_eq_on`: if `E[X | 𝒢'] = g` on `F ∈ 𝒢` with `g` `𝒢`-measurable, then `E[Y X | 𝒢] = g E[Y | 𝒢]` on `F`
  for bounded `𝒢'`-measurable `Y`;
* `ae_tendsto_condExp_of_announce`: Lévy's upward theorem along an announcing sequence of driving stops;
* **`ae_condExp_eq_of_birth`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

/-! ### Abstract steps -/

section Abstract

variable {Ω : Type*} {𝒢 𝒢' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsFiniteMeasure P]

/-- **On `{T ≤ σ}` an `𝓕_T`-measurable function is its own conditional expectation given `𝓕_σ`.** -/
theorem ae_condExp_stopping_eq_of_le {𝓖 : Filtration ℝ≥0 mΩ} {T σ : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime 𝓖 T) (hσ : IsStoppingTime 𝓖 σ) {Y : Ω → ℂ}
    (hY : StronglyMeasurable[hT.measurableSpace] Y) (hYi : Integrable Y P) :
    ∀ᵐ ω ∂P, T ω ≤ σ ω → P[Y | hσ.measurableSpace] ω = Y ω := by
  set s : Set Ω := {ω | T ω ≤ σ ω} with hs
  have hsT : MeasurableSet[hT.measurableSpace] s := hT.measurableSet_le_stopping_time hσ
  have hsσ : MeasurableSet[hσ.measurableSpace] s := hT.measurableSet_stopping_time_le hσ
  have hsmin : MeasurableSet[(hT.min hσ).measurableSpace] s := by
    rw [hT.measurableSpace_min hσ]; exact ⟨hsT, hsσ⟩
  have hmin_le : (hT.min hσ).measurableSpace ≤ hσ.measurableSpace :=
    IsStoppingTime.measurableSpace_mono (hT.min hσ) hσ fun ω => min_le_right _ _
  -- `E[Y | 𝓕_{T ∧ σ}] = Y` on `s`
  have h1 := condExp_min_stopping_time_ae_eq_restrict_le (μ := P) (f := Y) hT hσ
  rw [condExp_of_stronglyMeasurable hT.measurableSpace_le hY hYi] at h1
  -- `1_s Y` is a.e. `𝓕_σ`-measurable
  have hind : s.indicator Y =ᵐ[P] s.indicator (P[Y | (hT.min hσ).measurableSpace]) := by
    have h1' := (ae_restrict_iff' (hT.measurableSpace_le _ hsT)).1 h1
    filter_upwards [h1'] with ω hω
    by_cases h : ω ∈ s
    · rw [indicator_of_mem h, indicator_of_mem h, hω h]
    · rw [indicator_of_notMem h, indicator_of_notMem h]
  have hsm : AEStronglyMeasurable[hσ.measurableSpace] (s.indicator Y) P :=
    ⟨_, ((stronglyMeasurable_condExp.mono hmin_le).indicator hsσ), hind⟩
  have h2 := condExp_of_aestronglyMeasurable' hσ.measurableSpace_le hsm (hYi.indicator
    (hσ.measurableSpace_le _ hsσ))
  have h3 := condExp_indicator (μ := P) hYi hsσ
  filter_upwards [h2, h3] with ω e2 e3 hω
  have := e3.symm.trans e2
  rwa [indicator_of_mem (show ω ∈ s from hω), indicator_of_mem (show ω ∈ s from hω)] at this

/-- **Pull-out of a kernel known on an event.** Let `𝒢 ≤ 𝒢' ≤ mΩ`, `Y` bounded and `𝒢'`-measurable, `X` bounded, and
`F ∈ 𝒢` an event on which `E[X | 𝒢'] = g` for a bounded `𝒢`-measurable `g`. Then `E[Y X | 𝒢] = g E[Y | 𝒢]` on `F`. -/
theorem ae_condExp_mul_eq_on (h𝒢 : 𝒢 ≤ 𝒢') (h𝒢' : 𝒢' ≤ mΩ) {Y X g : Ω → ℂ} {F : Set Ω}
    (hF : MeasurableSet[𝒢] F) (hY : StronglyMeasurable[𝒢'] Y) (hYb : ∀ ω, ‖Y ω‖ ≤ 1)
    (hX : AEStronglyMeasurable X P) (hXb : ∀ ω, ‖X ω‖ ≤ 1) (hg : StronglyMeasurable[𝒢] g)
    (hgb : ∀ ω, ‖g ω‖ ≤ 1) (hXg : ∀ᵐ ω ∂P, ω ∈ F → P[X | 𝒢'] ω = g ω) :
    ∀ᵐ ω ∂P, ω ∈ F → P[Y * X | 𝒢] ω = g ω * P[Y | 𝒢] ω := by
  have hFm : MeasurableSet F := h𝒢' _ (h𝒢 _ hF)
  have hYi : Integrable Y P :=
    Integrable.of_bound (hY.mono h𝒢').aestronglyMeasurable 1 (Eventually.of_forall hYb)
  have hXi : Integrable X P := Integrable.of_bound hX 1 (Eventually.of_forall hXb)
  have hgi : Integrable g P :=
    Integrable.of_bound ((hg.mono h𝒢).mono h𝒢').aestronglyMeasurable 1 (Eventually.of_forall hgb)
  have hYX : Integrable (Y * X) P := Integrable.of_bound
    ((hY.mono h𝒢').aestronglyMeasurable.mul hX) 1 (Eventually.of_forall fun ω => by
      rw [Pi.mul_apply, norm_mul]
      nlinarith [hYb ω, hXb ω, norm_nonneg (Y ω), norm_nonneg (X ω)])
  have hFY : Integrable (F.indicator Y) P := hYi.indicator hFm
  have hFYg : Integrable (F.indicator Y * g) P := Integrable.of_bound
    ((hYi.indicator hFm).aestronglyMeasurable.mul hgi.aestronglyMeasurable) 1
    (Eventually.of_forall fun ω => by
      rw [Pi.mul_apply, norm_mul]
      have : ‖F.indicator Y ω‖ ≤ 1 := by
        by_cases h : ω ∈ F
        · rw [indicator_of_mem h]; exact hYb ω
        · rw [indicator_of_notMem h, norm_zero]; exact zero_le_one
      nlinarith [hgb ω, norm_nonneg (F.indicator Y ω), norm_nonneg (g ω)])
  -- `E[Y X | 𝒢'] = Y E[X | 𝒢']`
  have hpull := Sec7.condExp_mul_of_aestronglyMeasurable_left_complex
    (hY.aestronglyMeasurable) hYX hXi (m := 𝒢')
  -- on `F`: `1_F E[Y X | 𝒢'] = 1_F Y g`
  have hloc : F.indicator (P[Y * X | 𝒢']) =ᵐ[P] F.indicator Y * g := by
    filter_upwards [hpull, hXg] with ω e1 e2
    by_cases h : ω ∈ F
    · rw [indicator_of_mem h, Pi.mul_apply, indicator_of_mem h, e1, Pi.mul_apply, e2 h]
    · rw [indicator_of_notMem h, Pi.mul_apply, indicator_of_notMem h, zero_mul]
  have h1 : P[F.indicator (Y * X) | 𝒢] =ᵐ[P] F.indicator (P[Y * X | 𝒢]) := condExp_indicator hYX hF
  have h2 : P[F.indicator (Y * X) | 𝒢] =ᵐ[P] P[F.indicator (P[Y * X | 𝒢']) | 𝒢] := by
    have e : F.indicator (P[Y * X | 𝒢']) =ᵐ[P] P[F.indicator (Y * X) | 𝒢'] :=
      (condExp_indicator hYX (h𝒢 _ hF)).symm
    refine (condExp_condExp_of_le h𝒢 h𝒢').symm.trans (condExp_congr_ae e.symm)
  have h3 : P[F.indicator (P[Y * X | 𝒢']) | 𝒢] =ᵐ[P] P[F.indicator Y * g | 𝒢] := condExp_congr_ae hloc
  have h4 : P[F.indicator Y * g | 𝒢] =ᵐ[P] P[F.indicator Y | 𝒢] * g :=
    Sec7.condExp_mul_of_aestronglyMeasurable_right_complex hg.aestronglyMeasurable hFYg hFY
  have h5 : P[F.indicator Y | 𝒢] =ᵐ[P] F.indicator (P[Y | 𝒢]) := condExp_indicator hYi hF
  filter_upwards [h1, h2, h3, h4, h5] with ω e1 e2 e3 e4 e5 hω
  have := e1.symm.trans (e2.trans (e3.trans e4))
  rw [indicator_of_mem hω, Pi.mul_apply, e5, indicator_of_mem hω] at this
  rw [this, mul_comm]

end Abstract

/-! ### Lévy's upward theorem along announcing stops, and the birth transfer -/

section Coupling

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

open LQGMetric QuantumZipper

/-- The stopping σ-algebras of a monotone sequence of driving stops, as a filtration indexed by `ℕ`. -/
def stopFiltration (hX : IsMeasurableKilledDriving W VL VR ζ) {ρ : ℕ → Ω → ℝ≥0}
    (hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0))
    (hρm : ∀ ω, Monotone fun n => ρ n ω) : Filtration ℕ mΩ where
  seq n := (hρ n).measurableSpace
  mono' _ _ hmn := IsStoppingTime.measurableSpace_mono (hρ _) (hρ _) fun ω =>
    WithTop.coe_le_coe.2 (hρm ω hmn)
  le' n := (hρ n).measurableSpace_le

/-- **Lévy's upward theorem along announcing stops.** For the frozen coupling, a driving stop `T < ζ` (positive, or
a separated word) and nondecreasing driving stops `ρₙ ≤ T` converging to `T`: `E[Z | 𝓕_{ρₙ}] → E[Z | 𝓕_T]` almost
surely, for every integrable complex `Z` (quasi-left continuity identifies `⋁ₙ 𝓕_{ρₙ}` with `𝓕_T`). -/
theorem ae_tendsto_condExp_of_announce (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω) (hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j)
    {ρ : ℕ → Ω → ℝ≥0} (hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0))
    (hρm : ∀ ω, Monotone fun n => ρ n ω) (hρT : ∀ n ω, ρ n ω ≤ T ω)
    (hρlim : ∀ᵐ ω ∂P, Tendsto (fun n => ρ n ω) atTop (𝓝 (T ω))) {Z : Ω → ℂ} (hZ : Integrable Z P) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (P[Z | (hρ n).measurableSpace]) ω) atTop
      (𝓝 ((P[Z | hT.measurableSpace]) ω)) := by
  have hsup : (⨆ n, stopFiltration hX hρ hρm n) = hT.measurableSpace :=
    le_antisymm (iSup_le fun n => IsStoppingTime.measurableSpace_mono (hρ n) hT fun ω =>
      WithTop.coe_le_coe.2 (hρT n ω))
      (stopping_le_iSup_of_tendsto hC hκ hu₀ hX hT hTζ hT0 hρ hρT hρlim)
  have := tendsto_ae_condExp_complex (P := P) (stopFiltration hX hρ hρm) hZ
  rw [hsup] at this
  exact this

/-- **The birth transfer** (C.3–C.4 with quasi-left continuity). Let `T < ζ` be a driving stop (positive, or a
separated word), announced by nondecreasing driving stops `ρₙ ≤ T`, `ρₙ → T`, and let `σ` be a driving stop. Let `Z`
be a bounded observable and `F ∈ 𝓕_T` an event on which `Z` is an observable of the germ at `T` (`1_F Z` is
`Γ(𝓕_T, K_T)`-measurable). Suppose that, on events `Eₙ`, `E[Z | 𝓕_{ρₙ}] = Φₙ`, and that on an event `E ⊆ F ∩ {T ≤ σ}`
eventually `ω ∈ Eₙ` and `Φₙ → Φ`. Then `E[Z | 𝓕_σ] = Φ` almost surely on `E`. -/
theorem ae_condExp_eq_of_birth (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T σ : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hσ : IsStoppingTime (drivingFiltration P hX) fun ω => (σ ω : WithTop ℝ≥0))
    (hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω) (hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j)
    {ρ : ℕ → Ω → ℝ≥0} (hρ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0))
    (hρm : ∀ ω, Monotone fun n => ρ n ω) (hρT : ∀ n ω, ρ n ω ≤ T ω)
    (hρlim : ∀ᵐ ω ∂P, Tendsto (fun n => ρ n ω) atTop (𝓝 (T ω)))
    {AT : Ω → Set ℂ} (hAT : Measurable[mΩ, hittingSigma] AT)
    (hATK : ∀ᵐ ω ∂P, AT ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (T ω : ℝ))
    {Z : Ω → ℂ} (hZm : AEStronglyMeasurable Z P) (hZb : ∀ ω, ‖Z ω‖ ≤ 1) {F : Set Ω}
    (hF : MeasurableSet[hT.measurableSpace] F)
    (hFZ : StronglyMeasurable[histGerm hT.measurableSpace AT (centredField h u₀)] (F.indicator Z))
    {E : Set Ω} {En : ℕ → Set Ω} {Φn : ℕ → Ω → ℂ} {Φ : Ω → ℂ}
    (h1 : ∀ n, ∀ᵐ ω ∂P, ω ∈ En n → (P[Z | (hρ n).measurableSpace]) ω = Φn n ω)
    (h2 : ∀ᵐ ω ∂P, ω ∈ E → ∀ᶠ n in atTop, ω ∈ En n)
    (h3 : ∀ᵐ ω ∂P, ω ∈ E → Tendsto (fun n => Φn n ω) atTop (𝓝 (Φ ω)))
    (h4 : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ F ∧ T ω ≤ σ ω) :
    ∀ᵐ ω ∂P, ω ∈ E → (P[Z | hσ.measurableSpace]) ω = Φ ω := by
  have hZi : Integrable Z P := Integrable.of_bound hZm 1 (Eventually.of_forall hZb)
  -- the birth: `E[Z | 𝓕_T] = Φ` on `E`
  have hlev := ae_tendsto_condExp_of_announce hC hκ hu₀ hX hT hTζ hT0 hρ hρm hρT hρlim hZi
  have hbirth : ∀ᵐ ω ∂P, ω ∈ E → (P[Z | hT.measurableSpace]) ω = Φ ω := by
    filter_upwards [hlev, ae_all_iff.2 h1, h2, h3] with ω hl e1 e2 e3 hω
    refine tendsto_nhds_unique hl ((e3 hω).congr' ?_)
    filter_upwards [e2 hω] with n hn
    exact (e1 n hn).symm
  -- the freeze after the birth, with `F' = F ∩ {T ≤ σ}`
  set s : Set Ω := {ω | (T ω : WithTop ℝ≥0) ≤ (σ ω : WithTop ℝ≥0)} with hs
  have hsT : MeasurableSet[hT.measurableSpace] s := hT.measurableSet_le_stopping_time hσ
  have hsσ : MeasurableSet[hσ.measurableSpace] s := hT.measurableSet_stopping_time_le hσ
  have hF'σ : MeasurableSet[hσ.measurableSpace] (F ∩ s) := by
    have := IsStoppingTime.measurableSet_inter_le hT hσ F hF
    exact IsStoppingTime.measurableSpace_mono (hT.min hσ) hσ (fun ω => min_le_right _ _) _ this
  have hF'T : MeasurableSet[hT.measurableSpace] (F ∩ s) := hF.inter hsT
  have hgle : histGerm hT.measurableSpace AT (centredField h u₀) ≤ mΩ :=
    histGerm_le hT.measurableSpace_le hAT (measurable_centredField hC.2.1 u₀)
  have hZ' : StronglyMeasurable[histGerm hT.measurableSpace AT (centredField h u₀)] ((F ∩ s).indicator Z) := by
    have e : (F ∩ s).indicator Z = s.indicator (F.indicator Z) := by
      rw [inter_comm, indicator_indicator]
    rw [e]
    exact hFZ.indicator (le_histGerm _ _ _ hsT)
  have hZ'b : ∀ᵐ ω ∂P, ‖(F ∩ s).indicator Z ω‖ ≤ 1 := Eventually.of_forall fun ω => by
    by_cases h' : ω ∈ F ∩ s
    · rw [indicator_of_mem h']; exact hZb ω
    · rw [indicator_of_notMem h', norm_zero]; exact zero_le_one
  have hmax := hT.max hσ
  have hTmax : hT.measurableSpace ≤ hmax.measurableSpace :=
    IsStoppingTime.measurableSpace_mono hT hmax fun ω => le_max_left _ _
  have hσmax : hσ.measurableSpace ≤ hmax.measurableSpace :=
    IsStoppingTime.measurableSpace_mono hσ hmax fun ω => le_max_right _ _
  have hfreeze := condExp_histGerm_eq_complex hC hκ hu₀ hX hT hTζ hT0 hAT hATK hZ' (c := 1) hZ'b hTmax
    (stopping_le_iSup_driving hX hmax)
  have hZ'i : Integrable ((F ∩ s).indicator Z) P := hZi.indicator (hT.measurableSpace_le _ hF'T)
  -- `E[1_{F'} Z | 𝓕_σ] = E[1_{F'} Z | 𝓕_T]` on `s`
  have htower : P[(F ∩ s).indicator Z | hσ.measurableSpace] =ᵐ[P]
      P[P[(F ∩ s).indicator Z | hT.measurableSpace] | hσ.measurableSpace] :=
    (condExp_condExp_of_le hσmax hmax.measurableSpace_le).symm.trans (condExp_congr_ae hfreeze)
  have hstop := ae_condExp_stopping_eq_of_le (P := P) hT hσ
    (stronglyMeasurable_condExp (m := hT.measurableSpace) (μ := P) (f := (F ∩ s).indicator Z))
    integrable_condExp
  have hindσ := condExp_indicator (μ := P) hZi hF'σ
  have hindT := condExp_indicator (μ := P) hZi hF'T
  filter_upwards [hbirth, htower, hstop, hindσ, hindT, h4] with ω eb et es eσ eT e4 hω
  obtain ⟨hωF, hωs⟩ := e4 hω
  have hωs' : ω ∈ s := WithTop.coe_le_coe.2 hωs
  have hmem : ω ∈ F ∩ s := ⟨hωF, hωs'⟩
  have := eσ.symm.trans (et.trans ((es hωs').trans eT))
  rw [indicator_of_mem hmem, indicator_of_mem hmem] at this
  rw [this, eb hω]

end Coupling

end WholeField

end InteractingSLE
