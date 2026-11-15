/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RLawFam
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkRecord

/-!
# Zhan's A.1 under R83: the compensated residual as the image noise

Packet PROVE-A1-RECTLAW2 (R83). The image noise of the C families is the compensated residual of the image driving
equation, `seedCapacityNoise a ρL ρR W VL VR` (A22): it is determined by the image data on `[0, t]`, so it is local in
the two stopped records, and it is continuous before each cap as soon as the image data have the deterministic
geometry (`SeedImageGeometry`) up to the cap. This file supplies the generic facts:

* `SeedImageGeometry.continuousOn_unstop`, `…integrable_unstop`, …: the geometry of data stopped at `T` gives the
  regularity of the unstopped data on `[0, T]`;
* **`continuousOn_residual_of_geometry`**: the residual is continuous on `[0, T]`;
* **`exists_measurable_residual_of_geometry`**: the residual at `r` has a measurable version on the samples where some
  positive cap is `≥ r` (a singular entrance at `0` is allowed; MULTIMARK's Riemann-sum construction);
* **`exists_residualNoise`**: a jointly measurable noise indexed by the frozen time, `0` at time `0`, continuous on
  every cap interval at every sample, and equal to the residual on every cap interval (the family's `N`);
* **`IsSeedSampleLaw.congr_noise`**: the one-sample law only reads the noise up to the cap;
* **`measurable_stopped_of_before_of_continuousOn`**: MULTIMARK's `measurable_stopped_of_before` (`hNs`) for a noise
  continuous on the cap interval only.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RLaw

open A1Canon A1Ref A1Core A1Frozen A1Family A1MultiMark A1RectLaw

/-! ### The geometry of stopped data gives the regularity of the unstopped data -/

section Unstop

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0}

theorem min_toNNReal_eq {r T : ℝ≥0} (hr : r ≤ T) {s : ℝ} (hs : s ≤ r) : min s.toNNReal T = s.toNNReal :=
  min_eq_left ((Real.toNNReal_le_iff_le_coe.2 hs).trans hr)

theorem continuousOn_unstop {f : ℝ≥0 → ℝ} (hf : Continuous fun t => f (min t T)) :
    ContinuousOn f (Icc 0 T) :=
  hf.continuousOn.congr fun t ht => by simp only [min_eq_left ht.2]

theorem continuousOn_unstop_real {f : ℝ≥0 → ℝ} (hf : Continuous fun t => f (min t T)) {r : ℝ≥0} (hr : r ≤ T) :
    ContinuousOn (fun s : ℝ => f s.toNNReal) (Icc 0 r) :=
  ((hf.comp continuous_real_toNNReal).continuousOn).congr fun s hs => by
    simp only [Function.comp_apply, min_toNNReal_eq hr hs.2]

theorem intervalIntegrable_unstop {g : ℝ≥0 → ℝ} {r : ℝ≥0} (hr : r ≤ T)
    (hi : IntervalIntegrable (fun s : ℝ => g (min s.toNNReal T)) volume 0 r) :
    IntervalIntegrable (fun s : ℝ => g s.toNNReal) volume 0 r :=
  hi.congr fun s hs => by
    rw [uIoc_of_le r.coe_nonneg] at hs
    simp only [min_toNNReal_eq hr hs.2]

/-- The left gaps of data stopped at `T` with geometry up to `T`, unstopped on `(0, r]`, `r ≤ T`. -/
theorem left_ne_unstop
    (h : SeedImageGeometry xL xR ρL ρR (fun t => w (min t T)) (fun i t => vL i (min t T))
      (fun j t => vR j (min t T)) T) {r : ℝ≥0} (hr : r ≤ T) (i : Fin nL) :
    ∀ s ∈ Ioc (0 : ℝ) r, w s.toNNReal ≠ vL i s.toNNReal := fun s hs => by
  have h' := h.left_lt s.toNNReal (Real.toNNReal_pos.2 hs.1) ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans hr) i
  simp only [min_toNNReal_eq hr hs.2] at h'
  exact h'.ne'

/-- The right gaps, mirror of `SeedImageGeometry.left_ne_unstop`. -/
theorem right_ne_unstop
    (h : SeedImageGeometry xL xR ρL ρR (fun t => w (min t T)) (fun i t => vL i (min t T))
      (fun j t => vR j (min t T)) T) {r : ℝ≥0} (hr : r ≤ T) (j : Fin nR) :
    ∀ s ∈ Ioc (0 : ℝ) r, w s.toNNReal ≠ vR j s.toNNReal := fun s hs => by
  have h' := h.right_gt s.toNNReal (Real.toNNReal_pos.2 hs.1) ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans hr) j
  simp only [min_toNNReal_eq hr hs.2] at h'
  exact h'.ne

/-- **The residual is continuous on `[0, T]`** for data stopped at `T` with the geometry up to `T`. -/
theorem continuousOn_residual_of_geometry (a : ℝ)
    (h : SeedImageGeometry xL xR ρL ρR (fun t => w (min t T)) (fun i t => vL i (min t T))
      (fun j t => vR j (min t T)) T) :
    ContinuousOn (seedCapacityNoise a ρL ρR w vL vR) (Icc 0 T) := by
  refine continuousOn_seedCapacityNoise (continuousOn_unstop h.continuous_w) (fun i => ?_) (fun j => ?_)
  · simpa only [div_eq_mul_inv] using
      (intervalIntegrable_unstop (g := fun t => (w t - vL i t)⁻¹) le_rfl (h.integrable_left T le_rfl i)).const_mul
        (ρL i)
  · simpa only [div_eq_mul_inv] using
      (intervalIntegrable_unstop (g := fun t => (w t - vR j t)⁻¹) le_rfl (h.integrable_right T le_rfl j)).const_mul
        (ρR j)

/-- The residual at time `0` is the driver at `0` (scaled). -/
theorem seedCapacityNoise_zero (a : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) :
    seedCapacityNoise a ρL ρR w vL vR 0 = w 0 / Real.sqrt a := by
  simp only [seedCapacityNoise, NNReal.coe_zero, intervalIntegral.integral_same, Finset.sum_const_zero, sub_zero]

end Unstop

/-! ### Measurable versions of the residual -/

section Generic

variable {Z : Type*} [𝓜 : MeasurableSpace Z] {nL nR : ℕ}

/-- **The residual at `r` has a measurable version on the samples covered by a positive cap** (`r ≤ S m z`,
`0 < S m z` for some `m`), when the image data are measurable at each time and have the geometry up to every positive
cap. -/
theorem exists_measurable_residual_of_geometry (a : ℝ) {xL : Z → Fin nL → ℝ} {xR : Z → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {S : ℕ → Z → ℝ≥0} {W : ℝ≥0 → Z → ℝ} {VL : Fin nL → ℝ≥0 → Z → ℝ}
    {VR : Fin nR → ℝ≥0 → Z → ℝ} (hW : ∀ s, Measurable (W s)) (hVL : ∀ i s, Measurable (VL i s))
    (hVR : ∀ j s, Measurable (VR j s))
    (hgeo : ∀ m z, 0 < S m z → SeedImageGeometry (xL z) (xR z) ρL ρR (fun t => W (min t (S m z)) z)
      (fun i t => VL i (min t (S m z)) z) (fun j t => VR j (min t (S m z)) z) (S m z)) (r : ℝ≥0) :
    ∃ f : Z → ℝ, Measurable f ∧ ∀ z, (∃ m, r ≤ S m z ∧ 0 < S m z) →
      seedCapacityNoise a ρL ρR (W · z) (fun i s => VL i s z) (fun j s => VR j s z) r = f z := by
  classical
  set cap : Z → ℝ≥0 := fun z => if ∃ m, r ≤ S m z ∧ 0 < S m z then r + 1 else 0 with hcap
  have hcov : ∀ z, r < cap z → ∃ m, r ≤ S m z ∧ 0 < S m z := fun z hz => by
    by_contra hn
    simp only [hcap, hn, ↓reduceIte, not_lt_zero] at hz
  have hcov' : ∀ z, (∃ m, r ≤ S m z ∧ 0 < S m z) → r < cap z := fun z hz => by
    simp only [hcap, hz, ↓reduceIte, lt_add_one]
  obtain ⟨f, hf, hfe⟩ := exists_measurable_seedCapacityNoise_before a ρL ρR (cap := cap) r
    (fun s => ⟨W s, hW s, fun _ _ => rfl⟩) (fun i s => ⟨VL i s, hVL i s, fun _ _ => rfl⟩)
    (fun j s => ⟨VR j s, hVR j s, fun _ _ => rfl⟩)
    (fun z hz => by
      obtain ⟨m, hrm, hm⟩ := hcov z hz
      exact (continuousOn_unstop_real (f := fun t => W t z) (hgeo m z hm).continuous_w hrm).mono Ioc_subset_Icc_self)
    (fun z hz i => by
      obtain ⟨m, hrm, hm⟩ := hcov z hz
      exact (continuousOn_unstop_real (f := fun t => VL i t z) ((hgeo m z hm).continuous_left i) hrm).mono
        Ioc_subset_Icc_self)
    (fun z hz j => by
      obtain ⟨m, hrm, hm⟩ := hcov z hz
      exact (continuousOn_unstop_real (f := fun t => VR j t z) ((hgeo m z hm).continuous_right j) hrm).mono
        Ioc_subset_Icc_self)
    (fun z hz i => by
      obtain ⟨m, hrm, hm⟩ := hcov z hz
      exact left_ne_unstop (w := fun t => W t z) (vL := fun i t => VL i t z)
        (vR := fun j t => VR j t z) (hgeo m z hm) hrm i)
    (fun z hz j => by
      obtain ⟨m, hrm, hm⟩ := hcov z hz
      exact right_ne_unstop (w := fun t => W t z) (vL := fun i t => VL i t z)
        (vR := fun j t => VR j t z) (hgeo m z hm) hrm j)
    (fun z hz i => by
      obtain ⟨m, hrm, hm⟩ := hcov z hz
      exact intervalIntegrable_unstop (g := fun t => (W t z - VL i t z)⁻¹) hrm
        ((hgeo m z hm).integrable_left r hrm i))
    (fun z hz j => by
      obtain ⟨m, hrm, hm⟩ := hcov z hz
      exact intervalIntegrable_unstop (g := fun t => (W t z - VR j t z)⁻¹) hrm
        ((hgeo m z hm).integrable_right r hrm j))
  exact ⟨f, hf, fun z hz => hfe z (hcov' z hz)⟩

/-- **The family's residual noise**: for image data indexed by the frozen time `σ`, jointly measurable in `(σ, z)` at
each time, with the driver `0` at time `0` and the geometry up to every positive cap, there is a noise, jointly
measurable at each time, `0` at time `0`, continuous on every cap interval at every sample, and equal to the residual
on every cap interval. -/
theorem exists_residualNoise (a : ℝ) {xL : ℝ≥0 → Z → Fin nL → ℝ} {xR : ℝ≥0 → Z → Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → ℝ≥0 → Z → ℝ} {VL : ℝ≥0 → Fin nL → ℝ≥0 → Z → ℝ}
    {VR : ℝ≥0 → Fin nR → ℝ≥0 → Z → ℝ} {S : ℝ≥0 → ℕ → Z → ℝ≥0}
    (hW : ∀ t, Measurable fun p : ℝ≥0 × Z => W p.1 t p.2)
    (hVL : ∀ i t, Measurable fun p : ℝ≥0 × Z => VL p.1 i t p.2)
    (hVR : ∀ j t, Measurable fun p : ℝ≥0 × Z => VR p.1 j t p.2) (hW0 : ∀ σ z, W σ 0 z = 0)
    (hgeo : ∀ σ m z, 0 < S σ m z → SeedImageGeometry (xL σ z) (xR σ z) ρL ρR (fun t => W σ (min t (S σ m z)) z)
      (fun i t => VL σ i (min t (S σ m z)) z) (fun j t => VR σ j (min t (S σ m z)) z) (S σ m z)) :
    ∃ N : ℝ≥0 → ℝ≥0 → Z → ℝ, (∀ t, Measurable fun p : ℝ≥0 × Z => N p.1 t p.2) ∧ (∀ σ z, N σ 0 z = 0) ∧
      (∀ σ m z, ContinuousOn (N σ · z) (Icc 0 (S σ m z))) ∧
      ∀ σ m z t, t ≤ S σ m z → N σ t z = seedCapacityNoise a ρL ρR (W σ · z) (fun i s => VL σ i s z)
        (fun j s => VR σ j s z) t := by
  classical
  have hex := fun r : ℝ≥0 => exists_measurable_residual_of_geometry (Z := ℝ≥0 × Z) a
    (xL := fun p => xL p.1 p.2) (xR := fun p => xR p.1 p.2) (ρL := ρL) (ρR := ρR) (S := fun m p => S p.1 m p.2)
    (W := fun s p => W p.1 s p.2) (VL := fun i s p => VL p.1 i s p.2) (VR := fun j s p => VR p.1 j s p.2) hW hVL hVR
    (fun m p hp => hgeo p.1 m p.2 hp) r
  choose f hf hfe using hex
  have hres0 : ∀ σ z, seedCapacityNoise a ρL ρR (W σ · z) (fun i s => VL σ i s z) (fun j s => VR σ j s z) 0 = 0 :=
    fun σ z => by rw [seedCapacityNoise_zero, hW0, zero_div]
  have heq : ∀ σ m z t, t ≤ S σ m z → (if t = 0 then 0 else f t (σ, z)) =
      seedCapacityNoise a ρL ρR (W σ · z) (fun i s => VL σ i s z) (fun j s => VR σ j s z) t := by
    intro σ m z t ht
    by_cases h0 : t = 0
    · simp only [h0, ↓reduceIte, hres0]
    · simp only [h0, ↓reduceIte]
      exact (hfe t (σ, z) ⟨m, ht, lt_of_lt_of_le (pos_iff_ne_zero.2 h0) ht⟩).symm
  refine ⟨fun σ t z => if t = 0 then 0 else f t (σ, z), fun t => ?_, fun σ z => by simp,
    fun σ m z => ?_, heq⟩
  · by_cases h0 : t = 0
    · simp only [h0, ↓reduceIte]
      exact measurable_const
    · simp only [h0, ↓reduceIte]
      exact hf t
  · rcases eq_zero_or_pos (S σ m z) with hS | hS
    · rw [hS, Icc_self]
      exact continuousOn_singleton _ _
    · exact (continuousOn_residual_of_geometry a (hgeo σ m z hS)).congr fun t ht => heq σ m z t ht.2

/-- **`hNs` for a noise continuous on the cap interval only** (MULTIMARK's `measurable_stopped_of_before`): a process
that is continuous on `[0, cap]`, `0` at time `0`, and agrees before a measurable cap with a measurable function at
each time is measurable at the cap. -/
theorem measurable_stopped_of_before_of_continuousOn {N : ℝ≥0 → Z → ℝ} {cap : Z → ℝ≥0} (hcap : Measurable cap)
    (hN : ∀ r, ∃ f : Z → ℝ, Measurable f ∧ ∀ z, r < cap z → N r z = f z)
    (hNc : ∀ z, ContinuousOn (N · z) (Icc 0 (cap z))) (hN0 : ∀ z, N 0 z = 0) (t : ℝ≥0) :
    Measurable fun z => N (min t (cap z)) z := by
  have e : (fun z => N (min t (cap z)) z) = fun z => stoppedAt N cap (min t (cap z)) z := by
    funext z
    simp only [stoppedAt, min_le_right, min_eq_left]
  rw [e]
  refine measurable_stopped_of_before hcap (fun r => ?_) (continuous_stoppedAt hNc)
    (fun z => by simp only [stoppedAt, zero_min, hN0]) t
  obtain ⟨f, hf, hfe⟩ := hN r
  exact ⟨f, hf, fun z hz => by simp only [stoppedAt, min_eq_left hz.le, hfe z hz]⟩

end Generic

/-! ### The one-sample law reads the noise up to the cap only -/

section Congr

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}

/-- **The one-sample law only reads the noise up to the cap.** -/
theorem IsSeedSampleLaw.congr_noise {Q : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {N N' : ℝ≥0 → Ω → ℝ} {Scap : ℕ → Ω → ℝ≥0}
    {m : ℕ} (h : IsSeedSampleLaw Q W ζ VL VR N Scap m) (hN : ∀ ω t, t ≤ Scap m ω → N' t ω = N t ω) :
    IsSeedSampleLaw Q W ζ VL VR N' Scap m := by
  obtain ⟨𝓗, B, hB, hBc, hC, hG, heq⟩ := h
  refine ⟨𝓗, B, hB, hBc, hC, fun s => ?_, ?_⟩
  · refine forall_imageGen (p := fun g => MeasurableSet[𝓗 s] (g ∩ {ω | s < Scap m ω}))
      (fun r hr U hU => hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inl rfl⟩⟩)
      (fun r hr U hU i => hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩)
      (fun r hr U hU j => hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))⟩⟩)
      (fun r hr U hU => ?_) (fun r hr k => hG s _ ⟨r, hr, Or.inr (Or.inl ⟨k, rfl⟩)⟩)
      (fun r hr => hG s _ ⟨r, hr, Or.inr (Or.inr rfl)⟩)
    exact measurableSet_preimage_inter_of_eqOn (𝓜 := {A | MeasurableSet[𝓗 s] A})
      (fun ω hω => hN ω r (hr.trans (le_of_lt hω))) (hG s _ ⟨r, hr, Or.inl ⟨U, hU, Or.inr (Or.inr (Or.inr rfl))⟩⟩)
  · filter_upwards [heq] with ω hω t ht
    rw [hω t ht, hN ω t ht]

end Congr

end InteractingSLE.ZhanGT4.A1RLaw
