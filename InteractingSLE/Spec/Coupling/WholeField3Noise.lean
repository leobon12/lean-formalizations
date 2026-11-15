/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Exhaust
import InteractingSLE.Spec.Coupling.Assembly11Drv

/-!
# The driving noise is a function of the driving state; localization in the driving filtration

Packet PROVE-WHOLEFIELD3 (follow-up note Part C.2, `source/external/AstraIG1/ig1_followup_proofs.txt` L1497–1548,
ruling R38; additional note §7.4, Aux. lemma 47, L3093–3128, ruling R39). C.2 proves that the driving Brownian motion
stays Brownian after the hull germ is retained. The germ filtration contains only the **driving** filtration
(`drivingFiltration`, the usual augmentation of the filtration of the killed driving state), in which the noise `B`
after the lifetime is not adapted. Two facts make the Itô localization of PROVE-T11-ITO2 available in that filtration:

* **Noise recovery** (C.7: "Brownian noise recoverable from the integrated state"). Before `ζ`, the integrated
  equations give `∫₀ᵗ ρ/(W − V) = −(ρ/2)(V_t − x)`, hence
  `√κ B_t = W_t + ∑ (ρᴸ/2)(Vᴸ_t − xᴸ) + ∑ (ρᴿ/2)(Vᴿ_t − xᴿ)` (`IsIntegratedSLEPath.eq_noiseOf`): before `ζ` the noise is
  a continuous function of the current driving state.
* **Localization in the driving filtration** (`exists_localizingSeq_driving`): the natural localizing sequence of
  `Ito.exists_localizingSeq_of_seq`, built from stopping times of the driving filtration, consists of stopping times
  of the driving filtration. The protection condition reads `B` only before `ζ`, where it agrees with the adapted
  process `noiseOf (W, V)` of the killed state.

## Main results

* `noiseOf`, `IsIntegratedSLEPath.eq_noiseOf`, `measurable_noiseOf`;
* `adapted_killedNoise`: the noise of the killed state is adapted to the driving filtration;
* `isProtectedAt_congr_noise`: the protection condition only reads the noise before `ζ`;
* **`exists_localizingSeq_driving`**: the localizing sequence of the Itô core in the driving filtration.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace WholeField

open Ito

variable {nL nR : ℕ}

/-! ### Noise recovery -/

/-- The noise recovered from the driving state: `(w + ∑ (ρᴸ/2)(vᴸ − xᴸ) + ∑ (ρᴿ/2)(vᴿ − xᴿ)) / √κ`. -/
def noiseOf (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (w : ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) : ℝ :=
  (w + (∑ i, ρL i / 2 * (vL i - xL i)) + ∑ i, ρR i / 2 * (vR i - xR i)) / Real.sqrt κ

theorem div_sub_eq_neg_half_mul (ρ a b : ℝ) : ρ / (a - b) = -(ρ / 2) * (2 / (b - a)) := by
  rw [show b - a = -(a - b) by ring, div_neg]
  ring

/-- `∫₀ᵗ ρ/(w − v) = −(ρ/2)(v_t − x)` when `v_t = x + ∫₀ᵗ 2/(v − w)`. -/
theorem integral_div_gap_eq {w v : ℝ≥0 → ℝ} {x ρ : ℝ} {t : ℝ≥0}
    (hv : v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)) :
    ∫ s in (0 : ℝ)..t, ρ / (w s.toNNReal - v s.toNNReal) = -(ρ / 2) * (v t - x) := by
  have e : (fun s : ℝ => ρ / (w s.toNNReal - v s.toNNReal)) =
      fun s => -(ρ / 2) * (2 / (v s.toNNReal - w s.toNNReal)) :=
    funext fun s => div_sub_eq_neg_half_mul ρ _ _
  rw [e, intervalIntegral.integral_const_mul]
  congr 1
  linarith

/-- **Noise recovery.** Before `ζ`, the noise of an integrated `SLE_κ(ρ)` path is `noiseOf` of the current state. -/
theorem IsIntegratedSLEPath.eq_noiseOf {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    b t = noiseOf κ ρL ρR xL xR (w t) (fun i => vL i t) (fun i => vR i t) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, hvLeq, hvReq, -⟩ := hp
  have hL : (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal)) =
      -∑ i, ρL i / 2 * (vL i t - xL i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_div_gap_eq (hvLeq t ht i)]
    ring
  have hR : (∑ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal)) =
      -∑ i, ρR i / 2 * (vR i t - xR i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_div_gap_eq (hvReq t ht i)]
    ring
  have hw := hweq t ht
  rw [hL, hR] at hw
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  rw [noiseOf, eq_div_iff hs.ne']
  linarith

theorem measurable_noiseOf (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) :
    Measurable fun p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => noiseOf κ ρL ρR xL xR p.1 p.2.1 p.2.2 := by
  unfold noiseOf
  refine Measurable.div_const (Measurable.add (Measurable.add measurable_fst ?_) ?_) _
  · exact Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply i).comp measurable_snd.fst).sub measurable_const).const_mul _
  · exact Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply i).comp measurable_snd.snd).sub measurable_const).const_mul _

/-! ### The noise of the killed state is adapted to the driving filtration -/

section Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The noise of the killed driving state (the cemetery value of each coordinate is `0`). -/
def killedNoise (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  noiseOf κ ρL ρR xL xR (Girsanov.killed ζ W t ω) (fun i => Girsanov.killed ζ (VL i) t ω)
    (fun i => Girsanov.killed ζ (VR i) t ω)

theorem killedNoise_of_lt (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) {t : ℝ≥0} {ω : Ω} (ht : (t : ℝ≥0∞) < ζ ω) :
    killedNoise κ ρL ρR xL xR W VL VR ζ t ω =
      noiseOf κ ρL ρR xL xR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω) := by
  simp only [killedNoise, Girsanov.killed_of_lt ht]

theorem adapted_killedNoise (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ)
    (xR : Fin nR → ℝ) (hW : AdaptedBefore 𝓖 ζ W) (hVL : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVR : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) : Adapted 𝓖 (killedNoise κ ρL ρR xL xR W VL VR ζ) := by
  intro t
  have hst : Measurable[𝓖 t] fun ω => (Girsanov.killed ζ W t ω, fun i => Girsanov.killed ζ (VL i) t ω,
      fun i => Girsanov.killed ζ (VR i) t ω) :=
    (Girsanov.measurable_killed hW t).prodMk
      (((@measurable_pi_iff Ω (Fin nL) (fun _ => ℝ) (𝓖 t) _ _).2 fun i =>
          Girsanov.measurable_killed (hVL i) t).prodMk
        ((@measurable_pi_iff Ω (Fin nR) (fun _ => ℝ) (𝓖 t) _ _).2 fun i =>
          Girsanov.measurable_killed (hVR i) t))
  exact @Measurable.comp _ _ _ (𝓖 t) _ _ _ _ (measurable_noiseOf κ ρL ρR xL xR) hst

end Adapted

/-! ### The protection condition reads the noise only before `ζ` -/

theorem isProtectedAt_congr_noise {k : ℕ} {zs : Fin k → ℂ} {δ ε R N : ℝ} {σ₀ : ℝ≥0} {ζ : ℝ≥0∞}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b b' : ℝ≥0 → ℝ} {t : ℝ≥0}
    (h : (t : ℝ≥0∞) < ζ → b t = b' t) :
    IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t ↔ IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b' t := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, h3, h4, h5, (h h1) ▸ h6, h7, h8, h9⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1, h2, h3, h4, h5, (h h1).symm ▸ h6, h7, h8, h9⟩

/-! ### The localizing sequence in the driving filtration -/

section Sequence

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The natural localizing sequence of the Itô core, in the driving filtration.** For an integrated `SLE_κ(ρ)`
evolution (`κ > 0`), finitely many distinct points `z_i ∈ ℍ`, and a nondecreasing sequence of stopping times
`σ₀ n < ζ` of the frozen driving filtration, the protection exit times of `Ito.exists_localizingSeq_of_seq` are
stopping times of the **driving** filtration, below `σ₀ n`, nondecreasing, protected, and exhausting every horizon
`t ≤ σ₀ j` at which the points are alive. -/
theorem exists_localizingSeq_driving (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (hX : IsMeasurableKilledDriving W VL VR ζ) {k : ℕ}
    {zs : Fin k → ℂ} (hz : ∀ i, 0 < (zs i).im) {m e : ℝ} (hm : 0 < m) (hzm : ∀ i, m ≤ (zs i).im)
    (he : 0 < e) (hze : ∀ i j, i ≠ j → e ≤ ‖zs i - zs j‖) {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : ∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (σ₀ n ω : WithTop ℝ≥0))
    (hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω) (hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω) :
    ∃ ρ : ℕ → Ω → ℝ≥0,
      (∀ n, IsStoppingTime (drivingFiltration P hX) fun ω => (ρ n ω : WithTop ℝ≥0)) ∧
      (∀ n ω, ρ n ω ≤ σ₀ n ω) ∧ (∀ ω, Monotone fun n => ρ n ω) ∧
      (∀ n : ℕ, ∀ᵐ ω ∂P, ∀ s ≤ ρ n ω, IsProtectedAt zs (m / ((n : ℝ) + 1)) (e / ((n : ℝ) + 1))
        ((n : ℝ) + initBound xL xR) n (σ₀ n ω) (ζ ω) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (B · ω) s) ∧
      ∀ᵐ ω ∂P, ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω →
        (∀ i, ∃ u, IsForwardSol (rpath (W · ω)) (zs i) t u) → ∀ᶠ n in atTop, t ≤ ρ n ω := by
  obtain ⟨hB, -, -, -, hpath⟩ := hE
  set 𝓖 := drivingFiltration P hX with h𝓖
  have h𝓖u : 𝓖 = usualAugmentation (killedDrivingFiltration hX) P := rfl
  have hWa : AdaptedBefore 𝓖 ζ W :=
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_W hX)
  have hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_VL hX i)
  have hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation _ P) (Coupling.adaptedBefore_killedDriving_VR hX i)
  have hba : Adapted 𝓖 (killedNoise κ ρL ρR xL xR W VL VR ζ) :=
    adapted_killedNoise κ ρL ρR xL xR hWa hVLa hVRa
  have hinj : Function.Injective zs := fun i j hij => by
    by_contra hne
    have := hze i j hne
    rw [hij, sub_self, norm_zero] at this
    linarith
  set good : Ω → Prop := fun ω => IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω)
    (fun i t => VL i t ω) (fun i t => VR i t ω) (fun t => B t ω) (ζ ω) ∧ Continuous (B · ω) ∧
    B 0 ω = 0 ∧ ∀ n, (σ₀ n ω : ℝ≥0∞) < ζ ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, hB.1.cont, hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero,
      ae_all_iff.2 hσ₀ζ] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG : ∀ t, MeasurableSet[𝓖 t] G := fun t => by
    have := (measurableSet_usualAugmentation_of_null (𝓕 := killedDrivingFiltration hX) hGm.compl hGc t).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set C := initBound xL xR with hC
  set ρ : ℕ → Ω → ℝ≥0 := fun n ω => if ω ∈ G then protectedExitTime zs (m / ((n : ℝ) + 1))
    (e / ((n : ℝ) + 1)) ((n : ℝ) + C) n (σ₀ n ω) (ζ ω) (W · ω) (fun i t => VL i t ω)
    (fun i t => VR i t ω) (B · ω) else 0 with hρ
  have hcont : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      (∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧ Continuous (B · ω) :=
    fun ω hω => ⟨(hGgood ω hω).1.2.2.2.1, (hGgood ω hω).1.2.2.2.2.1, (hGgood ω hω).1.2.2.2.2.2.1,
      (hGgood ω hω).2.1⟩
  have hδ : ∀ n : ℕ, 0 < m / ((n : ℝ) + 1) := fun n => by positivity
  -- on `G`, the protection condition with `B` is the one with the killed noise
  have hiff : ∀ ω ∈ G, ∀ (n : ℕ) (d : ℝ≥0),
      IsProtectedAt zs (m / ((n : ℝ) + 1)) (e / ((n : ℝ) + 1)) ((n : ℝ) + C) n (σ₀ n ω) (ζ ω) (W · ω)
          (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) d ↔
        IsProtectedAt zs (m / ((n : ℝ) + 1)) (e / ((n : ℝ) + 1)) ((n : ℝ) + C) n (σ₀ n ω) (ζ ω) (W · ω)
          (fun i t => VL i t ω) (fun i t => VR i t ω)
          (killedNoise κ ρL ρR xL xR W VL VR ζ · ω) d := fun ω hω n d =>
    isProtectedAt_congr_noise fun hd => by
      rw [killedNoise_of_lt κ ρL ρR xL xR hd]
      exact IsIntegratedSLEPath.eq_noiseOf hκ (hGgood ω hω).1 hd
  have h0 : ∀ ω ∈ G, ∀ n : ℕ, IsProtectedAt zs (m / ((n : ℝ) + 1)) (e / ((n : ℝ) + 1))
      ((n : ℝ) + C) n (σ₀ n ω) (ζ ω) (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) 0 := by
    intro ω hω n
    obtain ⟨hP, -, hB0, hσζ'⟩ := hGgood ω hω
    have hσζ := hσζ' n
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    have hC0 : 0 ≤ C := initBound_nonneg
    have hnC : C ≤ (n : ℝ) + C := by linarith [n.cast_nonneg (α := ℝ)]
    refine isProtectedAt_zero hz hP.1 hB0 (lt_of_le_of_lt (by exact_mod_cast zero_le) hσζ)
      (fun i => (div_le_self hm.le hn1).trans (hzm i))
      (fun i j hij => (div_le_self he.le hn1).trans (hze i j hij)) (hC0.trans hnC)
      (fun i => ?_) (fun i => ?_) n.cast_nonneg
    · rw [show VL i 0 ω = xL i from hP.2.1 i]; exact (abs_le_initBound_left i).trans hnC
    · rw [show VR i 0 ω = xR i from hP.2.2.1 i]; exact (abs_le_initBound_right i).trans hnC
  refine ⟨ρ, fun n => ?_, fun n ω => ?_, fun ω => ?_, fun n => ?_, ?_⟩
  · -- stopping times of the driving filtration
    have : 𝓖.IsRightContinuous := by rw [h𝓖u]; infer_instance
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
    refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t => ?_
    have heq : {ω | ((ρ n ω : ℝ≥0) : WithTop ℝ≥0) < (t : WithTop ℝ≥0)} =
        (⋃ d ∈ D ∩ Iio t, G \ {ω | ω ∈ G ∧ IsProtectedAt zs (m / ((n : ℝ) + 1))
          (e / ((n : ℝ) + 1)) ((n : ℝ) + C) n (σ₀ n ω) (ζ ω) (W · ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (killedNoise κ ρL ρR xL xR W VL VR ζ · ω) d}) ∪
          (Gᶜ ∩ {_ω | (0 : ℝ≥0) < t}) := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_lt_coe, mem_union, mem_iUnion, mem_inter_iff, Set.mem_sdiff,
        mem_Iio, exists_prop, mem_compl_iff]
      by_cases hω : ω ∈ G
      · obtain ⟨hwc, hvLc, hvRc, hbc⟩ := hcont ω hω
        simp only [hρ, hω, ↓reduceIte, true_and, not_true_eq_false, false_and, or_false]
        rw [protectedExitTime_lt_iff hwc hvLc hvRc hbc hz (hδ n) hDd]
        constructor
        · rintro ⟨d, hd, hdt, hnp⟩; exact ⟨d, ⟨hd, hdt⟩, fun h => hnp ((hiff ω hω n d).2 h)⟩
        · rintro ⟨d, ⟨hd, hdt⟩, hnp⟩; exact ⟨d, hd, hdt, fun h => hnp ((hiff ω hω n d).1 h)⟩
      · simp only [hρ, hω, ↓reduceIte, false_and, and_false, exists_false, false_or, not_false_eq_true,
          true_and]
    rw [heq]
    refine MeasurableSet.union (MeasurableSet.biUnion (hDc.mono inter_subset_left) fun d hd => ?_)
      ((hG t).compl.inter (MeasurableSet.const _))
    exact 𝓖.mono hd.2.le _ ((hG d).diff (measurableSet_isProtectedAt hWa hVLa hVRa hba
      (fun ω hω => (hcont ω hω).1) (hG 0) hz (hσ₀ n) _ _ _ _ d))
  · -- below σ₀
    by_cases hω : ω ∈ G
    · simp only [hρ, hω, ↓reduceIte]; exact protectedExitTime_le_sigma
    · simp only [hρ, hω, ↓reduceIte]; exact zero_le
  · -- monotone
    intro n n' hnn'
    by_cases hω : ω ∈ G
    · simp only [hρ, hω, ↓reduceIte]
      have hn : (n : ℝ) ≤ n' := by exact_mod_cast hnn'
      exact (protectedExitTime_mono (div_le_div_of_nonneg_left hm.le (by positivity) (by linarith))
        (div_le_div_of_nonneg_left he.le (by positivity) (by linarith)) (by linarith) hn).trans
        (protectedExitTime_mono_sigma (hσ₀m ω hnn'))
    · simp only [hρ, hω, ↓reduceIte]; exact le_rfl
  · -- protection
    filter_upwards [hGae] with ω hω s hs
    simp only [hρ, hω, ↓reduceIte] at hs
    obtain ⟨hwc, hvLc, hvRc, hbc⟩ := hcont ω hω
    exact isProtectedAt_of_le_protectedExitTime hwc hvLc hvRc hbc hz (hδ n) ((hGgood ω hω).2.2.2 n)
      (h0 ω hω n) hs
  · -- exhaustion
    filter_upwards [hGae] with ω hω j t htσ halive
    obtain ⟨hwc, hvLc, hvRc, hbc⟩ := hcont ω hω
    have hev := eventually_le_protectedExitTime hwc hvLc hvRc hbc hz hinj m e C htσ
      (lt_of_le_of_lt (by exact_mod_cast htσ) ((hGgood ω hω).2.2.2 j)) halive
    filter_upwards [hev, eventually_ge_atTop j] with n hn hjn
    simp only [hρ, hω, ↓reduceIte]
    exact hn.trans (protectedExitTime_mono_sigma (hσ₀m ω hjn))

end Sequence

end WholeField

end InteractingSLE
