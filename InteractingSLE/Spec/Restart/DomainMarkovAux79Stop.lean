/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovAux79

/-!
# K2's (S) gives the coupling characteristic functional at stopping times, without the driving equations

Packet PROVE-DOMAINMARKOV8. PROVE-DOMAINMARKOV7's (E) (`ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun`)
needs the conditional-law clause at every stopping time of a right-continuous filtration
(`MartMeans.IsCouplingCharFun`). The landed bridge from fixed times to stopping times
(`DomainMarkov.setIntegral_cexp_eq_cfAt_of_dyadic`, `condExp_cexp_eq_frozenRHS_of_dyadic`,
`Coupling.exists_drivingStopped_measurable`) assumes the integrated evolution itself (it is used under a kernel where
(E) is known), so it cannot produce (E). This file reruns those proofs with

* the integrated evolution replaced by **pathwise regularity** (`Aux79.IsForceReg`: driver from `0`, driver and
  force points continuous before `ζ`, force points on their sides), almost surely;
* the killed driving filtration replaced by **any filtration `𝓗`** in which the continuation is adapted before `ζ`,
  and its usual augmentation;
* the dyadic identities replaced by **K2's input (S)** (`K2.HasSafeLaw` for `𝓗` on the live event `F`, with `ζ = 0`
  almost surely off `F`), passed to the null augmentation (`exists_ae_eq_of_measurableSet_nullAugmented`).

## Main results

* `exists_stopped_measurable` (`Coupling.exists_drivingStopped_measurable` for `usualAugmentation 𝓗 P`);
* `setIntegral_cexp_eq_cfAt_of_hasSafeLaw`;
* **`isCouplingCharFun_of_hasSafeLaw`**: (S) for `𝓗` ⇒ `IsCouplingCharFun` for `usualAugmentation 𝓗 P`.

The proofs are copies of the landed ones with the changes above (provenance in the docstrings).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Restart.DomainMarkov.Aux79

open Coupling Ito K2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-! ### Measurability at a stopping time of the usual augmentation -/

/-- **Measurability at a stopping time of the usual augmentation of `𝓗`** (`Coupling.exists_drivingStopped_measurable`
with the driving filtration replaced by any filtration in which the continuation is adapted before `ζ`, and the
integrated evolution by `IsForceReg` almost surely). -/
theorem exists_stopped_measurable [IsProbabilityMeasure P] {𝓗 : Filtration ℝ≥0 mΩ}
    (hpath : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω) (hWa₀ : AdaptedBefore 𝓗 ζ W)
    (hVLa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVRa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VR i))
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (usualAugmentation 𝓗 P) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω)):
    ∃ E' : Set Ω, MeasurableSet[hτ.measurableSpace] E' ∧
      E' ⊆ {ω | Disjoint (tsupport ψ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))} ∧
      (∀ᵐ ω ∂P, Disjoint (tsupport ψ)
        (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) → ω ∈ E') ∧
      (∀ ω ∈ E', ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension
        (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
        (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
          (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) v →
        ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) v z * ψ z =
          ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * ψ z) ∧
      (∀ ω ∈ E', ContinuousOn (rpath (W · ω)) (Icc 0 (((τ ω).untopD 0 : ℝ≥0) : ℝ)) ∧ W 0 ω = 0 ∧
        ∀ z ∈ tsupport ψ, ∃ v, IsForwardSol (rpath (W · ω)) z (((τ ω).untopD 0 : ℝ≥0) : ℝ) v) ∧
      StronglyMeasurable[hτ.measurableSpace]
        (E'.indicator (frozenRHS κ W u ψ fun ω => (τ ω).untopD 0)) := by
  set 𝓓 := usualAugmentation 𝓗 P with h𝓓
  have h𝓓u : 𝓓 = usualAugmentation 𝓗 P := rfl
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  have hτf : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := hτζ.mono fun _ h => ne_top_of_lt_zeta h
  have hτ' : IsStoppingTime 𝓓 fun ω => (τ' ω : WithTop ℝ≥0) := isStoppingTime_untopD (𝓕 := 𝓗) hτ hτf
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[𝓓 0] s := fun s hs h0 =>
    measurableSet_usualAugmentation_of_null (𝓕 := 𝓗) hs h0 0
  have hσeq : hτ.measurableSpace = hτ'.measurableSpace := measurableSpace_untopD_eq hnull hτ hτf hτ'
  have hWa : AdaptedBefore 𝓓 ζ W :=
    adaptedBefore_mono (le_usualAugmentation 𝓗 P) hWa₀
  have hVLa : ∀ i, AdaptedBefore 𝓓 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation 𝓗 P) (hVLa₀ i)
  have hVRa : ∀ i, AdaptedBefore 𝓓 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_usualAugmentation 𝓗 P) (hVRa₀ i)
  have hpath' : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hpath] with ω hP using ⟨hP.2.1, hP.1⟩
  -- the support of `ψ`
  set K : Set ℂ := tsupport ψ with hKdef
  have hKH : K ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact hK hKH
  -- the truncations `τ ∧ n` and the safe stops below them
  set σ₀ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ' ω) n with hσ₀_def
  have hσ₀ : ∀ n : ℕ, IsStoppingTime 𝓓 fun ω => (σ₀ n ω : WithTop ℝ≥0) := fun n => by
    have h := hτ'.min_const (n : ℝ≥0)
    convert h using 2 with ω
    simp only [hσ₀_def, WithTop.coe_min]
  have hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω := fun ω n n' h =>
    min_le_min le_rfl (by exact_mod_cast h)
  have hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω := fun n => by
    filter_upwards [hτζ] with ω h
    exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) (coe_untopD_lt_zeta h)
  obtain ⟨ρ, hρst, hρle, hρmono, hρsafe, hρex⟩ := exists_safeSeq_of_adapted (𝓗 := 𝓗) (P := P)
    hWa₀ hpath' hK hKH hm hKm hσ₀ hσ₀m hσ₀ζ
  -- the good event
  set good : Ω → Prop := fun ω => IsForceReg W VL VR ζ ω ∧
    ((τ' ω : ℝ≥0∞) < ζ ω) ∧
    (∀ n : ℕ, IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) (ρ n ω)) ∧
    ∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ j ω →
      (∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z t u) → ∀ᶠ n in atTop, t ≤ ρ n ω with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hpath, hτζ, ae_all_iff.2 hρsafe, hρex] with ω h1 h2 h3 h4
    exact ⟨h1, coe_untopD_lt_zeta h2, h3, h4⟩
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h; exact hω (subset_toMeasurable _ _ h)
  have hG0 : MeasurableSet[𝓓 0] G := by
    have := (hnull _ hGm.compl hGc).compl
    rwa [compl_compl] at this
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  have hGw : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGgood ω hω).1.2.1
  have hGv : ∀ ω ∈ G, (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    ⟨(hGgood ω hω).1.2.2.1, (hGgood ω hω).1.2.2.2.1⟩
  have hδ : ∀ n : ℕ, 0 < m / ((n : ℝ) + 1) := fun n => by positivity
  have hψc : Continuous (ψ : ℂ → ℝ) := ψ.continuous
  -- the stopped pairs
  have hY : ∀ n : ℕ, Measurable[(hρst n).measurableSpace] fun ω => if ω ∈ G then
      ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ρ n ω) z * ψ z),
        loewnerGreenEnergy (rpath (W · ω)) (ρ n ω) ψ) else ((0 : ℝ), (0 : ℝ)) := fun n =>
    measurable_stoppedPair hWa hVLa hVRa hGw hGv hG0 hψc ψ.hasCompactSupport hKH (hδ n) (hρst n)
      fun ω hω => (hGgood ω hω).2.2.1 n
  have hle : ∀ n, (hρst n).measurableSpace ≤ hτ'.measurableSpace := fun n =>
    IsStoppingTime.measurableSpace_mono (hρst n) hτ' fun ω =>
      WithTop.coe_le_coe.2 ((hρle n ω).trans (min_le_left _ _))
  -- the events `F n = G ∩ {ρ_n = τ}`
  set F : ℕ → Set Ω := fun n => G ∩ {ω | ρ n ω = τ' ω} with hFdef
  have hGτ : MeasurableSet[hτ'.measurableSpace] G := by
    have h0 := IsStoppingTime.measurableSpace_mono (isStoppingTime_const 𝓓 (0 : ℝ≥0)) hτ'
      (fun ω => WithTop.coe_le_coe.2 (zero_le (a := τ' ω)))
    rw [IsStoppingTime.measurableSpace_const] at h0
    exact h0 _ hG0
  have hF : ∀ n, MeasurableSet[hτ'.measurableSpace] (F n) := fun n => by
    have h := IsStoppingTime.measurableSet_eq_stopping_time hτ' (hρst n)
    have e : {ω | ρ n ω = τ' ω} = {ω | (τ' ω : WithTop ℝ≥0) = (ρ n ω : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_ofPred_eq, WithTop.coe_inj, eq_comm]
    rw [hFdef]; simp only
    rw [e]
    exact hGτ.inter h
  have hFmono : ∀ ω n n', n ≤ n' → ω ∈ F n → ω ∈ F n' := fun ω n n' hnn' ⟨hω, heq⟩ =>
    ⟨hω, le_antisymm ((hρle n' ω).trans (min_le_left _ _)) (heq ▸ hρmono ω hnn')⟩
  -- on `F n`, the support is safe at `τ`
  have hsafeτ : ∀ n, ∀ ω ∈ F n,
      IsSafeAt K (m / ((n : ℝ) + 1)) n (σ₀ n ω) (ζ ω) (W · ω) (τ' ω) := fun n ω ⟨hω, heq⟩ => by
    have := (hGgood ω hω).2.2.1 n
    rwa [heq] at this
  have hmeanEq : ∀ n, ∀ ω ∈ F n, ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i (τ' ω) ω - W (τ' ω) ω)
        (fun i => VR i (τ' ω) ω - W (τ' ω) ω))
      (forceJumpSet (fun i => VL i (τ' ω) ω - W (τ' ω) ω) (fun i => VR i (τ' ω) ω - W (τ' ω) ω)) v →
      ∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (τ' ω : ℝ≥0) v z * ψ z =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (τ' ω) z * ψ z :=
    fun n ω hωF v hv => by
      have hω := hωF.1
      have hP := (hGgood ω hω).1
      have hτζω := (hGgood ω hω).2.1
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ K
      · have h1 : ∀ i, VL i (τ' ω) ω ≤ W (τ' ω) ω := fun i => (hP.2.2.2.2 (τ' ω) hτζω).1 i
        have h2 : ∀ i, W (τ' ω) ω ≤ VR i (τ' ω) ω := fun i => (hP.2.2.2.2 (τ' ω) hτζω).2 i
        have := couplingMean_eq_meanCan (κ := κ) (ρL := ρL) (ρR := ρR) (w := (W · ω))
          (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) (s := τ' ω) (z := z)
          (hGw ω hω) hKH (hsafeτ n ω hωF) (hδ n) le_rfl hz h1 h2 hv
        dsimp only
        rw [show (fun s : ℝ => W s.toNNReal ω) = rpath (W · ω) from rfl, this]
      · simp [image_eq_zero_of_notMem_tsupport hz]
  refine ⟨⋃ n, F n, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hσeq]; exact MeasurableSet.iUnion hF
  · -- inside the avoidance event
    rintro ω ⟨_, ⟨n, rfl⟩, hωF⟩
    have hs := hsafeτ n ω hωF
    have hw := hGw ω hωF.1
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    exact notMem_fwdHull_of_alive hw hs.1 (hKH hz) (hs.2.2.2 z hz).1 hzK
  · -- almost surely equal to it
    filter_upwards [hGae] with ω hω hdis
    obtain ⟨hP, hτζω, -, hexh⟩ := hGgood ω hω
    have halive : ∀ z ∈ K, ∃ u, IsForwardSol (rpath (W · ω)) z (τ' ω) u := fun z hz =>
      exists_isForwardSol_of_mem (τ' ω).coe_nonneg ⟨hKH hz, Set.disjoint_left.1 hdis hz⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, τ' ω ≤ (j : ℝ≥0) := by
      obtain ⟨j, hj⟩ := exists_nat_ge (τ' ω); exact ⟨j, hj⟩
    have hτj : τ' ω ≤ σ₀ j ω := le_min le_rfl hj
    obtain ⟨n, hn⟩ := (hexh j (τ' ω) hτj halive).exists
    exact mem_iUnion.2 ⟨n, hω, le_antisymm ((hρle n ω).trans (min_le_left _ _)) hn⟩
  · -- the mean does not depend on the bounded harmonic extension
    rintro ω ⟨_, ⟨n, rfl⟩, hωF⟩ v hv
    rw [hmeanEq n ω hωF v hv, hmeanEq n ω hωF (u ω) (hu ω)]
  · -- path facts
    rintro ω ⟨_, ⟨n, rfl⟩, hωF⟩
    have hs := hsafeτ n ω hωF
    exact ⟨continuousOn_rpath (hGw ω hωF.1) hs.1, (hGgood ω hωF.1).1.1,
      fun z hz => (hs.2.2.2 z hz).1⟩
  · -- measurability, as a limit of the values at the safe stops
    rw [hσeq]
    set Z : ℕ → Ω → ℂ := fun n => (F n).indicator fun ω => cfPair (if ω ∈ G then
      ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (ρ n ω) z * ψ z),
        loewnerGreenEnergy (rpath (W · ω)) (ρ n ω) ψ) else ((0 : ℝ), (0 : ℝ))) with hZ
    have hZm : ∀ n, StronglyMeasurable[hτ'.measurableSpace] (Z n) := fun n =>
      (((continuous_cfPair.measurable.comp (hY n)).mono (hle n) le_rfl).stronglyMeasurable).indicator
        (hF n)
    refine stronglyMeasurable_of_tendsto (m := hτ'.measurableSpace) atTop hZm
      (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ ⋃ n, F n
    · obtain ⟨n₀, hn₀⟩ := mem_iUnion.1 hω
      rw [indicator_of_mem hω]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n₀] with n hn
      have hωF := hFmono ω n₀ n hn hn₀
      have hωG : ω ∈ G := hωF.1
      simp only [hZ, indicator_of_mem hωF, hωG, ↓reduceIte, frozenRHS, cfPair]
      rw [hmeanEq n ω hωF (u ω) (hu ω), hωF.2]
      rfl
    · rw [indicator_of_notMem hω]
      have : ∀ n, Z n ω = 0 := fun n => indicator_of_notMem (fun h => hω (mem_iUnion.2 ⟨n, h⟩)) _
      simp only [this]
      exact tendsto_const_nhds


/-! ### Safe events and pieces under pathwise regularity -/

/-- **Along one good path, times decreasing to an avoidance time are eventually safe, and `cfAt` converges.** -/
theorem exists_eventually_isSafeAt_tendsto_cfAt' {u : Ω → ℝ≥0 → ℂ → ℝ}
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {ω : Ω}
    (hp : IsForceReg W VL VR ζ ω)
    {a : ℝ≥0} (haζ : (a : ℝ≥0∞) < ζ ω)
    (hdis : Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) a))
    {t : ℕ → ℝ≥0} (ht : Tendsto t atTop (𝓝 a)) :
    ∃ m : ℕ, (∀ᶠ n in atTop, IsSafeAt (tsupport ψ) (1 / ((m : ℝ) + 1)) (t n) (t n) (ζ ω) (W · ω) (t n)) ∧
      Tendsto (fun n => cfAt κ W u ψ 1 (fun _ => t n) ω) atTop (𝓝 (cfAt κ W u ψ 1 (fun _ => a) ω)) := by
  set K : Set ℂ := tsupport (ψ : ℂ → ℝ) with hKdef
  have hKH : K ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact K := ψ.hasCompactSupport.isCompact
  have hw : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.2.1
  obtain ⟨δ', hδ', hrζ, hdisj⟩ := exists_pos_disjoint_fwdHull_rpath' hw haζ hK hKH hdis
  set r : ℝ≥0 := a + δ' with hr
  have halive : ∀ z ∈ K, ∃ v, IsForwardSol (rpath (W · ω)) z r v := fun z hz =>
    exists_isForwardSol_of_mem r.coe_nonneg ⟨hKH hz, fun hzK => Set.disjoint_left.1 (hdisj r le_rfl) hz hzK⟩
  obtain ⟨δ₀, hδ₀, hsafe⟩ := exists_isSafeAt_self hw hp.1 hK hKH hrζ halive
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ₀
  have har : a < r := lt_add_of_pos_right a hδ'
  have hev_le : ∀ᶠ n in atTop, t n ≤ r := ((tendsto_order.1 ht).2 r har).mono fun n h => h.le
  refine ⟨m, hev_le.mono fun n hn => ?_, ?_⟩
  · exact (isSafeAt_self_of (hsafe.anti hw hKH hn)).mono hm.le le_rfl le_rfl
  set g : ℝ≥0 → ℂ := fun s => Complex.exp (Complex.I * 1 *
      ((∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z * ψ z : ℝ) : ℂ) -
      1 ^ 2 * ((loewnerGreenEnergy (rpath (W · ω)) s ψ : ℝ) : ℂ) / 2) with hg
  have hgc : ContinuousOn g (Iic r) := by
    have h1 := hsafe.continuousOn_meanInt (κ := κ) (ρL := ρL) (ρR := ρR) ψ.continuous ψ.hasCompactSupport hw
      hp.2.2.1 hp.2.2.2.1 hKH hδ₀
    have h2 := hsafe.continuousOn_loewnerGreenEnergy ψ.continuous ψ.hasCompactSupport hw hKH hδ₀
    exact ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h1)).sub
      ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h2)).div_const 2)).cexp
  have hcf : ∀ s ≤ r, cfAt κ W u ψ 1 (fun _ => s) ω = g s := fun s hs => by
    have hsζ : (s : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast hs) hrζ
    have hmean : (∫ z, couplingMean κ (fun x : ℝ => W x.toNNReal ω) s (u ω s) z * ψ z) =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s z * ψ z := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ K
      · have hvL : ∀ i, VL i s ω ≤ W s ω := (hp.2.2.2.2 s hsζ).1
        have hvR : ∀ i, W s ω ≤ VR i s ω := (hp.2.2.2.2 s hsζ).2
        have e := couplingMean_eq_meanCan (κ := κ) (ρL := ρL) (ρR := ρR) (w := (W · ω))
          (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hw hKH hsafe hδ₀ hs hz hvL hvR (hu ω s)
        exact congrArg (· * ψ z) e
      · simp [image_eq_zero_of_notMem_tsupport hz]
    simp only [cfAt, hg, hmean]
    rfl
  have hlim : Tendsto (fun n => g (t n)) atTop (𝓝 (g a)) :=
    (hgc a (mem_Iic.2 har.le)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨ht, hev_le⟩)
  rw [hcf a har.le]
  exact hlim.congr' (hev_le.mono fun n hn => (hcf (t n) hn).symm)

/-- On a safe event at a fixed time `q`, `cfAt q` is a measurable function (the explicit mean and energy). -/
theorem measurable_safeSet_indicator_cfAt' {𝓖 : Filtration ℝ≥0 mΩ} (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {G : Set Ω}
    (hGp : ∀ ω ∈ G, IsForceReg W VL VR ζ ω)
    (hG0 : MeasurableSet[𝓖 0] G) (hWa : AdaptedBefore 𝓖 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i))
    (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i)) {δ : ℝ} (hδ : 0 < δ) (q : ℝ≥0) :
    Measurable ((safeSet W ζ G ψ δ q).indicator (cfAt κ W u ψ 1 fun _ => q)) := by
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGp ω hω).2.1
  have e : (safeSet W ζ G ψ δ q).indicator (cfAt κ W u ψ 1 fun _ => q) =
      (safeSet W ζ G ψ δ q).indicator (fun ω =>
        Complex.exp (Complex.I * 1 * ((meanK κ ρL ρR W VL VR ζ G ψ δ q ω : ℝ) : ℂ) -
          1 ^ 2 * ((energyK W ζ G ψ δ q ω : ℝ) : ℂ) / 2)) := by
    refine indicator_congr fun ω hω => ?_
    have hp := hGp ω hω.1
    have hw := hGc ω hω.1
    have hvL : ∀ i, VL i q ω ≤ W q ω := (hp.2.2.2.2 q hω.2.1).1
    have hvR : ∀ i, W q ω ≤ VR i q ω := (hp.2.2.2.2 q hω.2.1).2
    have hmean : (∫ z, couplingMean κ (fun x : ℝ => W x.toNNReal ω) q (u ω q) z * ψ z) =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q z * ψ z := by
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      by_cases hz : z ∈ tsupport (ψ : ℂ → ℝ)
      · have e := couplingMean_eq_meanCan (κ := κ) (ρL := ρL) (ρR := ρR) (w := (W · ω))
          (vL := fun i t => VL i t ω) (vR := fun i t => VR i t ω) hw hKH hω.2 hδ le_rfl hz hvL hvR (hu ω q)
        exact congrArg (· * ψ z) e
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have hm : meanK κ ρL ρR W VL VR ζ G ψ δ q ω =
        ∫ z, meanCan κ ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) q z * ψ z := by
      simp only [meanK, hω, ↓reduceIte]
    have he : energyK W ζ G ψ δ q ω = loewnerGreenEnergy (rpath (W · ω)) q ψ := by
      simp only [energyK, hω, ↓reduceIte]
    rw [hm, he, ← hmean]
    rfl
  rw [e]
  refine Measurable.indicator ?_ ((𝓖.le q) _ (measurableSet_safeSet hWa hGc hG0 hKH hδ q))
  have h1 := (measurable_meanK hWa hGc hG0 hKH hδ κ ρL ρR hVLa hVRa ψ.continuous.measurable q).mono
    (𝓖.le q) le_rfl
  have h2 := (measurable_energyK hWa hGc hG0 hKH hδ ψ.continuous.measurable q).mono (𝓖.le q) le_rfl
  exact Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp h1)).sub
    ((measurable_const.mul (Complex.measurable_ofReal.comp h2)).div_const 2))


section Good

variable {u : Ω → ℝ≥0 → ℂ → ℝ}
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
  (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {G : Set Ω}
  (hGp : ∀ ω ∈ G, IsForceReg W VL VR ζ ω)

include hGp in
theorem safeU_subset_avoidSet' (q : ℝ≥0) : safeU W ζ G ψ q ⊆ avoidSet W ζ ψ q := fun ω hω => by
  obtain ⟨m, hm⟩ := mem_iUnion.1 hω
  have hw : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := (hGp ω hm.1).2.1
  have hs : IsSafeAt (tsupport (ψ : ℂ → ℝ)) (1 / ((m : ℝ) + 1)) q q (ζ ω) (W · ω) q := hm.2
  have hd : Disjoint (tsupport (ψ : ℂ → ℝ)) (fwdHull (rpath (W · ω)) q) :=
    disjoint_fwdHull_of_isSafeAt hw (tsupport_subset_H ψ) hs
  exact ⟨hs.1, hd⟩

include hGp in
theorem norm_cfAt_le_one_of_mem_safeU' (u : Ω → ℝ≥0 → ℂ → ℝ) {q : ℝ≥0} {ω : Ω} (hω : ω ∈ safeU W ζ G ψ q) :
    ‖cfAt κ W u ψ 1 (fun _ => q) ω‖ ≤ 1 := by
  obtain ⟨m, hm⟩ := mem_iUnion.1 hω
  exact norm_cfAt_le_one u 1 ψ (r := fun _ => q) (continuousOn_rpath (hGp ω hm.1).2.1 hm.2.1)
    (hGp ω hm.1).1 (fun z hz => (hm.2.2.2.2 z hz).1)

include hu hGp in
/-- `cfAt q` restricted to the safe union is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable_safeU_indicator_cfAt' {𝓖 : Filtration ℝ≥0 mΩ} (hG0 : MeasurableSet[𝓖 0] G)
    (hWa : AdaptedBefore 𝓖 ζ W) (hVLa : ∀ i, AdaptedBefore 𝓖 ζ (VL i)) (hVRa : ∀ i, AdaptedBefore 𝓖 ζ (VR i))
    (q : ℝ≥0) : AEStronglyMeasurable ((safeU W ζ G ψ q).indicator (cfAt κ W u ψ 1 fun _ => q)) P := by
  have hmK : ∀ m : ℕ, Measurable
      ((safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q).indicator (cfAt κ W u ψ 1 fun _ => q)) := fun m =>
    measurable_safeSet_indicator_cfAt' u hu ψ hGp hG0 hWa hVLa hVRa (by positivity) q
  refine aestronglyMeasurable_of_tendsto_ae atTop (fun m => (hmK m).aestronglyMeasurable)
    (ae_of_all _ fun ω => ?_)
  by_cases hω : ω ∈ safeU W ζ G ψ q
  · obtain ⟨m₀, hm₀⟩ := mem_iUnion.1 hω
    rw [indicator_of_mem hω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop m₀] with m hm
    have hle : 1 / ((m : ℝ) + 1) ≤ 1 / ((m₀ : ℝ) + 1) := by gcongr
    rw [indicator_of_mem (show ω ∈ safeSet W ζ G ψ (1 / ((m : ℝ) + 1)) q from
      ⟨hm₀.1, hm₀.2.mono hle le_rfl le_rfl⟩)]
  · rw [indicator_of_notMem hω]
    exact tendsto_const_nhds.congr fun m =>
      (indicator_of_notMem (fun h' => hω (mem_iUnion.2 ⟨m, h'⟩)) _).symm

include hu hGp in
/-- **Pointwise convergence of the discretized integrands.** Almost surely (on the good set, with `τ < ζ`), the sums
over the pieces at level `n` of `e^{i(h,ψ)}` and of `cfAt` converge to their values at `τ` on `A ∩ {τ < ∞}`. -/
theorem ae_tendsto_sum_piece' {τ : Ω → WithTop ℝ≥0} {A : Set Ω} (f : Ω → ℂ)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))})
    (hGae : ∀ᵐ ω ∂P, ω ∈ G) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n), (piece τ A W ζ G ψ n k).indicator f ω) atTop
        (𝓝 ((A ∩ {ω | τ ω ≠ ⊤}).indicator f ω)) ∧
      Tendsto (fun n => ∑ k ∈ Finset.range (4 ^ n),
          (piece τ A W ζ G ψ n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω) atTop
        (𝓝 ((A ∩ {ω | τ ω ≠ ⊤}).indicator (cfAt κ W u ψ 1 fun ω => (τ ω).untopD 0) ω)) := by
  have hlab : ∀ n k ω, ω ∈ piece τ A W ζ G ψ n k → ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k := fun n k ω hω => hω.1.2.2
  filter_upwards [hGae, hτζ] with ω hωG hωζ
  by_cases hωA : ω ∈ A ∩ {ω | τ ω ≠ ⊤}
  · have hne : τ ω ≠ ⊤ := hωA.2
    set a : ℝ≥0 := (τ ω).untopD 0 with ha
    have haζ : (a : ℝ≥0∞) < ζ ω := coe_untopD_lt_zeta hωζ
    obtain ⟨m, hevs, htend⟩ := exists_eventually_isSafeAt_tendsto_cfAt' hu ψ (hGp ω hωG) haζ (hAE hωA.1)
      (tendsto_dyT_ceil a)
    have hevC : ∀ᶠ n in atTop, ⌈2 ^ n * a⌉₊ ∈ Finset.range (4 ^ n) ∧
        ω ∈ piece τ A W ζ G ψ n ⌈2 ^ n * a⌉₊ := by
      filter_upwards [eventually_ceil_lt_four_pow a, hevs] with n hn hs
      exact ⟨Finset.mem_range.2 hn, ⟨⟨hωA.1, hne, rfl⟩, mem_safeU_of_isSafeAt hωG hs⟩⟩
    rw [indicator_of_mem hωA, indicator_of_mem hωA]
    refine ⟨tendsto_const_nhds.congr' (hevC.mono fun n hn => ?_), htend.congr' (hevC.mono fun n hn => ?_)⟩
    · beta_reduce
      rw [sum_indicator_eq_of_label (hlab n) ω]
      split_ifs with hc
      · exact (indicator_of_mem hn.2 _).symm
      · exact absurd hn.1 hc
    · beta_reduce
      rw [sum_indicator_eq_of_label (hlab n) ω]
      split_ifs with hc
      · exact (indicator_of_mem hn.2 _).symm
      · exact absurd hn.1 hc
  · have h0 : ∀ n k, ω ∉ piece τ A W ζ G ψ n k := fun n k hω => hωA ⟨hω.1.1, hω.1.2.1⟩
    rw [indicator_of_notMem hωA, indicator_of_notMem hωA]
    exact ⟨tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => indicator_of_notMem (h0 n k) _).symm,
      tendsto_const_nhds.congr fun n => (Finset.sum_eq_zero fun k _ => indicator_of_notMem (h0 n k) _).symm⟩

end Good


/-! ### The stopping-time identities -/

/-- **The protected-kernel law at every stopping time from (S), without the driving equations.** Let the
continuation `(W, VL, VR)` be adapted before `ζ` to a filtration `𝓗`, almost surely regular (`IsForceReg`), with
`ζ = 0` almost surely off the live event `F`, and let the field `X` satisfy K2's input (S) for `𝓗` on `F`. Then for
every test function `ψ`, every stopping time `τ < ζ` of the usual augmentation of `𝓗` and every event `A ∈ 𝓗_τ` inside
`{supp ψ ∩ K_τ = ∅}`: `∫_A e^{i(X,ψ)} = ∫_A cfAt τ` (`DomainMarkov.setIntegral_cexp_eq_cfAt_of_dyadic`, same proof, with
the integrated evolution replaced by the pathwise regularity and the dyadic identities by (S)). -/
theorem setIntegral_cexp_eq_cfAt_of_hasSafeLaw [IsProbabilityMeasure P] {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω}
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR h) (hpath : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω)
    (hζF : ∀ᵐ ω ∂P, ω ∉ F → ζ ω = 0) (hWa₀ : AdaptedBefore 𝓗 ζ W)
    (hVLa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVRa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VR i))
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation 𝓗 P) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    (hAE : A ⊆ {ω | Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))}) :
    ∫ ω in A, Complex.exp (Complex.I * (h ω ψ : ℂ)) ∂P =
      ∫ ω in A, cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun ω => (τ ω).untopD 0) ω ∂P := by
  classical
  set u := bheProc κ ρL ρR W VL VR with hudef
  have hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun ω s =>
    isBoundedHarmonicExtension_bheProc ω s
  set 𝓐 := nullAugmented 𝓗 P with h𝓐
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh ψ)))
  have hfb : ∀ ω, ‖f ω‖ ≤ 1 := fun ω => (norm_cexp_I_mul_ofReal _).le
  have hfint : Integrable f P := Integrable.of_bound hfm.aestronglyMeasurable 1 (ae_of_all _ hfb)
  -- the good set
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hpath.and hζF))
  set G : Set Ω := Nᶜ with hGdef
  have hGF : ∀ ω ∈ G, IsForceReg W VL VR ζ ω ∧ (ω ∉ F → ζ ω = 0) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  have hGp : ∀ ω ∈ G, IsForceReg W VL VR ζ ω := fun ω hω => (hGF ω hω).1
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    simpa [hGdef] using hN0
  have hG0 : MeasurableSet[𝓐 0] G := (measurableSet_nullAugmented_of_null hNm hN0 0).compl
  have hWa : AdaptedBefore 𝓐 ζ W :=
    adaptedBefore_mono (le_nullAugmented 𝓗 P) hWa₀
  have hVLa : ∀ i, AdaptedBefore 𝓐 ζ (VL i) := fun i =>
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (hVLa₀ i)
  have hVRa : ∀ i, AdaptedBefore 𝓐 ζ (VR i) := fun i =>
    adaptedBefore_mono (le_nullAugmented 𝓗 P) (hVRa₀ i)
  have hGc : ∀ ω ∈ G, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := fun ω hω =>
    (hGp ω hω).2.1
  -- the pieces
  set C : ℕ → ℕ → Set Ω := fun n k => piece τ A W ζ G ψ n k with hC
  have hCm𝓐 : ∀ n k, MeasurableSet[𝓐 (dyT n (k + 1))] (C n k) := fun n k => by
    have h1 : MeasurableSet[𝓐 (dyT n (k + 1))]
        (A ∩ {ω | τ ω ≠ ⊤ ∧ ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k}) :=
      usualAugmentation_le_nullAugmented (P := P) 𝓗 (dyT_lt_dyT_succ n k) _ (measurableSet_piece hτ hA n k)
    have h2 : MeasurableSet[𝓐 (dyT n (k + 1))] (safeU W ζ G ψ (dyT n (k + 1))) :=
      MeasurableSet.iUnion fun m => measurableSet_safeSet hWa hGc hG0 (tsupport_subset_H ψ) (by positivity) _
    exact h1.inter h2
  have hCm : ∀ n k, MeasurableSet (C n k) := fun n k => 𝓐.le _ _ (hCm𝓐 n k)
  have hcfint : ∀ n k, Integrable ((C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1))) P := by
    intro n k
    have e : (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) =
        (C n k).indicator ((safeU W ζ G ψ (dyT n (k + 1))).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1))) := by
      rw [indicator_indicator, inter_eq_left.2 (fun ω hω => hω.2)]
    rw [e]
    refine Integrable.of_bound (((aestronglyMeasurable_safeU_indicator_cfAt' hu ψ hGp hG0 hWa hVLa hVRa
      _).indicator (hCm n k))) 1 (ae_of_all _ fun ω => ?_)
    by_cases hω : ω ∈ C n k
    · rw [indicator_of_mem hω, indicator_of_mem hω.2]
      exact norm_cfAt_le_one_of_mem_safeU' ψ hGp u hω.2
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  -- the dyadic identity, summed over the pieces at level `n`
  have hGF : ∀ n, ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (C n k).indicator f ω ∂P =
      ∫ ω, ∑ k ∈ Finset.range (4 ^ n), (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω ∂P := by
    intro n
    rw [integral_finsetSum _ (fun k _ => hfint.indicator (hCm n k)),
      integral_finsetSum _ (fun k _ => hcfint n k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_indicator (hCm n k), integral_indicator (hCm n k)]
    obtain ⟨C', hC'm, hCC'⟩ := exists_ae_eq_of_measurableSet_nullAugmented (hCm𝓐 n k)
    rw [setIntegral_congr_set hCC', setIntegral_congr_set hCC']
    refine hlaw ψ (dyT n (k + 1)) C' hC'm ?_
    filter_upwards [hCC'] with ω hω hωC'
    have hωC : ω ∈ C n k := by
      have : (ω ∈ C n k) = (ω ∈ C') := hω
      rw [this]; exact hωC'
    have hav := safeU_subset_avoidSet' ψ hGp _ hωC.2
    obtain ⟨m, hm⟩ := mem_iUnion.1 hωC.2
    refine ⟨by_contra fun hωF => ?_, hav⟩
    have h0 := (hGF ω hm.1).2 hωF
    have := hav.1
    rw [h0] at this
    exact absurd this (not_lt.2 (zero_le (a := ((dyT n (k + 1) : ℝ≥0) : ℝ≥0∞))))
  -- bounds
  have hlab : ∀ n k ω, ω ∈ C n k → ⌈2 ^ n * (τ ω).untopD 0⌉₊ = k := fun n k ω hω => hω.1.2.2
  have hGb : ∀ n ω, ‖∑ k ∈ Finset.range (4 ^ n), (C n k).indicator f ω‖ ≤ 1 := fun n ω => by
    rw [sum_indicator_eq_of_label (hlab n) ω]
    split_ifs
    · by_cases hω : ω ∈ C n ⌈2 ^ n * (τ ω).untopD 0⌉₊
      · rw [indicator_of_mem hω]; exact hfb ω
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · rw [norm_zero]; exact zero_le_one
  have hFb : ∀ n ω, ‖∑ k ∈ Finset.range (4 ^ n),
      (C n k).indicator (cfAt κ W u ψ 1 fun _ => dyT n (k + 1)) ω‖ ≤ 1 := fun n ω => by
    rw [sum_indicator_eq_of_label (hlab n) ω]
    split_ifs
    · by_cases hω : ω ∈ C n ⌈2 ^ n * (τ ω).untopD 0⌉₊
      · rw [indicator_of_mem hω]; exact norm_cfAt_le_one_of_mem_safeU' ψ hGp u hω.2
      · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
    · rw [norm_zero]; exact zero_le_one
  -- dominated convergence
  have hpt := ae_tendsto_sum_piece' hu ψ hGp f hAE hGae hτζ
  have hlimG := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (integrable_finsetSum _ (fun k _ => hfint.indicator (hCm n k))).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (hGb n)) (hpt.mono fun ω h => h.1)
  have hlimF := tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (integrable_finsetSum _ (fun k _ => hcfint n k)).aestronglyMeasurable)
    (integrable_const 1) (fun n => ae_of_all _ (hFb n)) (hpt.mono fun ω h => h.2)
  have heq := tendsto_nhds_unique (hlimG.congr hGF) hlimF
  have hA'm : MeasurableSet (A ∩ {ω | τ ω ≠ ⊤}) :=
    (hτ.measurableSpace_le _ hA).inter (measurableSet_eq_top_of_isStoppingTime hτ).compl
  rw [integral_indicator hA'm, integral_indicator hA'm] at heq
  have hAA' : A =ᵐ[P] (A ∩ {ω | τ ω ≠ ⊤} : Set Ω) := by
    filter_upwards [hτζ] with ω hω
    exact propext ⟨fun h => ⟨h, ne_top_of_lt_zeta hω⟩, fun h => h.1⟩
  rw [setIntegral_congr_set hAA', setIntegral_congr_set hAA']
  exact heq


/-- **K2's (S) gives the coupling characteristic functional at stopping times (`IsCouplingCharFun`) for the usual
augmentation, without the driving equations** (`DomainMarkov.condExp_cexp_eq_frozenRHS_of_dyadic`, same proof, with
`setIntegral_cexp_eq_cfAt_of_hasSafeLaw`). This is the input of PROVE-DOMAINMARKOV7's
`ConverseBefore.isRandomWordEvolution_prod_of_isCouplingCharFun` (the driving equations (E)), so (E) follows from
(S) without circularity. -/
theorem isCouplingCharFun_of_hasSafeLaw [IsProbabilityMeasure P] {𝓗 : Filtration ℝ≥0 mΩ} {F : Set Ω}
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (hh : ∀ ψ, Measurable fun ω => h ω ψ)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR h) (hpath : ∀ᵐ ω ∂P, IsForceReg W VL VR ζ ω)
    (hζF : ∀ᵐ ω ∂P, ω ∉ F → ζ ω = 0) (hWa₀ : AdaptedBefore 𝓗 ζ W)
    (hVLa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVRa₀ : ∀ i, AdaptedBefore 𝓗 ζ (VR i)) :
    Coupling.MartMeans.IsCouplingCharFun κ ρL ρR P (usualAugmentation 𝓗 P) W VL VR ζ h := by
  intro τ hτ hτζ uτ huτ φ
  set u := bheProc κ ρL ρR W VL VR with hudef
  have hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s) := fun ω s =>
    isBoundedHarmonicExtension_bheProc ω s
  set τ' : Ω → ℝ≥0 := fun ω => (τ ω).untopD 0 with hτ'def
  obtain ⟨E', hE'm, hE'sub, hE'ae, hE'mean, hE'path, hE'sm⟩ :=
    exists_stopped_measurable hpath hWa₀ hVLa₀ hVRa₀ φ hτ hτζ uτ huτ
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) with hf
  have hfm : Measurable f :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hh φ)))
  have hfint : Integrable f P :=
    Integrable.of_bound hfm.aestronglyMeasurable 1
      (ae_of_all _ fun ω => (norm_cexp_I_mul_ofReal _).le)
  set g : Ω → ℂ := E'.indicator (frozenRHS κ W uτ φ τ') with hg
  have hcf : ∀ ω ∈ E', frozenRHS κ W uτ φ τ' ω = cfAt κ W u φ 1 τ' ω := fun ω hω => by
    simp only [frozenRHS, cfAt]
    rw [← hE'mean ω hω (u ω (τ' ω)) (hu ω (τ' ω))]
    congr 1
    push_cast
    ring
  have hgb : ∀ ω, ‖g ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ E'
    · rw [hg, indicator_of_mem hω, hcf ω hω]
      obtain ⟨h1, h2, h3⟩ := hE'path ω hω
      exact norm_cfAt_le_one u 1 φ (r := τ') h1 h2 h3
    · rw [hg, indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hgm : StronglyMeasurable[hτ.measurableSpace] g := hE'sm
  have hgint : Integrable g P :=
    Integrable.of_bound ((hgm.mono hτ.measurableSpace_le).aestronglyMeasurable) 1 (ae_of_all _ hgb)
  have hE'mΩ : MeasurableSet E' := hτ.measurableSpace_le _ hE'm
  have key : g =ᵐ[P] condExp hτ.measurableSpace P (E'.indicator f) := by
    refine ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
      (hfint.indicator hE'mΩ) (fun A _ _ => hgint.integrableOn) (fun A hA _ => ?_)
      hgm.aestronglyMeasurable
    have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
    rw [hg, setIntegral_indicator hE'mΩ, setIntegral_indicator hE'mΩ]
    have hAE : MeasurableSet[hτ.measurableSpace] (A ∩ E') :=
      @MeasurableSet.inter Ω hτ.measurableSpace _ _ hA hE'm
    have hdy' := setIntegral_cexp_eq_cfAt_of_hasSafeLaw h hh hlaw hpath hζF hWa₀ hVLa₀ hVRa₀ φ hτ hτζ hAE
      (inter_subset_right.trans hE'sub)
    rw [hdy']
    refine setIntegral_congr_fun (hAm.inter hE'mΩ) fun ω hω => ?_
    exact hcf ω hω.2
  have hind := condExp_indicator (m := hτ.measurableSpace) (μ := P) hfint hE'm
  filter_upwards [key, hind, hE'ae] with ω h1 h2 h3 hdis
  have hω : ω ∈ E' := h3 hdis
  have e1 : condExp hτ.measurableSpace P f ω =
      E'.indicator (condExp hτ.measurableSpace P f) ω := (indicator_of_mem hω _).symm
  rw [e1, ← h2, ← h1, hg, indicator_of_mem hω]
  rfl

end InteractingSLE.Restart.DomainMarkov.Aux79
