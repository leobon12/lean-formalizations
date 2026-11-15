/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA3Drift

/-!
# The local comparison of Aux. lemma 55: the cross bracket `X B − ∫ θ` through and after the stop

Packet PROVE-LOCEXT-A3, item 1 (d). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L163–L182, p. 248): "The
stopped versions of these equations are used for arbitrary `t`."

* `martingale_mul_noise_sub_stopped`: for a bounded adapted `X` stopped at a stopping time `S` and the Brownian motion
  `B`, `X_t (B_t − B_{t∧S})` is a martingale (optional sampling at `ρ = (S ∨ s) ∧ t`: `V_t − V_s = X_t (B_t − B_ρ)` and
  `1_A X_t` is `𝓔_ρ`-measurable for `A ∈ 𝓔_s`);
* **`martingale_mul_B_sub_drift`**: with `X_t = ∫ 𝔥_{t∧S} v − (𝔥₀, v)` and the Girsanov drift `θ = srcTheta`,
  `X_t B_t − ∫₀ᵗ θ` is a martingale of the usual augmentation (the cross process of the source, the stopped noise, and the
  unstopped noise; `∫ v (Im f_{t∧S} − Im z) = ∫₀^{t∧S} A = ∫₀ᵗ θ` on the good event).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec2 Girsanov

/-! ### The unstopped noise -/

section Noise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **`X_t (B_t − B_{t∧S})` is a martingale** for a bounded adapted `X` stopped at the stopping time `S`. -/
theorem martingale_mul_noise_sub_stopped [IsProbabilityMeasure P] {𝓔 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsFilteredBrownianReal 𝓔 B P)
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝓔 t] N) {G : Set Ω}
    (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0) (hBc : ∀ ω ∈ G, Continuous (B · ω)) {S : Ω → ℝ≥0}
    (hS : IsStoppingTime 𝓔 fun ω => (S ω : WithTop ℝ≥0)) {X : ℝ≥0 → Ω → ℝ} (hX : StronglyAdapted 𝓔 X) {K : ℝ}
    (hXK : ∀ t ω, |X t ω| ≤ K) (hXS : ∀ t ω, X t ω = X (min t (S ω)) ω) :
    Martingale (fun t ω => X t ω * (WholeField.noiseOn B G t ω - WholeField.noiseOn B G (min t (S ω)) ω)) 𝓔 P := by
  set N := WholeField.noiseOn B G with hNdef
  obtain ⟨hN, -⟩ := WholeField.martingale_noiseOn hB hnull hGm hG0
  obtain ⟨hNS', -⟩ := WholeField.martingale_stoppedNoise hB hnull hGm hG0 hBc hS
  have hNS : Martingale (fun t ω => N (min t (S ω)) ω) 𝓔 P := by
    have e : stoppedProcess N (fun ω => (S ω : WithTop ℝ≥0)) = fun t ω => N (min t (S ω)) ω :=
      funext fun t => funext fun ω => WholeField.stoppedProcess_coe_apply N S t ω
    rwa [e] at hNS'
  have hNc : ∀ ω, Continuous fun t => N t ω := WholeField.continuous_noiseOn hBc
  set V : ℝ≥0 → Ω → ℝ := fun t ω => X t ω * (N t ω - N (min t (S ω)) ω) with hVdef
  have hVa : StronglyAdapted 𝓔 V := fun t => (hX t).mul ((hN.1 t).sub (hNS.1 t))
  have hVi : ∀ t, Integrable (V t) P := fun t =>
    ((hN.integrable t).sub (hNS.integrable t)).bdd_mul (((hX t).mono (𝓔.le t)).aestronglyMeasurable)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hXK t ω)
  refine ⟨hVa, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓔.le s) (hVi t) (fun A _ _ => (hVi s).integrableOn)
    (fun A hA _ => ?_) (hVa s).aestronglyMeasurable).symm
  -- `∫_A V_t = ∫_A V_s` by optional sampling at `ρ = (S ∨ s) ∧ t`
  set ρ : Ω → ℝ≥0 := fun ω => min (max (S ω) s) t with hρdef
  have hρ : IsStoppingTime 𝓔 fun ω => (ρ ω : WithTop ℝ≥0) := by
    have := (hS.max_const s).min_const t
    simp_rw [← WithTop.coe_max, ← WithTop.coe_min] at this
    exact this
  have hρt : ∀ ω, (ρ ω : WithTop ℝ≥0) ≤ t := fun ω => WithTop.coe_le_coe.2 (min_le_right _ _)
  set Z : Ω → ℝ := A.indicator (X t) with hZdef
  have hAm : MeasurableSet[𝓔 s] A := hA
  have hXt : ∀ v u, v ≤ u → Measurable[𝓔 u] (X v) := fun v u hvu => ((hX v).mono (𝓔.mono hvu)).measurable
  have hZ : StronglyMeasurable[hρ.measurableSpace] Z := by
    refine Measurable.stronglyMeasurable fun U hU => ?_
    refine ⟨?_, fun i => ?_⟩
    · have hZt : Measurable[𝓔 t] Z := (hXt t t le_rfl).indicator (𝓔.mono hst _ hAm)
      exact (le_iSup (fun u => 𝓔 u) t) _ (hZt hU)
    · rcases le_or_gt t i with hti | hit
      · have hset : {ω | (ρ ω : WithTop ℝ≥0) ≤ i} = univ := eq_univ_of_forall fun ω =>
          (hρt ω).trans (WithTop.coe_le_coe.2 hti)
        rw [hset, inter_univ]
        exact ((hXt t i hti).indicator (𝓔.mono (hst.trans hti) _ hAm)) hU
      · rcases le_or_gt s i with hsi | his
        · have hset : Z ⁻¹' U ∩ {ω | (ρ ω : WithTop ℝ≥0) ≤ i} =
              (A.indicator (X i)) ⁻¹' U ∩ {ω | (S ω : WithTop ℝ≥0) ≤ i} := by
            ext ω
            simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, WithTop.coe_le_coe, hρdef]
            constructor
            · rintro ⟨h1, h2⟩
              have hSi : S ω ≤ i := by
                rcases le_total (max (S ω) s) t with h | h
                · rw [min_eq_left h] at h2; exact (le_max_left _ _).trans h2
                · rw [min_eq_right h] at h2; exact absurd h2 (not_le.2 hit)
              have e : Z ω = A.indicator (X i) ω := by
                simp only [hZdef, indicator]
                rw [hXS t ω, hXS i ω, min_eq_right (hSi.trans hit.le), min_eq_right hSi]
              exact ⟨e ▸ h1, hSi⟩
            · rintro ⟨h1, h2⟩
              have e : Z ω = A.indicator (X i) ω := by
                simp only [hZdef, indicator]
                rw [hXS t ω, hXS i ω, min_eq_right (h2.trans hit.le), min_eq_right h2]
              exact ⟨e.symm ▸ h1, (min_le_left _ _).trans (max_le h2 hsi)⟩
          rw [hset]
          have hXi : Measurable[𝓔 i] (A.indicator (X i)) := (hXt i i le_rfl).indicator (𝓔.mono hsi _ hAm)
          exact (hXi hU).inter (hS i)
        · have hset : {ω | (ρ ω : WithTop ℝ≥0) ≤ i} = ∅ := eq_empty_of_forall_notMem fun ω h => by
            simp only [mem_ofPred_eq, WithTop.coe_le_coe, hρdef] at h
            have h1 : min s t ≤ min (max (S ω) s) t := min_le_min_right t (le_max_right _ _)
            exact absurd (h1.trans h) (not_le.2 (lt_min his hit))
          rw [hset, inter_empty]; exact @MeasurableSet.empty Ω (𝓔 i)
  have hZK : ∀ ω, |Z ω| ≤ K := fun ω => by
    by_cases hω : ω ∈ A
    · rw [hZdef, indicator_of_mem hω]; exact hXK t ω
    · rw [hZdef, indicator_of_notMem hω, abs_zero]; exact (abs_nonneg _).trans (hXK t ω)
  have hkey := Sec2.TwoSeed.integral_mul_sub_stoppedValue_eq_zero hN hNc hρ hρt hZ hZK
  have hsv : ∀ ω, stoppedValue N (fun ω => (ρ ω : WithTop ℝ≥0)) ω = N (ρ ω) ω := fun ω => rfl
  have hpt : ∀ ω, A.indicator (fun ω => V t ω - V s ω) ω =
      Z ω * (N t ω - stoppedValue N (fun ω => (ρ ω : WithTop ℝ≥0)) ω) := fun ω => by
    rw [hsv]
    by_cases hω : ω ∈ A
    · rw [indicator_of_mem hω, hZdef, indicator_of_mem hω, hVdef]
      simp only
      rcases le_total (S ω) s with hSs | hsS
      · have hρs : ρ ω = s := by rw [hρdef]; simp only [max_eq_right hSs, min_eq_left hst]
        have h1 : X s ω = X t ω := by rw [hXS s ω, hXS t ω, min_eq_right hSs, min_eq_right (hSs.trans hst)]
        rw [hρs, h1, min_eq_right hSs, min_eq_right (hSs.trans hst)]
        ring
      · rcases le_total (S ω) t with hSt | htS
        · have hρs : ρ ω = S ω := by rw [hρdef]; simp only [max_eq_left hsS, min_eq_left hSt]
          rw [hρs, min_eq_left hsS, min_eq_right hSt]
          ring
        · have hρs : ρ ω = t := by rw [hρdef]; simp only [max_eq_left hsS, min_eq_right htS]
          rw [hρs, min_eq_left (hst.trans htS), min_eq_left htS]
          ring
    · rw [indicator_of_notMem hω, hZdef, indicator_of_notMem hω, zero_mul]
  have hAm' : MeasurableSet A := 𝓔.le s _ hAm
  have h1 : ∫ ω in A, (V t ω - V s ω) ∂P = 0 := by
    rw [← integral_indicator hAm', integral_congr_ae (ae_of_all _ hpt)]
    exact hkey
  rw [integral_sub (hVi t).integrableOn (hVi s).integrableOn] at h1
  linarith

end Noise

/-! ### The cross bracket of the source with the noise -/

section Assembly

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}

theorem meanStop_eq_min (φ : ℂ → ℝ) (t : ℝ≥0) (ω : Ω) :
    meanStop κ ρL ρR r W VL VR ζ G φ t ω = meanStop κ ρL ρR r W VL VR ζ G φ (min t (stopTime r G ζ W ω)) ω := by
  unfold meanStop
  rw [min_eq_left (min_le_right t (stopTime r G ζ W ω))]

variable (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
  (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
  (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hG : ∀ ω ∈ G, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω)

include hκ hF hr hseed hG in
/-- The stopped tested mean of the source is bounded by `meanSrcBound · ∫ |v|`. -/
theorem abs_meanStop_vSrc_le (t : ℝ≥0) (ω : Ω) :
    |meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω| ≤
      meanSrcBound κ ρL ρR r * ∫ z, |vSrc κ xL xR ρL ρR r z| :=
  le_of_tendsto ((continuous_abs.tendsto _).comp (tendsto_meanDiag hκ hF hr hseed hG t ω))
    (Eventually.of_forall fun n => abs_meanDiag_le hκ hF hr hseed hG n t ω)

include hκ hE hF hr hseed hGm hGc hG in
/-- **The cross bracket of the source with the noise**: with `X_t = ∫ 𝔥_{t∧S} v − (𝔥₀, v)` and `θ = srcTheta`,
`X_t B_t − ∫₀ᵗ θ` is a martingale of the usual augmentation. -/
theorem martingale_mul_B_sub_drift :
    Martingale (fun t ω => (meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω -
        srcCentre κ xL xR ρL ρR r) * B t ω - drift (srcTheta κ xL xR ρL ρR r W VL VR ζ G) t ω)
      (usualAugmentation 𝓕 P) P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hE' := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[usualAugmentation 𝓕 P t] N :=
    fun t N hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t
  have hGp : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := fun ω hω => (hG ω hω).1
  have hBc : ∀ ω ∈ G, Continuous (B · ω) := fun ω hω => (hG ω hω).2
  have hS := isStoppingTime_stopTime (r := r) hE hGm hGc hGp
  have hmean := martingale_meanStop_vSrc hκ hE hF hr hseed hGm hGc hG
  have hcross := martingale_crossStop_vSrc hκ hE hF hr hseed hGm hGc hG
  set c₀ := srcCentre κ xL xR ρL ρR r with hc₀
  set K := meanSrcBound κ ρL ρR r * ∫ z, |vSrc κ xL xR ρL ρR r z| with hK
  set X : ℝ≥0 → Ω → ℝ := fun t ω => meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω - c₀ with hXdef
  set N := WholeField.noiseOn B G with hNdef
  have hXa : StronglyAdapted (usualAugmentation 𝓕 P) X := fun t => (hmean.1 t).sub stronglyMeasurable_const
  have hXK : ∀ t ω, |X t ω| ≤ K + |c₀| := fun t ω =>
    (abs_sub _ _).trans (add_le_add (abs_meanStop_vSrc_le hκ hF hr hseed hG t ω) le_rfl)
  have hXS : ∀ t ω, X t ω = X (min t (stopTime r G ζ W ω)) ω := fun t ω => by
    simp only [hXdef]; rw [meanStop_eq_min]
  have h3 := martingale_mul_noise_sub_stopped hE'.1 hnull hGm hGc hBc hS hXa hXK hXS
  obtain ⟨hNS', -⟩ := WholeField.martingale_stoppedNoise hE'.1 hnull hGm hGc hBc hS
  have hNS : Martingale (fun t ω => N (min t (stopTime r G ζ W ω)) ω) (usualAugmentation 𝓕 P) P := by
    have e : stoppedProcess N (fun ω => (stopTime r G ζ W ω : WithTop ℝ≥0)) =
        fun t ω => N (min t (stopTime r G ζ W ω)) ω :=
      funext fun t => funext fun ω => WholeField.stoppedProcess_coe_apply N _ t ω
    rwa [e] at hNS'
  have hY : Martingale (fun t ω => crossStop κ ρL ρR r W VL VR B ζ G (vSrc κ xL xR ρL ρR r) t ω -
      c₀ * N (min t (stopTime r G ζ W ω)) ω +
      X t ω * (N t ω - N (min t (stopTime r G ζ W ω)) ω)) (usualAugmentation 𝓕 P) P :=
    (hcross.sub (hNS.smul c₀)).add h3
  obtain ⟨hθp, hθb, -⟩ := hE'.isSLEEvolutionUpTo.weightDrift_props (seedWtL xL ρL) (seedWtR xR ρR)
    (measurableSet_le_capTime hE hGm hGc hGp) (capTime_le_zeta (r := r) (G := G) (ζ := ζ) (W := W))
    (show (0 : ℝ) < 7 * r by have := hr.1; positivity)
  have hBm : ∀ t, Measurable (B t) := fun t => (hE.1.2.1 t).mono (𝓕.le t) le_rfl
  refine WholeField.martingale_of_ae_eq_of_null hY (fun t => ?_) (fun t => ?_) hnull
  · exact ((((hmean.1 t).mono ((usualAugmentation 𝓕 P).le t)).measurable.sub_const _).mul (hBm t)).sub
      ((stronglyMeasurable_integral_comp hθp measurable_id t).mono ((usualAugmentation 𝓕 P).le t)).measurable
  · have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
    filter_upwards [hGae] with ω hω
    have hle : ((min t (stopTime r G ζ W ω) : ℝ≥0) : WithTop ℝ≥0) ≤ localStopPath r (ζ ω) fun t => W t ω := by
      rw [← coe_stopTime_of_mem hω]; exact WithTop.coe_le_coe.2 (min_le_right _ _)
    have hdr := drift_srcTheta_eq hGp hF hr hseed hθp hθb hω t
    have hint := integral_vSrc_mul_im_sub_eq_of_isGoodPath (hG ω hω).1.1 (hG ω hω).1.2 hF hr hseed hle
      (κ := κ) (ρL := ρL) (ρR := ρR)
    have hN1 : ∀ u, N u ω = B u ω := fun u => by simp [hNdef, WholeField.noiseOn, hω]
    simp only [hXdef, hN1, crossStop, hω, ↓reduceIte]
    have hint' : ∫ z, vSrc κ xL xR ρL ρR r z *
        ((QuantumZipper.fwdMap (Ito.rpath fun x => W x ω) (min t (stopTime r G ζ W ω) : ℝ≥0) z).im - z.im) =
        ∫ u in (0 : ℝ)..((min t (stopTime r G ζ W ω) : ℝ≥0) : ℝ),
          srcDrift κ xL xR ρL ρR r (fun s : ℝ => W s.toNNReal ω) u := hint
    rw [hdr, ← hint']
    ring

end Assembly

end LocalExt

end InteractingSLE
