/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA3Var
import InteractingSLE.Spec.Sec7.LocalExtAStoch

/-!
# The local comparison of Aux. lemma 55: the Cameron–Martin measure is the Girsanov measure through the stop

Packet PROVE-LOCEXT-A3, item 2 (f). Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L163–L206, pp. 248–249):
"`(M_t − m, v) = ∫₀ᵗ a_s dB_s`, `0 ≤ t ≤ S` … Thus under `ℚ`, `B^ℚ_{t∧S} = B_{t∧S} + ∫₀^{t∧S} a_s ds` is Brownian motion
stopped at `S` in the original stopped driving filtration", with (HL7) `a_t = κ^{−1/2} ∑_{j∈J} ρ_j/(W_t − V^j_t)`.

With `𝓔` the usual augmentation of the evolution's filtration, `S` the local stop and `θ = srcTheta` (the Girsanov drift
of the change of weights to the seed weights, cut at `S`):

* `stochIntegral_srcTheta_ae_eq`: `∫₀ᵗ θ dB = ∫ 𝔥_{t∧S} v − (𝔥₀, v)` almost surely (the brackets of `LocalExtA3Mart`,
  `LocalExtA3Noise` and the variance identity of `LocalExtA3Var`, through `LocalExt.stochIntegral_ae_eq_of_brackets`);
* `doleansDensity_srcTheta_ae_eq`: the Doléans density of `θ` at `r²/64 + 1` is `N_S = srcMart … S`;
* **`srcMeasure_eq_girsanovMeasure`**: `Q = Z · P` (`srcMeasure`) equals the Girsanov measure on the stopped driving
  σ-algebra `𝓖_S` (`S = capStop`);
* **`srcMeasure_girsanov`**: the Girsanov measure is equivalent to `P`, under it `(W, V, B + ∫ θ)` is a local evolution of
  the force word with the seed weights `(seedWtL, seedWtR)` before `S` (`Sec2.IsSLEEvolutionUpTo`), and it agrees with
  `Q` on `𝓖_S`; `map_srcMeasure_eq_map_girsanovMeasure`: hence every `𝓖_S`-measurable map (e.g. the history stopped at
  `S`) has the same law under `Q` and under the Girsanov measure;
* `exists_goodNoise_subset`: a good event with continuous noise inside any good event.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec2 Girsanov

section Girsanov

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **A good event with continuous noise inside a good event.** -/
theorem exists_goodNoise_subset [IsProbabilityMeasure P] (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0) :
    ∃ G' ⊆ G, MeasurableSet G' ∧ P G'ᶜ = 0 ∧ ∀ ω ∈ G', IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω := by
  obtain ⟨G₁, h1, h2, h3⟩ := exists_goodNoiseEvent hE hκ
  refine ⟨G ∩ G₁, inter_subset_left, hGm.inter h1, ?_, fun ω hω => h3 ω hω.2⟩
  rw [compl_inter]
  exact measure_union_null hGc h2

variable (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
  (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
  (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
  (hG : ∀ ω ∈ G, IsGoodNoisePath κ xL xR ρL ρR W VL VR B ζ ω)

include hκ hC hF hr hseed hGm hGc hG in
/-- **The tested mean of the source is the stochastic integral of `θ`**: `∫₀ᵗ θ dB = ∫ 𝔥_{t∧S} v − (𝔥₀, v)`. -/
theorem stochIntegral_srcTheta_ae_eq (t : ℝ≥0) :
    stochIntegral P (usualAugmentation 𝓕 P) B (srcTheta κ xL xR ρL ρR r W VL VR ζ G) t =ᵐ[P]
      fun ω => meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω - srcCentre κ xL xR ρL ρR r := by
  have hE := hC.1
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hE' := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hGp : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := fun ω hω => (hG ω hω).1
  obtain ⟨hθp, hθb, hθreg⟩ := hE'.isSLEEvolutionUpTo.weightDrift_props (seedWtL xL ρL) (seedWtR xR ρR)
    (measurableSet_le_capTime hE hGm hGc hGp) (capTime_le_zeta (r := r) (G := G) (ζ := ζ) (W := W))
    (show (0 : ℝ) < 7 * r by have := hr.1; positivity)
  have hB := isFilteredPreBrownian_of_isFilteredBrownianReal hE'.1
  have hmean := martingale_meanStop_vSrc hκ hE hF hr hseed hGm hGc hG
  have hX : Martingale (fun t ω => meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω -
      srcCentre κ xL xR ρL ρR r) (usualAugmentation 𝓕 P) P :=
    hmean.sub (martingale_const _ _ _)
  have hXL2 : ∀ t, MemLp (fun ω => meanStop κ ρL ρR r W VL VR ζ G (vSrc κ xL xR ρL ρR r) t ω -
      srcCentre κ xL xR ρL ρR r) 2 P := fun t =>
    MemLp.of_bound (((hX.1 t).mono ((usualAugmentation 𝓕 P).le t)).aestronglyMeasurable)
      (meanSrcBound κ ρL ρR r * (∫ z, |vSrc κ xL xR ρL ρR r z|) + |srcCentre κ xL xR ρL ρR r|)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact (abs_sub _ _).trans (add_le_add (abs_meanStop_vSrc_le hκ hF hr hseed hG t ω) le_rfl))
  exact stochIntegral_ae_eq_of_brackets hB hθp hθb hθreg hX hXL2
    (martingale_mul_B_sub_drift hκ hE hF hr hseed hGm hGc hG)
    (integral_meanStop_sub_sq_eq hκ hC hF hr hseed hGm hGc hG) t

include hκ hC hF hr hseed hGm hGc hG in
/-- **The Doléans density of `θ` past the stop is the density martingale at the stop**: `Z^θ_{r²/64+1} = N_S`. -/
theorem doleansDensity_srcTheta_ae_eq :
    doleansDensity P (usualAugmentation 𝓕 P) B (srcTheta κ xL xR ρL ρR r W VL VR ζ G) (stopHorizon r + 1) =ᵐ[P]
      fun ω => srcMart κ xL xR ρL ρR r W VL VR (stopTime r G ζ W ω) ω := by
  have hE := hC.1
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hE' := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hGp : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := fun ω hω => (hG ω hω).1
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  obtain ⟨hθp, hθb, -⟩ := hE'.isSLEEvolutionUpTo.weightDrift_props (seedWtL xL ρL) (seedWtR xR ρR)
    (measurableSet_le_capTime hE hGm hGc hGp) (capTime_le_zeta (r := r) (G := G) (ζ := ζ) (W := W))
    (show (0 : ℝ) < 7 * r by have := hr.1; positivity)
  filter_upwards [stochIntegral_srcTheta_ae_eq hκ hC hF hr hseed hGm hGc hG (stopHorizon r + 1), hGae]
    with ω h1 hω
  have hmin : min (stopHorizon r + 1) (stopTime r G ζ W ω) = stopTime r G ζ W ω :=
    min_eq_right ((stopTime_le_horizon ω).trans (le_add_of_nonneg_right zero_le_one))
  rw [doleansDensity, h1, quadInt_srcTheta_eq hGp hF hr hseed hθp hθb hω, hmin, srcMart]
  simp only [meanStop, hω, ↓reduceIte, hmin]
  rfl

include hκ hC hF hr hseed hGm hGc hG in
/-- **`Q = Z · P` is the Girsanov measure on the stopped driving σ-algebra `𝓖_S`.** -/
theorem srcMeasure_eq_girsanovMeasure (hX : IsMeasurableKilledDriving W VL VR ζ) {A : Set Ω}
    (hA : MeasurableSet[(isStoppingTime_capStop hX hGm hGc (fun ω hω => (hG ω hω).1) r).measurableSpace] A) :
    srcMeasure κ ρL ρR P hF hr h A =
      girsanovMeasure P (usualAugmentation 𝓕 P) B (srcTheta κ xL xR ρL ρR r W VL VR ζ G) (stopHorizon r + 1) A := by
  have hGp : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := fun ω hω => (hG ω hω).1
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set hτ := isStoppingTime_capStop hX hGm hGc hGp (B := B) r with hτdef
  have hτS : ∀ᵐ ω ∂P, capStop r G ζ W ω ≤ localStopPath r (ζ ω) fun t => W t ω := by
    filter_upwards [hGae] with ω hω
    rw [capStop_eq_localStop hGp hF hr hseed hω, localStop_of_mem hω]
  have hAm : MeasurableSet A := hτ.measurableSpace_le _ hA
  rw [srcMeasure_apply_of_measurableSet hκ hC hF hr hseed hX hτ hτS hA, girsanovMeasure,
    withDensity_apply _ hAm]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [doleansDensity_srcTheta_ae_eq hκ hC hF hr hseed hGm hGc hG, hGae] with ω h1 hω
  rw [h1, ← coe_capTime, WithTop.untopD_coe, capTime_eq_stopTime hGp hF hr hseed hω]

include hκ hC hF hr hseed hGm hGc hG in
/-- **The Girsanov step of Aux. lemma 55 (steps 3–4)**: with `θ = srcTheta` and `Q' = girsanovMeasure … θ (r²/64 + 1)`,
`Q'` is a probability measure equivalent to `P`; under `Q'`, `(W, V, B + ∫ θ)` is a local evolution of the force word with
the seed weights before the capped local stop; and `Q = Z · P` agrees with `Q'` on the stopped driving σ-algebra `𝓖_S`. -/
theorem srcMeasure_girsanov (hX : IsMeasurableKilledDriving W VL VR ζ) :
    MathFin.IsEquivProbMeasure P
        (girsanovMeasure P (usualAugmentation 𝓕 P) B (srcTheta κ xL xR ρL ρR r W VL VR ζ G) (stopHorizon r + 1)) ∧
      IsSLEEvolutionUpTo κ xL xR (seedWtL xL ρL) (seedWtR xR ρR)
        (girsanovMeasure P (usualAugmentation 𝓕 P) B (srcTheta κ xL xR ρL ρR r W VL VR ζ G) (stopHorizon r + 1))
        (usualAugmentation 𝓕 P) W VL VR (girsanovProcess B (srcTheta κ xL xR ρL ρR r W VL VR ζ G))
        (fun ω => (capTime r G ζ W ω : ℝ≥0∞)) ∧
      ∀ A, MeasurableSet[(isStoppingTime_capStop hX hGm hGc (fun ω hω => (hG ω hω).1) r).measurableSpace] A →
        srcMeasure κ ρL ρR P hF hr h A =
          girsanovMeasure P (usualAugmentation 𝓕 P) B (srcTheta κ xL xR ρL ρR r W VL VR ζ G) (stopHorizon r + 1) A := by
  have hE := hC.1
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hE' := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hGp : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω := fun ω hω => (hG ω hω).1
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  obtain ⟨h1, h2⟩ := hE'.isSLEEvolutionUpTo.girsanov_changeWeights hκ (seedWtL xL ρL) (seedWtR xR ρR)
    (measurableSet_le_capTime hE hGm hGc hGp) (capTime_le_zeta (r := r) (G := G) (ζ := ζ) (W := W))
    (T := stopHorizon r) (fun ω => ENNReal.coe_le_coe.2 (capTime_le_horizon ω))
    (show (0 : ℝ) < 7 * r by have := hr.1; positivity)
    (by filter_upwards [hGae] with ω hω t ht using gap_of_lt_capTime hGp hF hr hseed hω ht)
  exact ⟨h1, h2, fun A hA => srcMeasure_eq_girsanovMeasure hκ hC hF hr hseed hGm hGc hG hX hA⟩

include hκ hC hF hr hseed hGm hGc hG in
/-- **The stopped history has the same law under `Q` and under the Girsanov measure**: every `𝓖_S`-measurable map has the
same law under `Q = Z · P` and under `Q' = girsanovMeasure … θ (r²/64 + 1)`. -/
theorem map_srcMeasure_eq_map_girsanovMeasure (hX : IsMeasurableKilledDriving W VL VR ζ) {β : Type*}
    [MeasurableSpace β] {Ψ : Ω → β}
    (hΨ : Measurable[(isStoppingTime_capStop hX hGm hGc (fun ω hω => (hG ω hω).1) r).measurableSpace] Ψ) :
    (srcMeasure κ ρL ρR P hF hr h).map Ψ =
      (girsanovMeasure P (usualAugmentation 𝓕 P) B (srcTheta κ xL xR ρL ρR r W VL VR ζ G) (stopHorizon r + 1)).map Ψ := by
  have hΨm : Measurable Ψ :=
    hΨ.mono (isStoppingTime_capStop hX hGm hGc (fun ω hω => (hG ω hω).1) r).measurableSpace_le le_rfl
  ext U hU
  rw [Measure.map_apply hΨm hU, Measure.map_apply hΨm hU]
  exact srcMeasure_eq_girsanovMeasure hκ hC hF hr hseed hGm hGc hG hX (hΨ hU)

omit hG hGm hGc in
include hκ hC hF hr hseed in
/-- **`Q = Z · P` is a probability measure equivalent to `P`** (the `IsProbabilityMeasure Q ∧ P ≪ Q ∧ Q ≪ P` part of
`ReferenceExtensionStatement`). -/
theorem srcMeasure_isEquiv :
    IsProbabilityMeasure (srcMeasure κ ρL ρR P hF hr h) ∧ P ≪ srcMeasure κ ρL ρR P hF hr h ∧
      srcMeasure κ ρL ρR P hF hr h ≪ P :=
  ⟨isProbabilityMeasure_srcMeasure hκ hC hF hr hseed, absolutelyContinuous_srcMeasure hC hF hr,
    srcMeasure_absolutelyContinuous hF hr⟩

end Girsanov

end LocalExt

end InteractingSLE
