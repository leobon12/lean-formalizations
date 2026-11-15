/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.AuditFix.MarkovKernel

/-!
# Theorem 2.2, the Markov sentence: the time-zero case

Packet PROVE-AF-MARKOV. The landed restart law needs `0 < T` or a separated word: from an entrance word (two
marks at `0⁻`, `0⁺`) the state at time `0` is not separated, and the canonical Wiener functional does not start
there. The Markov property at time `0` is instead a consequence of uniqueness in law: conditioning on an event of
`𝓕₀` keeps the hypotheses of Definition 2.1, so by frozen Theorem 2.2 (uniqueness in law) the killed state is
independent of `𝓕₀`.

* `isFilteredBrownianReal_cond`: for `A ∈ 𝓕₀` with `P A ≠ 0`, `B` is still a Brownian motion of `𝓕` under `P[·|A]`
  (the whole path is independent of `𝓕₀`, `indep_future` at time `0`);
* `isIntegratedSLEEvolution_cond`: so `(W, V, B)` is an integrated evolution under `P[·|A]`;
* **`measure_inter_killedState`**: `P(A ∩ {killed-state event}) = P(A) · P(killed-state event)` for `A ∈ 𝓕₀`;
* `isOrderedForceWord_of_path`: a path that is alive at time `0` has an ordered word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace AuditFix

namespace Markov

open Sec2 Sec2.Restart QuantumZipper.StrongMarkov

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Conditioning on an event of `𝓕₀` keeps a filtered Brownian motion.** -/
theorem isFilteredBrownianReal_cond (hB : IsFilteredBrownianReal 𝓕 B P) {A : Set Ω}
    (hA : MeasurableSet[𝓕 0] A) (hPA : P A ≠ 0) : IsFilteredBrownianReal 𝓕 B (P[|A]) := by
  have hP : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  have hAm : MeasurableSet A := 𝓕.le 0 _ hA
  have hBm : ∀ t, Measurable (B t) := hB.measurable'
  have hind := indep_future hB 0
  have h0 := hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero
  refine ⟨⟨⟨fun I => ?_⟩, cond_absolutelyContinuous.ae_le hB.1.cont⟩, hB.2.1, fun s t hst => ?_⟩
  · -- the finite-dimensional laws are unchanged: the path is independent of `𝓕₀`
    set Y : Ω → I → ℝ := fun ω => I.restrict (smPath B (fun _ => (0 : ℝ≥0)) ω) with hY
    have hYm : Measurable[MeasurableSpace.comap (smPath B (fun _ => (0 : ℝ≥0)))
        MeasurableSpace.pi] Y :=
      (Finset.measurable_restrict I).comp (comap_measurable _)
    have hsm : Measurable (smPath B (fun _ => (0 : ℝ≥0))) :=
      measurable_pi_iff.2 fun s => (hBm _).sub (hBm _)
    have hYm' : Measurable Y := (Finset.measurable_restrict I).comp hsm
    have hXY : (fun ω => I.restrict (B · ω)) =ᵐ[P] Y := by
      filter_upwards [h0] with ω hω
      funext s
      simp only [hY, Finset.restrict, smPath, smShift, zero_add, hω, sub_zero]
    have hmap : (P[|A]).map Y = P.map Y := by
      ext D hD
      rw [Measure.map_apply hYm' hD, Measure.map_apply hYm' hD, cond_apply hAm,
        (Indep_iff _ _ _).1 hind A (Y ⁻¹' D) hA (hYm hD), ← mul_assoc,
        ENNReal.inv_mul_cancel hPA (measure_ne_top _ _), one_mul]
    have hXm : Measurable fun ω => I.restrict (B · ω) :=
      (Finset.measurable_restrict I).comp (measurable_pi_iff.2 hBm)
    refine ⟨hXm.aemeasurable, ?_⟩
    rw [Measure.map_congr (cond_absolutelyContinuous.ae_le hXY), hmap, ← Measure.map_congr hXY]
    exact (hB.1.hasLaw I).map_eq
  · exact indep_cond (𝓕.le s) (hB.2.2 s t hst) (𝓕.mono (zero_le : (0 : ℝ≥0) ≤ s) _ hA)

/-- **Conditioning on an event of `𝓕₀` keeps an integrated evolution.** -/
theorem isIntegratedSLEEvolution_cond (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {A : Set Ω} (hA : MeasurableSet[𝓕 0] A) (hPA : P A ≠ 0) :
    IsIntegratedSLEEvolution a xL xR ρL ρR (P[|A]) 𝓕 W VL VR B ζ :=
  ⟨isFilteredBrownianReal_cond hE.1 hA hPA, hE.2.1, hE.2.2.1, hE.2.2.2.1,
    cond_absolutelyContinuous.ae_le hE.2.2.2.2⟩

/-- **The Markov property at time `0`**: for an ordered word the killed state is independent of `𝓕₀`
(uniqueness in law, frozen Theorem 2.2, under the conditional measures). -/
theorem measure_inter_killedState (ha : 0 < a) (hF : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {A : Set Ω}
    (hA : MeasurableSet[𝓕 0] A) {n : ℕ} (ts : Fin n → ℝ≥0)
    {K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)} (hK : ∀ j, MeasurableSet (K j)) :
    P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ K j}) =
      P A * P {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω ∧
        (W (ts j) ω, (fun i => VL i (ts j) ω), (fun i => VR i (ts j) ω), B (ts j) ω) ∈ K j} := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hAm : MeasurableSet A := 𝓕.le 0 _ hA
  by_cases hPA : P A = 0
  · rw [hPA, zero_mul]
    exact measure_mono_null inter_subset_left hPA
  have := cond_isProbabilityMeasure (μ := P) hPA
  have h := IsIntegratedSLEEvolution.measure_killedState_eq ha hF
    (isIntegratedSLEEvolution_cond hE hA hPA) hE n ts K hK
  rw [cond_apply hAm] at h
  rw [← h, ← mul_assoc, ENNReal.mul_inv_cancel hPA (measure_ne_top _ _), one_mul]

/-- A path that is alive at time `0` has an ordered force word. -/
theorem isOrderedForceWord_of_path {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b τ) (h0 : ((0 : ℝ≥0) : ℝ≥0∞) < τ) :
    IsOrderedForceWord xL xR := by
  have hfp := hp.isForcePath
  refine ⟨?_, fun i => ?_, ?_, fun i => ?_⟩
  · have := hfp.antitone_vL h0
    simpa only [hfp.vL_zero] using this
  · have := hfp.vL_le_w h0 i
    rwa [hfp.vL_zero i, hfp.w_zero] at this
  · have := hfp.monotone_vR h0
    simpa only [hfp.vR_zero] using this
  · have := hfp.w_le_vR h0 i
    rwa [hfp.vR_zero i, hfp.w_zero] at this

end Markov

end AuditFix

end InteractingSLE
