/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovSLE

/-!
# Zhan's A.1 (G3): removing every force point by Girsanov, with pathwise conclusions

Packet PROVE-A1-G3ROW. Source: specification, proof of Theorem 2.2 (L488: "applying Girsanov's theorem to produce the
process corresponding to one force point"); Astra, *Follow-up proofs* §A.1.3 (`ig1_followup_proofs.txt` L300–L355:
the large curve is compared with ordinary `SLE_κ` on a protected rectangle, where its own force gaps are bounded below).

The (G3) large curve is `SLE_κ(κ − 4, −4)`, not ordinary `SLE_κ`. A1-LARGEDENS's one-sample law
(`isSeedSampleLaw_largeG3_of_encl`) needs a Brownian motion `B⁰` with `√κ B⁰` equal to the large driver **at every
sample** up to the rectangle stop, continuous at every sample. `Girsanov.girsanov_remove_forcePoints` gives the change
of measure and the Brownian motion, with the driving identity only almost surely. Here the identity is proved pathwise:

* **`sqrt_mul_girsanovProcess_removeAll`**: at every sample where the path relation of the evolution holds and the force
  gaps are at least `δ` before `τ ≤ ζ`, `W_t = √κ B⁰_t` for `t ≤ τ` before the lifetime, where
  `B⁰ = girsanovProcess B (shiftDrift κ (−1) δ ρ τ ζ W V)` removes every mark;
* **`continuous_girsanovProcess_shiftDrift`**: `B⁰` is continuous at every sample where `B` is;
* **`girsanov_removeAll_pathwise`**: for an integrated `SLE_κ(ρ)` evolution with the path relation and a continuous
  Brownian path at every sample (A1-COMMON's patched marginals) and every-sample gaps before a bounded stopping time
  `τ ≤ ζ`: `Q = Z_{T+1}·P` is an equivalent probability measure, `B⁰` is a Brownian motion of the same filtration under
  `Q`, continuous at every sample, and `W_t = √κ B⁰_t` for every sample and every `t ≤ τ` before the lifetime.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3Row

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL nR : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ τ : Ω → ℝ≥0∞} {δ : ℝ}

/-- The drift removing every mark of the force word `(ρL; ρR)` up to `τ` (cut at gap `δ`). -/
abbrev removeAllDrift (κ δ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (τ ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  shiftDrift κ (-1) δ (removedWeights ρL ρR Finset.univ Finset.univ) τ ζ W (allMarks VL VR)

theorem continuous_shiftIntegrand_removeAll (hδ : 0 < δ) :
    Continuous fun p : ℝ × (Fin (nL + nR) → ℝ) =>
      shiftIntegrand κ (-1) δ (removedWeights ρL ρR Finset.univ Finset.univ) p.1 p.2 :=
  continuous_const.mul (continuous_addedDriftCut _ hδ)

theorem abs_shiftIntegrand_removeAll_le (hδ : 0 < δ) (w : ℝ) (u : Fin (nL + nR) → ℝ) :
    |shiftIntegrand κ (-1) δ (removedWeights ρL ρR Finset.univ Finset.univ) w u| ≤
      |(-1) / Real.sqrt κ| * ((∑ j, |removedWeights ρL ρR Finset.univ Finset.univ j|) * δ⁻¹) := by
  rw [shiftIntegrand, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le _ hδ w u) (abs_nonneg _)

/-- **The pathwise driving identity after removing every mark**: at a sample where the path relation holds, `τ ≤ ζ` and
every force gap is at least `δ` before `τ`, `W_t = √κ B⁰_t` for every `t ≤ τ` before the lifetime. -/
theorem sqrt_mul_girsanovProcess_removeAll (hκ : 0 < κ) (hδ : 0 < δ) {ω : Ω}
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω) (ζ ω))
    (hτζ : τ ω ≤ ζ ω) (hgL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ i, δ ≤ |W t ω - VL i t ω|)
    (hgR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → ∀ j, δ ≤ |W t ω - VR j t ω|) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ τ ω)
    (htζ : (t : ℝ≥0∞) < ζ ω) :
    W t ω = Real.sqrt κ * girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W VL VR) t ω := by
  obtain ⟨-, -, -, hWc, hVLc, hVRc, -, -, -, -, hiL, hiR, hweq, -⟩ := hp
  have hUc : ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := fun k => by
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hVLc i
    | right i => simpa [allMarks] using hVRc i
  have hsq : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  rw [girsanovProcess, show removeAllDrift κ δ ρL ρR τ ζ W VL VR = cutDrift τ ζ
      (shiftIntegrand κ (-1) δ (removedWeights ρL ρR Finset.univ Finset.univ)) W (allMarks VL VR) from rfl,
    drift_cutDrift_eq (continuous_shiftIntegrand_removeAll hδ) hτζ hWc hUc ht]
  -- the cut integrand is the uncut drift on `[0, t)`
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ uIoc 0 (t : ℝ) →
      shiftIntegrand κ (-1) δ (removedWeights ρL ρR Finset.univ Finset.univ) (W s.toNNReal ω)
          (fun k => allMarks VL VR k s.toNNReal ω) =
        (Real.sqrt κ)⁻¹ * ((∑ i, ρL i * (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹) +
          ∑ j, ρR j * (W s.toNNReal ω - VR j s.toNNReal ω)⁻¹) := by
    filter_upwards [ae_ne_real (t : ℝ)] with s hst hs
    rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
    have hlt : (s.toNNReal : ℝ≥0∞) < τ ω := by
      refine lt_of_lt_of_le ?_ ht
      rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
      exact lt_of_le_of_ne hs.2 hst
    have eL : ∀ i, recipCut δ (W s.toNNReal ω - VL i s.toNNReal ω) = (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹ :=
      fun i => recipCut_of_le hδ (hgL _ hlt i)
    have eR : ∀ j, recipCut δ (W s.toNNReal ω - VR j s.toNNReal ω) = (W s.toNNReal ω - VR j s.toNNReal ω)⁻¹ :=
      fun j => recipCut_of_le hδ (hgR _ hlt j)
    simp only [shiftIntegrand, addedDriftCut, Fin.sum_univ_add, removedWeights, allMarks, Fin.addCases_left,
      Fin.addCases_right, Finset.mem_univ, ite_true, eL, eR]
    ring
  have hIL : ∀ i, IntervalIntegrable (fun s : ℝ => ρL i * (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹) volume 0 t :=
    fun i => (hiL t htζ i).const_mul _
  have hIR : ∀ j, IntervalIntegrable (fun s : ℝ => ρR j * (W s.toNNReal ω - VR j s.toNNReal ω)⁻¹) volume 0 t :=
    fun j => (hiR t htζ j).const_mul _
  have hSL : IntervalIntegrable (fun s : ℝ => ∑ i, ρL i * (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹) volume 0 t := by
    have e : (fun s : ℝ => ∑ i, ρL i * (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹) =
        ∑ i, fun s : ℝ => ρL i * (W s.toNNReal ω - VL i s.toNNReal ω)⁻¹ := by
      ext s
      simp only [Finset.sum_apply]
    rw [e]
    exact IntervalIntegrable.sum Finset.univ fun i _ => hIL i
  have hSR : IntervalIntegrable (fun s : ℝ => ∑ j, ρR j * (W s.toNNReal ω - VR j s.toNNReal ω)⁻¹) volume 0 t := by
    have e : (fun s : ℝ => ∑ j, ρR j * (W s.toNNReal ω - VR j s.toNNReal ω)⁻¹) =
        ∑ j, fun s : ℝ => ρR j * (W s.toNNReal ω - VR j s.toNNReal ω)⁻¹ := by
      ext s
      simp only [Finset.sum_apply]
    rw [e]
    exact IntervalIntegrable.sum Finset.univ fun j _ => hIR j
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hSL hSR,
    intervalIntegral.integral_finsetSum fun i _ => hIL i, intervalIntegral.integral_finsetSum fun j _ => hIR j]
  have hw := hweq t htζ
  simp only [div_eq_mul_inv] at hw
  rw [hw, mul_add, ← mul_assoc, mul_inv_cancel₀ hsq, one_mul]
  ring

/-- **`B⁰` is continuous at every sample where `B` is.** -/
theorem continuous_girsanovProcess_removeAll (hδ : 0 < δ) (hW : AdaptedBefore 𝓕 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i)) (hVR : ∀ i, AdaptedBefore 𝓕 ζ (VR i))
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s}) {ω : Ω} (hBc : Continuous fun t => B t ω) :
    Continuous fun t => girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W VL VR) t ω := by
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (allMarks VL VR k) := fun k => by
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hVL i
    | right i => simpa [allMarks] using hVR i
  have hθ := isStronglyProgressive_cutDrift (continuous_shiftIntegrand_removeAll (κ := κ) (ρL := ρL) (ρR := ρR) hδ)
    hW hU hτ
  have hθb := abs_cutDrift_le (τ := τ) (ζ := ζ) (W := W) (U := allMarks VL VR)
    (abs_shiftIntegrand_removeAll_le (κ := κ) (ρL := ρL) (ρR := ρR) hδ)
  exact hBc.add (continuous_drift hθ hθb ω)

/-- **Removing every force point by Girsanov, pathwise.** Let `(W, V, B)` be an integrated `SLE_κ(ρ)` evolution whose
path relation holds and whose Brownian path is continuous at every sample, and `τ ≤ ζ ∧ T` a stopping time before
which every force gap is at least `δ > 0` at every sample. With `B⁰ = girsanovProcess B (removeAllDrift …)` and
`Q = girsanovMeasure P 𝓕 B (removeAllDrift …) (T + 1)`:

* `Q` is a probability measure equivalent to `P`;
* `B⁰` is a Brownian motion of `𝓕` under `Q`, continuous at every sample;
* at every sample, `W_t = √κ B⁰_t` for every `t ≤ τ` before the lifetime. -/
theorem girsanov_removeAll_pathwise [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hpath : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) (B · ω)
      (ζ ω))
    (hBc : ∀ ω, Continuous fun t => B t ω) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hδ : 0 < δ)
    (hgL : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < τ ω → ∀ i, δ ≤ |W t ω - VL i t ω|)
    (hgR : ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < τ ω → ∀ j, δ ≤ |W t ω - VR j t ω|) :
    MathFin.IsEquivProbMeasure P (girsanovMeasure P 𝓕 B (removeAllDrift κ δ ρL ρR τ ζ W VL VR) (T + 1)) ∧
    IsFilteredBrownianReal 𝓕 (girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W VL VR))
      (girsanovMeasure P 𝓕 B (removeAllDrift κ δ ρL ρR τ ζ W VL VR) (T + 1)) ∧
    (∀ ω, Continuous fun t => girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W VL VR) t ω) ∧
    ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) ≤ τ ω → (t : ℝ≥0∞) < ζ ω →
      W t ω = Real.sqrt κ * girsanovProcess B (removeAllDrift κ δ ρL ρR τ ζ W VL VR) t ω := by
  obtain ⟨h1, h2, -⟩ := girsanov_remove_forcePoints hκ hE Finset.univ Finset.univ hτ hτζ hτT hδ
    (Eventually.of_forall fun ω t ht => ⟨fun i _ => hgL ω t ht i, fun j _ => hgR ω t ht j⟩)
  obtain ⟨-, hW, hVL, hVR, -⟩ := hE
  exact ⟨h1, h2, fun ω => continuous_girsanovProcess_removeAll hδ hW hVL hVR hτ (hBc ω),
    fun ω t ht htζ => sqrt_mul_girsanovProcess_removeAll hκ hδ (hpath ω) (hτζ ω) (hgL ω) (hgR ω) ht htζ⟩

end InteractingSLE.ZhanGT4.A1G3Row
