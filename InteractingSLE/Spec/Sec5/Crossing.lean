/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.GirsanovSLE
import MathFin.Probability.Analysis.FiniteMeasureCauchySchwarz

/-!
# Lemma 5.10: the Girsanov–Cauchy–Schwarz transfer of the crossing estimate

Packet PROVE-SEC5-A (specification §5.2, Lemma 5.10 and its proof, `source/spec/p097-144.md` L922–L959,
pp. 140–141, with the correction printed on p. 141: "`ℙ(A) ≥ e^{−C²/κ} ℙ̂(A)²` for `A = {τ ≥ 1}`").

The proof of Lemma 5.10 removes the bounded additional drift `U` by Girsanov's theorem: under `ℙ̂ = Z · ℙ`,
`Z = exp(M_ζ − ½⟨M⟩_ζ)`, `M = −κ^{-1/2} ∫ U dB`, the pair `(W, V^{1,R})` is a one-force-point evolution. Then
(5.6), `ℙ̂[A] = 𝔼[1_A Z] ≤ (ℙ[A] 𝔼[Z²])^{1/2}`, and `𝔼[Z²] ≤ e^{⟨M⟩-bound}` give `ℙ[A] ≥ e^{−C²/κ} ℙ̂[A]²`.

In the sign convention of the landed Girsanov theorem (`Girsanov.doleansDensity`,
`Z_t = exp(−∫₀ᵗ θ dB − ½∫₀ᵗ θ²)`, `θ = −κ^{-1/2}·(drift)`), for a bounded `|θ| ≤ C'`:

* `integral_sq_doleansDensity_le`: `𝔼[Z_T²] ≤ exp(C'² T)` (Fatou along the approximating simple densities, whose
  second moments obey the same bound);
* `girsanovMeasure_real_sq_le`: for every event `A`, `ℙ̂(A)² ≤ ℙ(A) · exp(C'² T)`, with `ℙ̂ = Z_T · ℙ`
  (`Girsanov.girsanovMeasure`);
* `le_measureReal_of_girsanov`: `exp(−C'² T) ℙ̂(A)² ≤ ℙ(A)`. With `|U| ≤ C`, `θ = −U/√κ`, `C' = C/√κ` and `T = 1`
  this is the corrected crossing estimate `ℙ(A) ≥ e^{−C²/κ} ℙ̂(A)²` (`le_measureReal_of_girsanov_drift`);
* `le_measureReal_of_girsanov_cutDrift`, `le_measureReal_of_remove_forcePoints`: the same transfer for the cut drifts
  of the landed Girsanov theorems, in particular for the measure of `Girsanov.girsanov_remove_forcePoints` under
  which an integrated `SLE_κ(ρ)` evolution, with the separated marks removed up to a stopping time `τ ≤ ζ ∧ T`,
  follows the equation of the remaining word (horizon `T + 1`, constant `exp(−C'²(T + 1))`).
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

section Density

variable [IsProbabilityMeasure P] [hB : IsFilteredPreBrownian B 𝓕 P]

include hB

/-- **The second moment of the Doléans density** of a bounded drift: `𝔼[Z_T²] ≤ exp(C² T)` for `|θ| ≤ C`
(proof of Lemma 5.10: "Since `⟨M⟩_ζ ≤ C²/κ`, … `𝔼[exp(2M_ζ − ⟨M⟩_ζ)] ≤ C₀`"). -/
theorem integral_sq_doleansDensity_le (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) :
    ∫ ω, (doleansDensity P 𝓕 B θ T ω) ^ 2 ∂P ≤ Real.exp (C ^ 2 * (T : ℝ)) := by
  have hTc : T ≤ (⌈(T : ℝ)⌉₊ : ℝ≥0) := by simpa using le_shift T 0
  obtain ⟨ms, hms⟩ := exists_subseq_ae_tendsto_approxDensity (B := B) hθm hθb hθreg hTc id
    tendsto_id
  set c := ⌈(T : ℝ)⌉₊
  set f : ℕ → Ω → ℝ := fun k => approxDensity B θ (ms k + c) T
  have hmeas : ∀ k, Measurable (f k) := fun k => measurable_approxDensity (B := B) (P := P) hθm hθb _ T
  have hbnd : ∀ k, ∫⁻ ω, ENNReal.ofReal ((f k ω) ^ 2) ∂P ≤ ENNReal.ofReal (Real.exp (C ^ 2 * T)) := by
    intro k
    have hint := (memLp_two_iff_integrable_sq
      (memLp_approxDensity (B := B) (P := P) hθm hθb hTc (ms k)).aestronglyMeasurable).mp
      (memLp_approxDensity (B := B) (P := P) hθm hθb hTc (ms k))
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (sq_integral_approxDensity_le (B := B) hθm hθb hTc (ms k))
  have hZ := memLp_doleansDensity (B := B) hθm hθb hθreg T
  have hZint := (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).mp hZ
  have hlim : (fun ω => ENNReal.ofReal ((doleansDensity P 𝓕 B θ T ω) ^ 2))
      =ᵐ[P] fun ω => liminf (fun k => ENNReal.ofReal ((f k ω) ^ 2)) atTop := by
    filter_upwards [hms] with ω hω
    exact (((ENNReal.continuous_ofReal.tendsto _).comp (hω.1.pow 2)).liminf_eq).symm
  have hlint : ∫⁻ ω, ENNReal.ofReal ((doleansDensity P 𝓕 B θ T ω) ^ 2) ∂P ≤
      ENNReal.ofReal (Real.exp (C ^ 2 * T)) := by
    rw [lintegral_congr_ae hlim]
    exact (lintegral_liminf_le fun k => ENNReal.measurable_ofReal.comp ((hmeas k).pow_const 2)).trans
      ((liminf_le_liminf (Eventually.of_forall hbnd)).trans (liminf_const _).le)
  rw [← ofReal_integral_eq_lintegral_ofReal hZint (ae_of_all _ fun _ => sq_nonneg _)] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 hlint

/-- The Girsanov measure of an event is the set integral of the density. -/
theorem girsanovMeasure_real_eq (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet A) :
    (girsanovMeasure P 𝓕 B θ T).real A = ∫ ω in A, doleansDensity P 𝓕 B θ T ω ∂P := by
  have hZint := (memLp_doleansDensity (B := B) hθm hθb hθreg T).integrable one_le_two
  rw [measureReal_def, girsanovMeasure, withDensity_apply _ hA,
    ← ofReal_integral_eq_lintegral_ofReal hZint.integrableOn
      (ae_of_all _ fun ω => (doleansDensity_pos T ω).le),
    ENNReal.toReal_ofReal (setIntegral_nonneg hA fun ω _ => (doleansDensity_pos T ω).le)]

/-- **(5.6), Cauchy–Schwarz** (proof of Lemma 5.10): for every event `A`,
`ℙ̂(A)² ≤ ℙ(A) · 𝔼[Z_T²] ≤ ℙ(A) · exp(C² T)`, where `ℙ̂ = Z_T · ℙ` is the Girsanov measure. -/
theorem girsanovMeasure_real_sq_le (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet A) :
    ((girsanovMeasure P 𝓕 B θ T).real A) ^ 2 ≤ P.real A * Real.exp (C ^ 2 * (T : ℝ)) := by
  rw [girsanovMeasure_real_eq (B := B) hθm hθb hθreg T hA]
  have hZ := memLp_doleansDensity (B := B) hθm hθb hθreg T
  have hZint := (memLp_two_iff_integrable_sq hZ.aestronglyMeasurable).mp hZ
  calc (∫ ω in A, doleansDensity P 𝓕 B θ T ω ∂P) ^ 2
      ≤ ((P.restrict A) univ).toReal * ∫ ω in A, (doleansDensity P 𝓕 B θ T ω) ^ 2 ∂P :=
        MathFin.sq_integral_le_measureReal_mul (hZ.restrict A)
    _ ≤ P.real A * ∫ ω, (doleansDensity P 𝓕 B θ T ω) ^ 2 ∂P := by
        rw [Measure.restrict_apply_univ, ← measureReal_def]
        exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral hZint (ae_of_all _ fun _ => sq_nonneg _)) measureReal_nonneg
    _ ≤ P.real A * Real.exp (C ^ 2 * (T : ℝ)) :=
        mul_le_mul_of_nonneg_left (integral_sq_doleansDensity_le (B := B) hθm hθb hθreg T)
          measureReal_nonneg

/-- **The transfer of a lower bound** (proof of Lemma 5.10, "rearranging (5.6), we obtain
`ℙ[A] ≥ C₀^{-1} ℙ̂[A]²`"): `exp(−C² T) ℙ̂(A)² ≤ ℙ(A)`. -/
theorem le_measureReal_of_girsanov (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet A) :
    Real.exp (-(C ^ 2 * (T : ℝ))) * ((girsanovMeasure P 𝓕 B θ T).real A) ^ 2 ≤ P.real A := by
  have h := girsanovMeasure_real_sq_le (B := B) hθm hθb hθreg T hA
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_comm]
  exact h

/-- **The corrected crossing estimate** of Lemma 5.10 (p. 141): if the removed drift `D` satisfies `|D| ≤ C` and
`θ = −κ^{-1/2} D` (so `|θ| ≤ C/√κ`), then on the horizon `T = 1`,
`ℙ(A) ≥ e^{−C²/κ} ℙ̂(A)²`. -/
theorem le_measureReal_of_girsanov_drift {κ : ℝ} (hκ : 0 < κ) {D : ℝ≥0 → Ω → ℝ}
    (hθ : θ = fun t ω => -(Real.sqrt κ)⁻¹ * D t ω) (hθm : StronglyAdapted 𝓕 θ) {C : ℝ}
    (hDb : ∀ t ω, |D t ω| ≤ C) (hθreg : IsRiemannRegular P θ) {A : Set Ω} (hA : MeasurableSet A) :
    Real.exp (-(C ^ 2 / κ)) * ((girsanovMeasure P 𝓕 B θ 1).real A) ^ 2 ≤ P.real A := by
  have hs := Real.sqrt_pos.2 hκ
  have hθb : ∀ t ω, |θ t ω| ≤ C / Real.sqrt κ := by
    intro t ω
    rw [hθ, abs_mul, abs_neg, abs_inv, abs_of_pos hs, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hDb t ω) hs.le
  have h := le_measureReal_of_girsanov (B := B) hθm hθb hθreg 1 hA
  rwa [NNReal.coe_one, mul_one, div_pow, Real.sq_sqrt hκ.le] at h

end Density

section Evolution

variable [IsProbabilityMeasure P] {B W : ℝ≥0 → Ω → ℝ} {τ ζ : Ω → ℝ≥0∞}

/-- **The transfer for a cut drift.** For the drift `θ = cutDrift τ ζ F W U` of a bounded continuous `F`
(`|F| ≤ M`) cut at a stopping time `τ ≤ ζ ∧ T`, and the Girsanov measure `ℙ̂ = Z_{T+1} · ℙ` of
`Girsanov.girsanov_cutDrift`: `exp(−M²(T + 1)) ℙ̂(A)² ≤ ℙ(A)` for every event `A`. -/
theorem le_measureReal_of_girsanov_cutDrift {m : ℕ} (hBF : IsFilteredBrownianReal 𝓕 B P)
    {F : ℝ → (Fin m → ℝ) → ℝ} (hF : Continuous fun p : ℝ × (Fin m → ℝ) => F p.1 p.2) {M : ℝ}
    (hFb : ∀ w u, |F w u| ≤ M) {U : Fin m → ℝ≥0 → Ω → ℝ} (hW : AdaptedBefore 𝓕 ζ W)
    (hU : ∀ j, AdaptedBefore 𝓕 ζ (U j)) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ j, ContinuousOn (fun s => U j s ω) {s | (s : ℝ≥0∞) < ζ ω}) (T : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet A) :
    Real.exp (-(M ^ 2 * ((T + 1 : ℝ≥0) : ℝ))) *
        ((girsanovMeasure P 𝓕 B (cutDrift τ ζ F W U) (T + 1)).real A) ^ 2 ≤ P.real A := by
  have := isFilteredPreBrownian_of_isFilteredBrownianReal hBF
  exact le_measureReal_of_girsanov (B := B) (isStronglyProgressive_cutDrift hF hW hU hτ).stronglyAdapted
    (abs_cutDrift_le (τ := τ) (ζ := ζ) (W := W) (U := U) hFb)
    (isRiemannRegular_cutDrift (P := P) hF hτζ hcont) (T + 1) hA

/-- **Lemma 5.10's transfer at the evolution level.** Let `(W, V, B)` be an integrated `SLE_κ(ρ)` evolution and
remove the marks `SL`, `SR` by `Girsanov.girsanov_remove_forcePoints` up to a stopping time `τ ≤ ζ ∧ T` before
which they stay at distance `≥ δ > 0` from the driver; under the resulting measure `ℙ̂` the driver follows the
equation of the remaining word. Then for every event `A`,
`exp(−((∑ |removed weights|)/(√κ δ))² (T + 1)) ℙ̂(A)² ≤ ℙ(A)` ("`ℙ[A] ≥ C₀^{-1} ℙ̂[A]²`", with `C₀` depending only on
the drift bound, `κ` and the horizon). -/
theorem le_measureReal_of_remove_forcePoints {κ : ℝ} {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (SL : Finset (Fin nL))
    (SR : Finset (Fin nR)) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) (T : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) {A : Set Ω} (hA : MeasurableSet A) :
    Real.exp (-((|(-1 : ℝ) / Real.sqrt κ| * ((∑ j, |removedWeights ρL ρR SL SR j|) * δ⁻¹)) ^ 2 *
        ((T + 1 : ℝ≥0) : ℝ))) *
      ((girsanovMeasure P 𝓕 B
        (shiftDrift κ (-1) δ (removedWeights ρL ρR SL SR) τ ζ W (allMarks VL VR)) (T + 1)).real A) ^ 2
      ≤ P.real A := by
  obtain ⟨hBF, hW, hVL, hVR, hpath⟩ := hE
  have hU : ∀ k, AdaptedBefore 𝓕 ζ (allMarks VL VR k) := fun k => by
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hVL i
    | right i => simpa [allMarks] using hVR i
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => W s ω) {s | (s : ℝ≥0∞) < ζ ω} ∧
      ∀ k, ContinuousOn (fun s => allMarks VL VR k s ω) {s | (s : ℝ≥0∞) < ζ ω} := by
    filter_upwards [hpath] with ω hp
    refine ⟨hp.2.2.2.1, fun k => ?_⟩
    cases k using Fin.addCases with
    | left i => simpa [allMarks] using hp.2.2.2.2.1 i
    | right i => simpa [allMarks] using hp.2.2.2.2.2.1 i
  have hF : Continuous fun p : ℝ × (Fin (nL + nR) → ℝ) =>
      shiftIntegrand κ (-1) δ (removedWeights ρL ρR SL SR) p.1 p.2 :=
    continuous_const.mul (continuous_addedDriftCut _ hδ)
  have hFb : ∀ w u, |shiftIntegrand κ (-1) δ (removedWeights ρL ρR SL SR) w u| ≤
      |(-1 : ℝ) / Real.sqrt κ| * ((∑ j, |removedWeights ρL ρR SL SR j|) * δ⁻¹) := fun w u => by
    rw [shiftIntegrand, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (abs_addedDriftCut_le _ hδ w u) (abs_nonneg _)
  exact le_measureReal_of_girsanov_cutDrift hBF hF hFb hW hU hτ hτζ hcont T hA

end Evolution

end Sec5

end InteractingSLE
