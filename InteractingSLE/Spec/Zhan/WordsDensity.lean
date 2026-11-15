/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AddMarksInverse

/-!
# A uniform reverse density bound for Girsanov measures

Packet PROVE-ZHAN-B4. The whole-tail comparison of Astra §3 ("bounded-energy adapted Girsanov", L1572–L1584 of
`source/external/AstraIG1/ig1_formalization_proofs.txt`) needs equivalence of the original and the reference laws
with constants that do not depend on the horizon. Here this is proved in the following finite-horizon form: for the
Girsanov measure `Q = Z_T · P` of a bounded drift `θ` and an event `A` on which the energy `∫₀ᵀ θ²` is at most `m`,

  `P(F ∩ A) ≤ e^{m/2} Q(F)^{1/2}`  for every event `F`.

Proof: on `A`, `Z_T⁻¹ = exp(∫θ dB + ½∫θ²) = D_T(−θ) e^{∫θ²} ≤ e^m D_T(−θ)`, where `D(−θ)` is the Doléans density
of `−θ` (mean one); then Cauchy–Schwarz, `P(F ∩ A) = ∫_{F∩A} Z^{1/2} Z^{−1/2} dP`.

## Main results

* `lintegral_inv_doleansDensity_le`: `∫_A Z_T⁻¹ dP ≤ e^m`.
* `measure_inter_le_girsanov`: `P(F ∩ A) ≤ (e^m)^{1/2} Q(F)^{1/2}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-- **The inverse density on an event of bounded energy**: `∫_A Z_T⁻¹ dP ≤ e^m` when `∫₀ᵀ θ² ≤ m` on `A`. -/
theorem lintegral_inv_doleansDensity_le [IsProbabilityMeasure P] (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ)
    (T : ℝ≥0) {A : Set Ω} (hAm : MeasurableSet A) {m : ℝ} (hA : ∀ ω ∈ A, quadInt θ T ω ≤ m) :
    ∫⁻ ω in A, ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω)⁻¹ ∂P ≤ ENNReal.ofReal (Real.exp m) := by
  have := hB
  have hm' : StronglyAdapted 𝓕 (fun s ω => -θ s ω) := fun s => (hθm s).neg
  have hb' : ∀ s ω, |-θ s ω| ≤ C := fun s ω => by rw [abs_neg]; exact hθb s ω
  have hreg' : IsRiemannRegular P (fun s ω => -θ s ω) :=
    hθreg.mono fun ω hω => hω.mono fun u hu => hu.neg
  have hneg := stochIntegral_neg_ae_eq hB hθm hθb hθreg T
  have hint := (memLp_doleansDensity (B := B) hm' hb' hreg' T).integrable one_le_two
  have h1 := integral_doleansDensity (B := B) hm' hb' hreg' T
  have hkey : ∀ᵐ ω ∂P, ω ∈ A → ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω)⁻¹ ≤
      ENNReal.ofReal (Real.exp m) * ENNReal.ofReal (doleansDensity P 𝓕 B (fun s ω => -θ s ω) T ω) := by
    filter_upwards [hneg] with ω hω hωA
    rw [← ENNReal.ofReal_mul (Real.exp_pos m).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hq := hA ω hωA
    rw [doleansDensity, doleansDensity, hω, quadInt_neg, ← Real.exp_neg, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  have hone : ∫⁻ ω, ENNReal.ofReal (doleansDensity P 𝓕 B (fun s ω => -θ s ω) T ω) ∂P = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ω => (doleansDensity_pos T ω).le), h1, ENNReal.ofReal_one]
  calc ∫⁻ ω in A, ENNReal.ofReal (doleansDensity P 𝓕 B θ T ω)⁻¹ ∂P
      ≤ ∫⁻ ω in A, ENNReal.ofReal (Real.exp m) *
          ENNReal.ofReal (doleansDensity P 𝓕 B (fun s ω => -θ s ω) T ω) ∂P :=
        lintegral_mono_ae ((ae_restrict_iff' hAm).2 hkey)
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp m) *
          ENNReal.ofReal (doleansDensity P 𝓕 B (fun s ω => -θ s ω) T ω) ∂P :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (Real.exp m) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hone, mul_one]

/-- **The uniform reverse density bound**: for the Girsanov measure `Q = Z_T · P` of a bounded drift `θ` and a
measurable event `A` on which `∫₀ᵀ θ² ≤ m`, every measurable event `F` has `P(F ∩ A) ≤ (e^m)^{1/2} Q(F)^{1/2}`. -/
theorem measure_inter_le_girsanov [IsProbabilityMeasure P] (hB : IsFilteredPreBrownian B 𝓕 P)
    (hθm : StronglyAdapted 𝓕 θ) {C : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ C) (hθreg : IsRiemannRegular P θ)
    (T : ℝ≥0) {F A : Set Ω} (hF : MeasurableSet F) (hAm : MeasurableSet A) {m : ℝ}
    (hA : ∀ ω ∈ A, quadInt θ T ω ≤ m) :
    P (F ∩ A) ≤ ENNReal.ofReal (Real.exp m) ^ (1 / 2 : ℝ) *
      girsanovMeasure P 𝓕 B θ T F ^ (1 / 2 : ℝ) := by
  have := hB
  set Z : Ω → ℝ := doleansDensity P 𝓕 B θ T with hZ
  have hZpos : ∀ ω, 0 < Z ω := fun ω => doleansDensity_pos T ω
  have hZm : AEMeasurable Z (P.restrict (F ∩ A)) :=
    (memLp_doleansDensity (B := B) hθm hθb hθreg T).1.aemeasurable.restrict
  set f : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Z ω) ^ (1 / 2 : ℝ) with hf
  set g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Z ω)⁻¹ ^ (1 / 2 : ℝ) with hg
  have hfg : ∀ ω, (f * g) ω = 1 := fun ω => by
    simp only [Pi.mul_apply, hf, hg]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.ofReal_mul (hZpos ω).le,
      mul_inv_cancel₀ (hZpos ω).ne', ENNReal.ofReal_one, ENNReal.one_rpow]
  have hfm : AEMeasurable f (P.restrict (F ∩ A)) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hZm).pow_const _
  have hgm : AEMeasurable g (P.restrict (F ∩ A)) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hZm.inv).pow_const _
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (P.restrict (F ∩ A)) Real.HolderConjugate.two_two hfm hgm
  have hL : ∫⁻ ω, (f * g) ω ∂(P.restrict (F ∩ A)) = P (F ∩ A) := by
    simp only [hfg, lintegral_const, one_mul, Measure.restrict_apply_univ]
  have hsq : ∀ x : ℝ≥0∞, (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_mul]; norm_num
  have hf2 : ∫⁻ ω, f ω ^ (2 : ℝ) ∂(P.restrict (F ∩ A)) ≤ girsanovMeasure P 𝓕 B θ T F := by
    simp only [hf, hsq]
    rw [girsanovMeasure, withDensity_apply _ hF]
    exact lintegral_mono_set inter_subset_left
  have hg2 : ∫⁻ ω, g ω ^ (2 : ℝ) ∂(P.restrict (F ∩ A)) ≤ ENNReal.ofReal (Real.exp m) := by
    simp only [hg, hsq]
    exact (lintegral_mono_set inter_subset_right).trans
      (lintegral_inv_doleansDensity_le hB hθm hθb hθreg T hAm hA)
  rw [← hL]
  refine hH.trans ?_
  rw [mul_comm]
  gcongr

end InteractingSLE.Zhan
