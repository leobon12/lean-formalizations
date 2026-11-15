/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AddMarksInverse

/-!
# Aux. lemma 62, probabilistic layer: events of bounded drift energy

Packet PROVE-GB7A2. Source: proof of Aux. lemma 62 (`source/spec/p241-288.md`, p. 263): "The full density is also
strictly positive, so the original and weighted laws, and hence their stopped path marginals, are mutually absolutely
continuous." In this project's field-free form the density of the comparison is the Doléans exponential of the drift
difference, which is not uniformly integrable along the whole approach to a boundary hit; only its *energy* is
controlled (`Aux61Cutoff.exists_markDrift_energy_le`). This file proves the transfer used instead: on an event where
the energy `∫ θ²` is at most `C`, the original probability is controlled by the Girsanov probability,

  `P(D) ≤ λ Q(D)/2 + e^C/(2λ)` for every `λ > 0` (`measureReal_le_of_quadInt_le`),

from `1 ≤ (λ Z + 1/(λ Z))/2`, `1/Z = Z⁻ e^{∫θ²}` with `Z⁻` the Doléans density of `−θ` (mean `1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace GB7a

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {B θ : ℝ≥0 → Ω → ℝ}

/-- `quadInt` is unchanged under `θ ↦ −θ`. -/
theorem quadInt_neg (t : ℝ≥0) (ω : Ω) : quadInt (fun s ω => -θ s ω) t ω = quadInt θ t ω := by
  simp only [quadInt, neg_sq]

/-- **The energy transfer**: for a bounded progressive Riemann-regular drift `θ`, the Girsanov measure
`Q = Z_T · P` and a measurable event `D` on which `∫₀ᵀ θ² ≤ C`, `P(D) ≤ λ Q(D)/2 + e^C/(2λ)` for every `λ > 0`. -/
theorem measureReal_le_of_quadInt_le (hB : IsFilteredPreBrownian B 𝓕 P) (hθ : IsStronglyProgressive 𝓕 θ)
    {Cθ : ℝ} (hθb : ∀ t ω, |θ t ω| ≤ Cθ) (hθreg : IsRiemannRegular P θ) (T : ℝ≥0) {D : Set Ω}
    (hD : MeasurableSet D) {C : ℝ} (hDC : ∀ ω ∈ D, quadInt θ T ω ≤ C) {lam : ℝ} (hlam : 0 < lam) :
    P.real D ≤ lam / 2 * (girsanovMeasure P 𝓕 B θ T).real D + Real.exp C / (2 * lam) := by
  have hθm := hθ.stronglyAdapted
  set Z := doleansDensity P 𝓕 B θ T with hZ
  set Z' := doleansDensity P 𝓕 B (fun s ω => -θ s ω) T with hZ'
  have hθ' : IsStronglyProgressive 𝓕 (fun s ω => -θ s ω) := fun t => (hθ t).neg
  have hθb' : ∀ t ω, |(fun s ω => -θ s ω) t ω| ≤ Cθ := fun t ω => by simp only [abs_neg]; exact hθb t ω
  have hθreg' : IsRiemannRegular P (fun s ω => -θ s ω) :=
    hθreg.mono fun ω hω => hω.mono fun u hu => hu.neg
  have hZm : StronglyMeasurable Z := (stronglyMeasurable_doleansDensity hθ hθb hθreg T).mono (𝓕.le T)
  have hZ'm : StronglyMeasurable Z' := (stronglyMeasurable_doleansDensity hθ' hθb' hθreg' T).mono (𝓕.le T)
  have hZpos : ∀ ω, 0 < Z ω := fun ω => doleansDensity_pos T ω
  have hZ'pos : ∀ ω, 0 < Z' ω := fun ω => doleansDensity_pos T ω
  have hZi : Integrable Z P := by
    have h1 := integral_doleansDensity (hB := hB) hθm hθb hθreg T
    exact integrable_of_integral_eq_one h1
  have hZ'i : Integrable Z' P := by
    have h1 := integral_doleansDensity (hB := hB) (fun t => (hθm t).neg) hθb' hθreg' T
    exact integrable_of_integral_eq_one h1
  have hZ'1 : ∫ ω, Z' ω ∂P = 1 := integral_doleansDensity (hB := hB) (fun t => (hθm t).neg) hθb' hθreg' T
  -- `1/Z = Z' e^{∫θ²}` almost surely
  have hneg := stochIntegral_neg_ae_eq hB hθm hθb hθreg T
  have hinv : ∀ᵐ ω ∂P, (Z ω)⁻¹ = Z' ω * Real.exp (quadInt θ T ω) := by
    filter_upwards [hneg] with ω hω
    simp only [hZ, hZ', doleansDensity, hω, quadInt_neg]
    rw [← Real.exp_neg, ← Real.exp_add]
    ring_nf
  -- the pointwise inequality `1 ≤ (λ Z + 1/(λ Z))/2`
  have hpt : ∀ ω, (1 : ℝ) ≤ lam / 2 * Z ω + (Z ω)⁻¹ / (2 * lam) := fun ω => by
    have hz := hZpos ω
    have h : 0 ≤ (lam * Z ω - 1) ^ 2 := sq_nonneg _
    rw [show lam / 2 * Z ω + (Z ω)⁻¹ / (2 * lam) = ((lam * Z ω) ^ 2 + 1) / (2 * (lam * Z ω)) by
      field_simp]
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- integrate over `D`
  have hQ : (girsanovMeasure P 𝓕 B θ T).real D = ∫ ω in D, Z ω ∂P := by
    rw [girsanovMeasure, measureReal_def, withDensity_apply _ hD,
      ← ofReal_integral_eq_lintegral_ofReal hZi.integrableOn (ae_of_all _ fun ω => (hZpos ω).le),
      ENNReal.toReal_ofReal (integral_nonneg fun ω => (hZpos ω).le)]
  have hinvD : ∫ ω in D, (Z ω)⁻¹ ∂P ≤ Real.exp C := by
    have h1 : ∫ ω in D, (Z ω)⁻¹ ∂P ≤ ∫ ω in D, Z' ω * Real.exp C ∂P := by
      refine setIntegral_mono_on_ae ?_ (hZ'i.mul_const _).integrableOn hD ?_
      · refine (hZ'i.mul_const (Real.exp C)).integrableOn.mono' (hZm.measurable.inv.aestronglyMeasurable)
          ((ae_restrict_iff' hD).2 ?_)
        filter_upwards [hinv] with ω hω hωD
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hZpos ω)), hω]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hDC ω hωD)) (hZ'pos ω).le
      · filter_upwards [hinv] with ω hω hωD
        rw [hω]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hDC ω hωD)) (hZ'pos ω).le
    refine h1.trans ?_
    rw [integral_mul_const]
    have h2 : ∫ ω in D, Z' ω ∂P ≤ 1 := by
      rw [← hZ'1]
      exact setIntegral_le_integral hZ'i (ae_of_all _ fun ω => (hZ'pos ω).le)
    nlinarith [Real.exp_pos C]
  have hinvi : IntegrableOn (fun ω => (Z ω)⁻¹) D P := by
    refine (hZ'i.mul_const (Real.exp C)).integrableOn.mono' (hZm.measurable.inv.aestronglyMeasurable)
      ((ae_restrict_iff' hD).2 ?_)
    filter_upwards [hinv] with ω hω hωD
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hZpos ω)), hω]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hDC ω hωD)) (hZ'pos ω).le
  calc P.real D = ∫ ω in D, (1 : ℝ) ∂P := by rw [setIntegral_const, smul_eq_mul, mul_one]
    _ ≤ ∫ ω in D, (lam / 2 * Z ω + (Z ω)⁻¹ / (2 * lam)) ∂P :=
        setIntegral_mono (integrable_const _).integrableOn
          ((hZi.integrableOn.const_mul _).add (hinvi.div_const _)) hpt
    _ = lam / 2 * (∫ ω in D, Z ω ∂P) + (∫ ω in D, (Z ω)⁻¹ ∂P) / (2 * lam) := by
        rw [integral_add (hZi.integrableOn.const_mul _) (hinvi.div_const _), integral_const_mul,
          integral_div]
    _ ≤ lam / 2 * (girsanovMeasure P 𝓕 B θ T).real D + Real.exp C / (2 * lam) := by
        rw [hQ]
        gcongr

end GB7a

end InteractingSLE
