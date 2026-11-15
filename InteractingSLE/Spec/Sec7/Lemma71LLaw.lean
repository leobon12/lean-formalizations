/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71JLaw
import InteractingSLE.Spec.Sec7.Lemma71GSpace

/-!
# Lemma 7.1: the three-curve law given a σ-algebra inside the completed labelled histories

Packet PROVE-LEMMA71L. The prefix filtration of the mapped segment is contained in the labelled histories of the three
curves only up to null sets (`Lemma71L.prefixFiltrationOf_le_aeSigma`). This file passes the stopped three-curve law of
Remark 6.7 (`Lemma71G.ae_condExp_exp_eq_three_of_le`, PROVE-LEMMA71G/J) to every `𝒢 ≤ mΩ` with
`𝒢 ≤ aeSigma (germs ∨ labelled histories) P` (`ae_condExp_exp_eq_three_of_le_aeSigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal Real
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.Lemma71L

open Sec6 LocalSets Lemma71G

section CondExp

variable {Ω : Type*} {𝒢 𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The tower property on an event for `𝒢` inside the completion of `𝒦`.** -/
theorem condExp_ae_eq_on_of_le_aeSigma (h𝒢m : 𝒢 ≤ mΩ) (h𝒢 : 𝒢 ≤ aeSigma 𝒦 P) (h𝒦 : 𝒦 ≤ mΩ) {X Y : Ω → ℂ}
    (hX : Integrable X P) (hY : StronglyMeasurable[𝒢] Y) (hYi : Integrable Y P) {G : Set Ω}
    (hG : MeasurableSet[𝒢] G) (hXY : ∀ᵐ ω ∂P, ω ∈ G → P[X | 𝒦] ω = Y ω) :
    ∀ᵐ ω ∂P, ω ∈ G → P[X | 𝒢] ω = Y ω := by
  have hle : 𝒦 ⊔ 𝒢 ≤ mΩ := sup_le h𝒦 h𝒢m
  have hae : 𝒦 ⊔ 𝒢 ≤ aeSigma 𝒦 P := sup_le (le_aeSigma 𝒦 P) h𝒢
  have heq := Lemma71Pin.condExp_ae_eq_of_le_aeSigma h𝒦 le_sup_left hle hae X
  refine Sec6.condExp_ae_eq_on_of_le (le_sup_right : 𝒢 ≤ 𝒦 ⊔ 𝒢) hle hX hY hYi hG ?_
  filter_upwards [heq, hXY] with ω h1 h2 hω
  rw [h1, h2 hω]

end CondExp

section Law

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {β α γ : Ω → ℝ≥0 → ℂ} {τ : Ω → ℝ≥0∞}
  {S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- **The three-curve law given any `𝒢 ≤ mΩ` inside the completion of germs ∨ labelled histories**
(`Lemma71Pin.ae_condExp_exp_eq_three_of_le_good`, same proof, the tower step by
`condExp_ae_eq_on_of_le_aeSigma`; curve hypotheses in `IsLemma62Curve` form). -/
theorem ae_condExp_exp_eq_three_of_le_aeSigma
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hβ : IsLemma62Curve β h P) (hα : IsLemma62Curve α h P) (hγ : IsLemma62Curve γ h P)
    (hSm : Measurable fun z : (Hist × Hist) × (ℚ≥0 → ℂ) => S z.1.1 z.1.2 z.2)
    (hSg : ∀ x y c c', (∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ S x y c) → c q = c' q) → S x y c' = S x y c)
    (hτ : ∀ ω, τ ω = S (histOf (pathCoord (β ω)) ⊤) (histOf (pathCoord (α ω)) ⊤) (pathCoord (γ ω)))
    {gS gL gT : Ω → DistOn upperHalfPlaneOpens}
    (hgS : IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h P gS)
    (hgL : IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) h P gL)
    (hgT : IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i) h P gT)
    {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ)
    (φ : TestOn upperHalfPlaneOpens) (h𝒢m : 𝒢 ≤ mΩ)
    (h𝒢 : 𝒢 ≤ aeSigma (germSigma (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h ⊔
      stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ)) P)
    {E : Set Ω} (hE : MeasurableSet[𝒢] E) {M V : Ω → ℝ} (hM : Measurable[𝒢] M) (hV : Measurable[𝒢] V)
    (hprem : ∀ᵐ ω ∂P, ω ∈ E → IsThreeChartPremise
      (explored (Three.threeCurves β α γ) (Three.threeStops τ) ω)
      (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
      (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) F χ φ
      (M ω) (V ω)) :
    ∀ᵐ ω ∂P, ω ∈ E → P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * V ω) : ℝ) : ℂ) := by
  obtain ⟨hc, h0, him, hηm, hdet, hloc, htr⟩ := IsLemma62Curve.three hβ hα hγ
  have hhm := hh.measurable
  have hstops : ∀ i, Measurable (Three.threeStops τ i) :=
    measurable_of_galmarino hηm (Three.measurable_threeRule hSm) (Three.isGalmarino_threeRule hSg)
      (Three.threeStops_eq_threeRule hτ)
  have hle : germSigma (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h ⊔
      stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ) ≤ mΩ :=
    sup_le (germSigma_le (measurable_explored hc hηm hstops) hhm) (stoppedHistSigma_le hηm hstops)
  set Y : Ω → ℂ := fun ω => cexp (I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * max (V ω) 0) : ℝ) : ℂ)
    with hYdef
  have hYm : Measurable[𝒢] Y := by
    let _ : MeasurableSpace Ω := 𝒢
    exact (GFF.measurable_exp_I_mul hM).mul (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (hV.max measurable_const))))
  have hYi : Integrable Y P := by
    refine Integrable.of_bound ((hYm.mono h𝒢m le_rfl).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => ?_)
    rw [hYdef, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [le_max_right (V ω) 0]
  have hX : Integrable (fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ))) P :=
    GFF.integrable_exp_I_mul (((LQGMetric.measurable_distOn_apply φ).comp hhm).add_const _)
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ explored (Three.threeCurves β α γ) (Three.threeStops τ) ω) :=
    htr.mono fun ω hω => isOpen_H_diff_explored (fun i => hc i ω) hω
  have hXY : ∀ᵐ ω ∂P, ω ∈ E →
      P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) |
        germSigma (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h ⊔
          stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ)] ω = Y ω := by
    filter_upwards [Three.ae_condExp_exp_eq_three_of_tendsto hh hc h0 him hηm hdet hloc htr hSm hSg hτ hgS hgL
      hgT hF hFb χ φ, hprem, hopen] with ω hω hpr hωo hmem
    obtain ⟨z₀, hz₀, hφC, v, vL, vT, hv, hgv, hvL, hgvL, hvT, hgvT, f, φc, G, Lc, Ex, hf, hφc, hG, hGb, hLc,
      hder, hEx, hpe, hMω, hVω⟩ := hpr hmem
    have hV0 : 0 ≤ V ω := by
      rw [← hVω]
      exact zeroGFFTestCov_self_nonneg hωo.connectedComponentIn
        ((connectedComponentIn_subset _ _).trans sdiff_subset) φ
    rw [hω z₀ hz₀ hφC v vL vT hv hgv hvL hgvL hvT hgvT f φc G Lc Ex hf hφc hG hGb hLc hder hEx hpe, hMω, hVω]
    simp only [hYdef, max_eq_left hV0]
  filter_upwards [condExp_ae_eq_on_of_le_aeSigma h𝒢m h𝒢 hle hX hYm.stronglyMeasurable hYi hE hXY, hprem, hopen]
    with ω hω hpr hωo hmem
  obtain ⟨z₀, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hVω⟩ := hpr hmem
  have hV0 : 0 ≤ V ω := by
    rw [← hVω]
    exact zeroGFFTestCov_self_nonneg hωo.connectedComponentIn
      ((connectedComponentIn_subset _ _).trans sdiff_subset) φ
  rw [hω hmem]
  simp only [hYdef, max_eq_left hV0]

end Law

end InteractingSLE.Sec7.Lemma71L
