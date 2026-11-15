/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71GLaw

/-!
# Lemma 7.1's pocket: the three-curve law given a σ-algebra enlarged by a full-measure event

Packet PROVE-LEMMA71J (specification §7.1, proof of Lemma 7.1, pp. 224–225). The pocket chart of Lemma 7.1 is a
measurable function of the outer curves only on the almost-sure event `Good` where the planar facts hold (simple,
ordered, no common arc: `Lemma71I.ae_isOrderedArcs`); off it a fixed default chart is used. The σ-algebra `𝓐₀` of the
pinned pocket statement (`Lemma71F.Lemma71PocketPinStatement`) is therefore taken to be the outer-curve σ-algebra
together with the event `Good`, and the three-curve law (`Lemma71G.ae_condExp_exp_eq_three_of_le`) is needed for every
`𝒢 ≤ (germs ⊔ labelled histories) ⊔ σ(Good)`. A full-measure event changes no conditional expectation:

* `condExp_ae_eq_of_le_aeSigma`: if `𝒦 ≤ 𝒦' ≤ mΩ` and every `𝒦'`-set is almost surely a `𝒦`-set, then
  `P[f | 𝒦'] = P[f | 𝒦]` almost surely;
* `sup_generateFrom_le_aeSigma`: `𝒦 ⊔ σ(G₀) ≤ aeSigma 𝒦 P` for a full-measure `G₀`;
* `condExp_ae_eq_on_of_le_sup`: the tower property on an event (`Sec6.condExp_ae_eq_on_of_le`) for
  `𝒢 ≤ 𝒦 ⊔ σ(G₀)`;
* **`ae_condExp_exp_eq_three_of_le_good`**: `Lemma71G.ae_condExp_exp_eq_three_of_le` for `𝒢 ≤ (germSigma A(τ) ⊔
  stoppedHistSigma) ⊔ σ(G₀)`, `G₀` measurable of full measure (same proof, one more step).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71Pin

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open Sec6 LocalSets Lemma71G

section CondExp

variable {Ω : Type*} {𝒢 𝒦 𝒦' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **Conditional expectations do not see null sets.** If `𝒦 ≤ 𝒦' ≤ mΩ` and every `𝒦'`-set is almost surely equal
to a `𝒦`-set, then `P[f | 𝒦'] = P[f | 𝒦]` almost surely. -/
theorem condExp_ae_eq_of_le_aeSigma (h𝒦 : 𝒦 ≤ mΩ) (h𝒦𝒦' : 𝒦 ≤ 𝒦') (h𝒦' : 𝒦' ≤ mΩ)
    (hae : 𝒦' ≤ aeSigma 𝒦 P) (f : Ω → ℂ) : P[f | 𝒦'] =ᵐ[P] P[f | 𝒦] := by
  by_cases hf : Integrable f P
  · refine (ae_eq_condExp_of_forall_setIntegral_eq h𝒦' hf (fun s _ _ => integrable_condExp.integrableOn)
      (fun s hs _ => ?_) ((stronglyMeasurable_condExp.mono h𝒦𝒦').aestronglyMeasurable)).symm
    obtain ⟨t, ht, hst⟩ := hae s hs
    rw [setIntegral_congr_set hst, setIntegral_condExp h𝒦 hf ht, setIntegral_congr_set hst]
  · rw [condExp_of_not_integrable hf, condExp_of_not_integrable hf]

omit [IsProbabilityMeasure P] in
/-- Adding a full-measure event to `𝒦` only adds sets that are almost surely `𝒦`-sets. -/
theorem sup_generateFrom_le_aeSigma {G₀ : Set Ω} (hG₀ : ∀ᵐ ω ∂P, ω ∈ G₀) :
    𝒦 ⊔ MeasurableSpace.generateFrom {G₀} ≤ aeSigma 𝒦 P := by
  refine sup_le (le_aeSigma 𝒦 P) (MeasurableSpace.generateFrom_le fun s hs => ?_)
  rw [mem_singleton_iff] at hs
  subst hs
  refine ⟨univ, MeasurableSet.univ, ?_⟩
  filter_upwards [hG₀] with ω hω
  simp [hω]

/-- **The tower property on an event, up to a full-measure event**: `Sec6.condExp_ae_eq_on_of_le` for
`𝒢 ≤ 𝒦 ⊔ σ(G₀)` with `G₀` measurable of full measure. -/
theorem condExp_ae_eq_on_of_le_sup {G₀ : Set Ω} (hG₀m : MeasurableSet G₀) (hG₀ : ∀ᵐ ω ∂P, ω ∈ G₀)
    (h𝒢 : 𝒢 ≤ 𝒦 ⊔ MeasurableSpace.generateFrom {G₀}) (h𝒦 : 𝒦 ≤ mΩ) {X Y : Ω → ℂ} (hX : Integrable X P)
    (hY : StronglyMeasurable[𝒢] Y) (hYi : Integrable Y P) {G : Set Ω} (hG : MeasurableSet[𝒢] G)
    (hXY : ∀ᵐ ω ∂P, ω ∈ G → P[X | 𝒦] ω = Y ω) : ∀ᵐ ω ∂P, ω ∈ G → P[X | 𝒢] ω = Y ω := by
  have hle : 𝒦 ⊔ MeasurableSpace.generateFrom {G₀} ≤ mΩ :=
    sup_le h𝒦 (MeasurableSpace.generateFrom_le fun s hs => by rw [mem_singleton_iff.1 hs]; exact hG₀m)
  have heq := condExp_ae_eq_of_le_aeSigma h𝒦 le_sup_left hle (sup_generateFrom_le_aeSigma hG₀) X
  refine condExp_ae_eq_on_of_le h𝒢 hle hX hY hYi hG ?_
  filter_upwards [heq, hXY] with ω h1 h2 hω
  rw [h1, h2 hω]

end CondExp

section Law

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {β α γ : Ω → ℝ≥0 → ℂ} {τ : Ω → ℝ≥0∞}
  {S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- **The three-curve law given any `𝒢 ≤` (germs ∨ labelled histories) ∨ a full-measure event**
(`Lemma71G.ae_condExp_exp_eq_three_of_le` with `σ(G₀)` added, `G₀` measurable of full measure; same proof, the tower
step by `condExp_ae_eq_on_of_le_sup`). -/
theorem ae_condExp_exp_eq_three_of_le_good
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hc : ∀ i ω, Continuous (Three.threeCurves β α γ i ω)) (h0 : ∀ i ω, Three.threeCurves β α γ i ω 0 = 0)
    (him : ∀ i ω t, 0 ≤ (Three.threeCurves β α γ i ω t).im)
    (hηm : ∀ i t, Measurable fun ω => Three.threeCurves β α γ i ω t)
    (hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => Three.threeCurves β α γ i ω t) =ᵐ[P] fun ω => f (h ω))
    (hloc : ∀ i, IsEntranceHistoryLocal (Three.threeCurves β α γ i) h P)
    (htr : ∀ᵐ ω ∂P, ∀ i, Tendsto (Three.threeCurves β α γ i ω) atTop (Bornology.cobounded ℂ))
    (hSm : Measurable fun z : (Hist × Hist) × (ℚ≥0 → ℂ) => S z.1.1 z.1.2 z.2)
    (hSg : ∀ x y c c', (∀ q : ℚ≥0, (((q : ℝ≥0) : ℝ≥0∞) ≤ S x y c) → c q = c' q) → S x y c' = S x y c)
    (hτ : ∀ ω, τ ω = S (histOf (pathCoord (β ω)) ⊤) (histOf (pathCoord (α ω)) ⊤) (pathCoord (γ ω)))
    {gS gL gT : Ω → DistOn upperHalfPlaneOpens}
    (hgS : IsLocalSetMean (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h P gS)
    (hgL : IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) h P gL)
    (hgT : IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i) h P gT)
    {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H) (hFb : ∃ M : ℝ, ∀ z ∈ H, |F z| ≤ M) (χ : ℝ)
    (φ : TestOn upperHalfPlaneOpens)
    {G₀ : Set Ω} (hG₀m : MeasurableSet G₀) (hG₀ : ∀ᵐ ω ∂P, ω ∈ G₀)
    (h𝒢 : 𝒢 ≤ (germSigma (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h ⊔
      stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ)) ⊔ MeasurableSpace.generateFrom {G₀})
    {E : Set Ω} (hE : MeasurableSet[𝒢] E) {M V : Ω → ℝ} (hM : Measurable[𝒢] M) (hV : Measurable[𝒢] V)
    (hprem : ∀ᵐ ω ∂P, ω ∈ E → IsThreeChartPremise
      (explored (Three.threeCurves β α γ) (Three.threeStops τ) ω)
      (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
      (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) F χ φ
      (M ω) (V ω)) :
    ∀ᵐ ω ∂P, ω ∈ E → P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * V ω) : ℝ) : ℂ) := by
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
    have hle' : (germSigma (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h ⊔
        stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ)) ⊔ MeasurableSpace.generateFrom {G₀} ≤
        mΩ := sup_le hle (MeasurableSpace.generateFrom_le fun s hs => by rw [mem_singleton_iff.1 hs]; exact hG₀m)
    refine Integrable.of_bound ((hYm.mono (h𝒢.trans hle') le_rfl).aestronglyMeasurable) 1
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
  filter_upwards [condExp_ae_eq_on_of_le_sup hG₀m hG₀ h𝒢 hle hX hYm.stronglyMeasurable hYi hE hXY, hprem, hopen]
    with ω hω hpr hωo hmem
  obtain ⟨z₀, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hVω⟩ := hpr hmem
  have hV0 : 0 ≤ V ω := by
    rw [← hVω]
    exact zeroGFFTestCov_self_nonneg hωo.connectedComponentIn
      ((connectedComponentIn_subset _ _).trans sdiff_subset) φ
  rw [hω hmem]
  simp only [hYdef, max_eq_left hV0]

end Law

end InteractingSLE.Sec7.Lemma71Pin
