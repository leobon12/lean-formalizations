/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71GSpace
import InteractingSLE.Spec.Sec7.TwoForceRestart

/-!
# Lemma 7.1: the three-curve law given a smaller σ-algebra (forgetting the germs)

Packet PROVE-LEMMA71G, part (B), step 3 (specification §7.1, proof of Lemma 7.1, pp. 224–225,
`source/spec/p193-240.md` L600–L602: "For each bounded stopping time of this mapped path, the history-locality
statement of Lemma 6.2 applies to the revealed outer curves and the middle prefix […] The means in all the remaining
components are those of the three-curve result in Remark 6.7"; and p. 154 for the forgetting of the germs: "Once the
mean below has been identified, it and the residual covariance are functions of the labeled pair, so the same
Gaussian law holds after those germs are forgotten").

The landed three-curve form of Lemma 6.2 (`Sec6.Three.ae_condExp_exp_eq_three_of_tendsto`) gives the conditional
characteristic function of the field given the germs of `A(τ) = β ∪ α ∪ γ([0, τ])` **and** the three labeled
histories. The fixed-time coupling clause of Lemma 7.1 conditions on the smaller prefix filtration (the complete outer
curves and the mapped middle prefix). This file passes the law to every `𝒢 ≤ germSigma A(τ) ⊔ stoppedHistSigma`:

* `IsThreeChartPremise`: the premise of the three-curve law at one realization — a component of `ℍ ∖ A(τ)` containing
  the support of `φ`, harmonic representatives of the three comparison means, a chart of Aux. lemma 28 with finite
  exceptional set and the prime-end boundary values — together with the values `M` (the mean pairing
  `∫ (G ∘ φ_C − χ L) φ`) and `V` (the zero-boundary variance of the component);
* **`ae_condExp_exp_eq_three_of_le`**: given any `𝒢 ≤ germSigma A(τ) ⊔ stoppedHistSigma`, a `𝒢`-event `E` and
  `𝒢`-measurable `M, V` such that the premise holds almost surely on `E`,
  `E[e^{i(h + F)(φ)} | 𝒢] = e^{iM} e^{−V/2}` almost surely on `E`;
* `measurable_outer_stoppedHistSigma`: the complete outer curves are measurable for the labeled histories (the
  first ingredient of `prefixFiltrationOf 𝓐₀ γ t ≤ germSigma A(τ_t) ⊔ stoppedHistSigma` with `𝓐₀ = σ(β, α)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71G

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open Sec6 LocalSets

/-- **The premise of the three-curve law at one realization**, with the values `M` of the mean pairing and `V` of the
variance. `A`, `AL`, `AT` are the explored set, the full union and the outer union; `gS`, `gL`, `gT` their local-set
means at this realization; `F` the harmonic shift of the field and `χ` the coefficient of the argument lift. -/
def IsThreeChartPremise (A AL AT : Set ℂ) (gS gL gT : DistOn upperHalfPlaneOpens) (F : ℂ → ℝ) (χ : ℝ)
    (φ : TestOn upperHalfPlaneOpens) (M V : ℝ) : Prop :=
  ∃ z₀ ∈ H \ A, tsupport φ ⊆ connectedComponentIn (H \ A) z₀ ∧
    ∃ v vL vT : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A) ∧
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ A → gS ψ = ∫ x, v x * ψ x) ∧
      InnerProductSpace.HarmonicOnNhd vL (H \ AL) ∧
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ AL → gL ψ = ∫ x, vL x * ψ x) ∧
      InnerProductSpace.HarmonicOnNhd vT (H \ AT) ∧
      (∀ ψ : TestOn upperHalfPlaneOpens, tsupport ψ ⊆ H \ AT → gT ψ = ∫ x, vT x * ψ x) ∧
    ∃ (f φc : ℂ → ℂ) (G Lc : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ A) z₀) ∧
      IsConformalBijection φc (connectedComponentIn (H \ A) z₀) {w : ℂ | 0 < w.im} ∧
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} ∧ (∃ M', ∀ w : ℂ, 0 < w.im → |G w| ≤ M') ∧
      ContinuousOn Lc (connectedComponentIn (H \ A) z₀) ∧
      (∀ z ∈ connectedComponentIn (H \ A) z₀, deriv φc z = ‖deriv φc z‖ * exp (Lc z * I)) ∧ E.Finite ∧
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E → ∃ p : ℂ, Tendsto f (𝓝[ball 0 1] q) (𝓝 p) ∧
        ((p ∈ A ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, AL ∩ ball p r ⊆ A) ∧
            Tendsto (fun ζ => (vL (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) ∨
          (p ∈ AT ∪ {z : ℂ | z.im = 0} ∧ (∃ r > 0, A ∩ ball p r ⊆ AT) ∧
            Tendsto (fun ζ => (vT (f ζ) + F (f ζ)) - (G (φc (f ζ)) - χ * Lc (f ζ))) (𝓝[ball 0 1] q)
              (𝓝 0)))) ∧
      (∫ x, (G (φc x) - χ * Lc x) * φ x) = M ∧
      QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ A) z₀) φ φ = V

section Law

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {β α γ : Ω → ℝ≥0 → ℂ} {τ : Ω → ℝ≥0∞}
  {S : Hist → Hist → (ℚ≥0 → ℂ) → ℝ≥0∞}

/-- **The three-curve law given any `𝒢 ≤` germs ∨ labeled histories** (Remark 6.7 stopped, with the germs and part of
the histories forgotten). Hypotheses of `Sec6.Three.ae_condExp_exp_eq_three_of_tendsto`; `𝒢 ≤ germSigma A(τ) ⊔
stoppedHistSigma`, `E ∈ 𝒢`, `M, V` `𝒢`-measurable, and almost surely on `E` the premise holds with the values `M, V`.
Then almost surely on `E`, `E[e^{i(h + F)(φ)} | 𝒢] = e^{iM} e^{−V/2}`. -/
theorem ae_condExp_exp_eq_three_of_le
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
    (h𝒢 : 𝒢 ≤ germSigma (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h ⊔
      stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ))
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
    refine Integrable.of_bound ((hYm.mono (h𝒢.trans hle) le_rfl).aestronglyMeasurable) 1
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
  filter_upwards [condExp_ae_eq_on_of_le h𝒢 hle hX hYm.stronglyMeasurable hYi hE hXY, hprem, hopen]
    with ω hω hpr hωo hmem
  obtain ⟨z₀, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hVω⟩ := hpr hmem
  have hV0 : 0 ≤ V ω := by
    rw [← hVω]
    exact zeroGFFTestCov_self_nonneg hωo.connectedComponentIn
      ((connectedComponentIn_subset _ _).trans sdiff_subset) φ
  rw [hω hmem]
  simp only [hYdef, max_eq_left hV0]

/-- `ae_condExp_exp_eq_three_of_le` with the curve hypotheses given by `IsLemma62Curve` for each curve (the form in
which `exists_threeCurveSpace` supplies them). -/
theorem ae_condExp_exp_eq_three_of_le_of_isLemma62Curve
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
    (φ : TestOn upperHalfPlaneOpens)
    (h𝒢 : 𝒢 ≤ germSigma (explored (Three.threeCurves β α γ) (Three.threeStops τ)) h ⊔
      stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ))
    {E : Set Ω} (hE : MeasurableSet[𝒢] E) {M V : Ω → ℝ} (hM : Measurable[𝒢] M) (hV : Measurable[𝒢] V)
    (hprem : ∀ᵐ ω ∂P, ω ∈ E → IsThreeChartPremise
      (explored (Three.threeCurves β α γ) (Three.threeStops τ) ω)
      (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω)
      (explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) (gS ω) (gL ω) (gT ω) F χ φ
      (M ω) (V ω)) :
    ∀ᵐ ω ∂P, ω ∈ E → P[fun ω' => cexp (I * ((h ω' φ + ∫ x, F x * φ x : ℝ) : ℂ)) | 𝒢] ω =
      cexp (I * (M ω : ℂ)) * ((Real.exp (-(1 / 2) * V ω) : ℝ) : ℂ) := by
  obtain ⟨hc, h0, him, hηm, hdet, hloc, htr⟩ := IsLemma62Curve.three hβ hα hγ
  exact ae_condExp_exp_eq_three_of_le hh hc h0 him hηm hdet hloc htr hSm hSg hτ hgS hgL hgT hF hFb χ φ h𝒢 hE hM hV
    hprem

end Law

/-! ### The complete outer curves are part of the labeled histories -/

section Outer

variable {Ω : Type*} {β α γ : Ω → ℝ≥0 → ℂ} {τ : Ω → ℝ≥0∞}

/-- **The complete outer curves are measurable for the labeled histories** (their stops are `∞`): for `i ≠ 2` and a
curve continuous for every `ω`, `ω ↦ η_i(ω, t)` is `stoppedHistSigma`-measurable (limit along rational times). -/
theorem measurable_outer_stoppedHistSigma {i : Fin 3} (hi : i ≠ 2)
    (hc : ∀ ω, Continuous (Three.threeCurves β α γ i ω)) (t : ℝ≥0) :
    Measurable[stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ)]
      fun ω => Three.threeCurves β α γ i ω t := by
  have htop : ∀ ω, Three.threeStops τ i ω = ⊤ := fun ω => by
    fin_cases i
    · rfl
    · rfl
    · exact absurd rfl hi
  obtain ⟨q, hq⟩ := exists_seq_nnrat_tendsto t
  have hqm : ∀ n, Measurable[stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ)]
      fun ω => Three.threeCurves β α γ i ω (q n : ℝ≥0) := fun n => by
    have hY := comap_measurable (m := (inferInstance : MeasurableSpace (Fin 3 → Hist)))
      (fun ω i => histOf (pathCoord (Three.threeCurves β α γ i ω)) (Three.threeStops τ i ω))
    have h1 := (measurable_pi_apply (q n)).comp (measurable_snd.comp ((measurable_pi_apply i).comp hY))
    have e : (fun ω => Three.threeCurves β α γ i ω (q n : ℝ≥0)) = (fun f : ℚ≥0 → ℂ => f (q n)) ∘ Prod.snd ∘
        (fun f : Fin 3 → Hist => f i) ∘
          fun ω i => histOf (pathCoord (Three.threeCurves β α γ i ω)) (Three.threeStops τ i ω) := by
      funext ω
      simp only [Function.comp_apply, histOf, htop ω]
      rw [stopCoord_of_le le_top]
      rfl
    rw [e]
    exact h1
  let _ : MeasurableSpace Ω := stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops τ)
  exact measurable_of_tendsto_metrizable hqm (tendsto_pi_nhds.2 fun ω => ((hc ω).tendsto t).comp hq)

end Outer

end InteractingSLE.Sec7.Lemma71G
