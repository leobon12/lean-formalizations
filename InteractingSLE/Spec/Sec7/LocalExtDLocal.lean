/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtDTilt
import InteractingSLE.Spec.Coupling.Locality11Gauss
import InteractingSLE.Spec.Sobolev.GFFRegularity
import InteractingSLE.Spec.Sec7.LocalExtCKernel

/-!
# Step 5's locality: a Cameron–Martin tilt preserves local sets

Packet PROVE-LOCEXT-D, item 2. Source: Aux. lemma 55, proof (`source/spec/p241-288.md` L196–L210, p. 250): under
`Q = Z · P` the hulls `K_τ` (`τ ≤ S`) stay local for the recoded field `h₀ = h + f − q`; PROVE-LOCEXT-B's handoff,
"Details" item 4 (the two-step-model argument).

**General statement (`IsLocalSet.withDensity_exp_neg`).** Let `A` be a local set of `h` under `P`, `s_k` energy-Cauchy test
functions (`IsCovCauchy`) with `h(s_k) → Λ(h)` almost surely (`Λ` Borel), `Z = exp(−Λ(h) + b)` a probability density, and
`c` a deterministic distribution whose Dirichlet pairings are those of the source: `c(−Δg/2π) = lim_k ∫ s_k g` for every
`g ∈ C_c^∞(U)`, `U ⊆ ℍ` open (`c` is "`G_ℍ v` up to a harmonic function"). Then `A` is a local set of `h + c` under
`Q = Z · P`.

Proof (on the two-step model `(A', h₁, h₂)` of `A` under `P`, with `𝒢 = σ(A', h₁)` and `D = ℍ ∖ A'`):
* the model is tilted by `Z(h₁ + h₂)`; along a subsequence `h₂(s_k) → Y` (`LocalExtDTilt`), so
  `Z = e^{−M₁ + b} e^{−Y}` with `M₁ = lim h₁(s_k)` `𝒢`-measurable;
* `E[Z | 𝒢] = e^{−M₁ + b} e^{σ²/2}` and the conditional tilt (`condExp_exp_neg_srcLim_mul_cexp`) give, by Bayes
  (`condExp_withDensity_ae_eq`), that `h₂ + Γ` is conditionally a zero-boundary GFF on `D` under the tilted model, where
  `Γ = covLimDist` is the conditional covariance of `h₂` with the source (the Green potential `G_D v`);
* the new harmonic part `h₁ + c − Γ` is harmonic on `D`: `c − Γ` annihilates `−Δg/2π` for `g ∈ C_c^∞(D)` (both sides are
  `lim ∫ s_k g`, `covVec_lapTest`, `inner_covVec_gradFeat`), and Weyl's lemma applies;
* the law of `(A', h₁ + h₂ + c)` under the tilted model is that of `(A, h + c)` under `Q` (`map_withDensity_comp`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal NNReal

universe u

namespace InteractingSLE

namespace LocalExt

open QuantumZipper QuantumZipper.Thm11Asm LQGMetric LocalSets

/-! ### Pushing a density forward -/

section MapDensity

variable {α β : Type*} {mα : MeasurableSpace α} [MeasurableSpace β]

/-- `(μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f` for a measurable `g`. -/
theorem map_withDensity_comp (μ : Measure α) {g : α → β} (hg : Measurable g) {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity fun a => f (g a)).map g = (μ.map g).withDensity f := by
  ext S hS
  rw [Measure.map_apply hg hS, withDensity_apply _ (hg hS), withDensity_apply _ hS,
    setLIntegral_map hS hf hg]

/-- `(μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f` for an almost everywhere measurable `g`. -/
theorem map_withDensity_comp_of_aemeasurable (μ : Measure α) {g : α → β} (hg : AEMeasurable g μ) {f : β → ℝ≥0∞}
    (hf : Measurable f) : (μ.withDensity fun a => f (g a)).map g = (μ.map g).withDensity f := by
  have h1 : (μ.withDensity fun a => f (g a)) = μ.withDensity fun a => f (hg.mk g a) :=
    withDensity_congr_ae (hg.ae_eq_mk.mono fun a ha => by simp only [ha])
  have hac : (μ.withDensity fun a => f (hg.mk g a)) ≪ μ := withDensity_absolutelyContinuous _ _
  rw [h1, Measure.map_congr (hac.ae_le hg.ae_eq_mk), map_withDensity_comp μ hg.measurable_mk hf,
    Measure.map_congr hg.ae_eq_mk]

end MapDensity

/-! ### The new harmonic part -/

section Harmonic

variable {s : ℕ → TestOn upperHalfPlaneOpens}

/-- The Dirichlet pairing of the covariance with a source: `Cov_D(−Δg/2π, ψ) = ∫ ψ g` for `g ∈ C_c^∞(D)`. -/
theorem zeroGFFTestCov_lapTest_eq {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) (g : MarkovZB.zsSub D)
    (ψ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov D (lapTest ⟨D, hD⟩ g) ψ = ∫ z, ψ z * g.1 z := by
  have hDo : (⟨D, hD⟩ : Opens ℂ) ≤ upperHalfPlaneOpens := hDH
  rw [zeroGFFTestCov_eq_inner_covVec hD hDH, covVec_lapTest hDo hD hDH subset_rfl g]
  by_cases hpos : ∃ f ∈ zeroSpace D, 0 < dirichletEnergyOn D f
  · rw [real_inner_comm]
    have h1 := inner_covVec_gradFeat hD hDH (toTestFunH ψ) hpos g.2
    simp only [toTestFunH] at h1
    rw [h1, setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport fun h' => hz (g.2.2.2 h'), mul_zero]]
  · have hE : dirichletEnergyOn D g.1 = 0 :=
      le_antisymm (not_lt.1 fun h => hpos ⟨g.1, g.2, h⟩) (K3.dirichletEnergyOn_nonneg D g.1)
    have hg0 : g.1 = 0 := Sobolev.eq_zero_of_dirichletEnergyOn_eq_zero (D := ⟨D, hD⟩) g.2 hE
    rw [gradFeat_eq_zero_of_nopos subset_rfl hpos g.2, inner_zero_left, hg0]
    simp

/-- **`c − Γ_D` is harmonic on `D`** when `c` has the Dirichlet pairings of the source. -/
theorem isHarmonicDistOn_sub_covLimDist {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) (hs : IsCovCauchy s)
    {c : DistOn upperHalfPlaneOpens}
    (hc : ∀ (U : Opens ℂ) (_ : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)),
      Tendsto (fun k => ∫ z, s k z * g.1 z) atTop (𝓝 (c (lapTest U g)))) :
    IsHarmonicDistOn (c - covLimDist hD hDH hs) D := by
  set Do : Opens ℂ := ⟨D, hD⟩ with hDodef
  have hDo : Do ≤ upperHalfPlaneOpens := hDH
  set T : DistOn upperHalfPlaneOpens := c - covLimDist hD hDH hs with hT
  have hweyl : ∀ f : MarkovZB.zsSub (Do : Set ℂ), GFF.restrictDist Do T (MarkovHarm.cmTestOn f) = 0 := by
    intro f
    rw [GFF.restrictDist_apply]
    show c (lapTest Do f) - covLimDist hD hDH hs (lapTest Do f) = 0
    rw [covLimDist_apply, sub_eq_zero]
    refine tendsto_nhds_unique (hc Do hDo f) ((tendsto_covLim hD hDH hs (lapTest Do f)).congr fun k => ?_)
    rw [zeroGFFTestCov_lapTest_eq hD hDH f]
  obtain ⟨g, hg, hgT⟩ := MarkovWeyl3.exists_harmonic_of_laplacian_eq_zero (GFF.restrictDist Do T) hweyl
  refine ⟨g, hg, fun φ hφ => ?_⟩
  have := hgT (testOnOfSubset (U := Do) φ hφ)
  rw [GFF.restrictDist_apply, testIncl_testOnOfSubset hDo] at this
  exact this

end Harmonic

/-! ### The tilted conditional law of the zero-boundary part -/

section CondTilt

theorem covLim_zero {U : Set ℂ} {s : ℕ → TestOn upperHalfPlaneOpens} (hU : IsOpen U) (hUH : U ⊆ H)
    (hs : IsCovCauchy s) : covLim U s 0 = 0 := by
  have h := covLim_smul hU hUH hs 0 0
  rwa [zero_smul, zero_mul] at h

variable {Ω : Type*} {𝒢 𝒢' : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **The tilted conditional law** (the Gaussian heart of step 5's locality). Let `h₂` be conditionally a zero-boundary
GFF on `ℍ ∖ A` given `𝒢`, `h₁` `𝒢`-measurable, `s_k` energy-Cauchy with `(h₁ + h₂)(s_k) → Λ(h₁ + h₂)` almost surely, and
`Z = exp(−Λ(h₁ + h₂) + b)` a probability density. Then under `Z · P`, `h₂ + Γ` (`Γ = covLimDist`, the Green potential of
the source on `ℍ ∖ A`) is conditionally a zero-boundary GFF on `ℍ ∖ A` given every `𝒢' ≤ 𝒢` that measures the
variances. -/
theorem isCondZeroBoundaryGFF_withDensity_tilt [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) (h𝒢' : 𝒢' ≤ 𝒢)
    {A : Ω → Set ℂ} (hD : ∀ ω, IsOpen (H \ A ω)) {h₁ h₂ : Ω → DistOn upperHalfPlaneOpens}
    (hh₁ : Measurable[𝒢] h₁) (hh₂ : Measurable h₂) (hcond : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) h₂)
    (hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens, Measurable[𝒢] fun ω => zeroGFFTestCov (H \ A ω) φ ψ)
    (hcov' : ∀ φ : TestOn upperHalfPlaneOpens, Measurable[𝒢'] fun ω => zeroGFFTestCov (H \ A ω) φ φ)
    {s : ℕ → TestOn upperHalfPlaneOpens} (hs : IsCovCauchy s) {Λ : DistOn upperHalfPlaneOpens → ℝ}
    (hΛ : Measurable Λ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun k => (h₁ ω + h₂ ω) (s k)) atTop (𝓝 (Λ (h₁ ω + h₂ ω))))
    {b : ℝ} (hZ : ∫⁻ ω, ENNReal.ofReal (Real.exp (-Λ (h₁ ω + h₂ ω) + b)) ∂P = 1) :
    IsCondZeroBoundaryGFF (P.withDensity fun ω => ENNReal.ofReal (Real.exp (-Λ (h₁ ω + h₂ ω) + b))) 𝒢'
      (fun ω => H \ A ω) fun ω => h₂ ω + covLimDist (hD ω) sdiff_subset hs := by
  have hh₁m : Measurable h₁ := hh₁.mono h𝒢 le_rfl
  have hXm : Measurable fun ω => h₁ ω + h₂ ω := measurable_distOn_iff.2 fun φ => by
    simp only [add_apply]
    exact ((measurable_distOn_apply φ).comp hh₁m).add ((measurable_distOn_apply φ).comp hh₂)
  set Z : Ω → ℝ := fun ω => Real.exp (-Λ (h₁ ω + h₂ ω) + b) with hZdef
  have hZm : Measurable Z := ((hΛ.comp hXm).neg.add_const b).exp
  have hZi : Integrable Z P :=
    (lintegral_ofReal_ne_top_iff_integrable hZm.aestronglyMeasurable
      (ae_of_all _ fun ω => (Real.exp_pos _).le)).1 (by
        show ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≠ ∞
        rw [hZ]; exact ENNReal.one_ne_top)
  have hQP : (P.withDensity fun ω => ENNReal.ofReal (Z ω)) ≪ P := withDensity_absolutelyContinuous _ _
  have hQprob : IsProbabilityMeasure (P.withDensity fun ω => ENNReal.ofReal (Z ω)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hZ⟩
  -- `Λ(h₁ + h₂) = M₁ + Y`
  have hY := ae_tendsto_srcLim h𝒢 hD hcond hh₂ hcovm hs
  set Y : Ω → ℝ := srcLim s h₂ with hYdef
  set M₁ : Ω → ℝ := fun ω => limUnder atTop fun k => h₁ ω (s k) with hM₁def
  have hM₁m : StronglyMeasurable[𝒢] M₁ :=
    @StronglyMeasurable.limUnder ℕ Ω ℝ 𝒢 _ _ atTop _ _ _ _ fun k =>
      ((measurable_distOn_apply (s k)).comp hh₁).stronglyMeasurable
  have hΛY : ∀ᵐ ω ∂P, Λ (h₁ ω + h₂ ω) = M₁ ω + Y ω := by
    filter_upwards [hconv, hY] with ω h1 h2
    have h3 : Tendsto (fun k => h₁ ω (s k)) atTop (𝓝 (Λ (h₁ ω + h₂ ω) - Y ω)) :=
      (h1.sub h2).congr fun k => by simp only [add_apply]; ring
    rw [show M₁ ω = Λ (h₁ ω + h₂ ω) - Y ω from h3.limUnder_eq]
    ring
  -- `E[Z | 𝒢] = N`
  set N : Ω → ℝ := fun ω => Real.exp (-M₁ ω + b) * Real.exp (srcVar (H \ A ω) s / 2) with hNdef
  have hEm : StronglyMeasurable[𝒢] fun ω => Real.exp (-M₁ ω + b) :=
    ((hM₁m.measurable.neg.add_const b).exp).stronglyMeasurable
  have hNm : StronglyMeasurable[𝒢] N :=
    (hEm.measurable.mul (((measurable_srcVar hcovm).div_const 2).exp)).stronglyMeasurable
  have hNpos : ∀ ω, 0 < N ω := fun ω => mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hYi : Integrable (fun ω => Real.exp (-Y ω)) P := integrable_exp_neg_srcLim h𝒢 hD hcond hh₂ hcovm hs
  have hcY : P[fun ω => Real.exp (-Y ω) | 𝒢] =ᵐ[P] fun ω => Real.exp (srcVar (H \ A ω) s / 2) := by
    have ht0 := condExp_exp_neg_srcLim_mul_cexp h𝒢 hD hcond hh₂ hcovm hs 0
    have hcomm := Complex.ofRealCLM.comp_condExp_comm (m := 𝒢) hYi
    filter_upwards [ht0, hcomm] with ω e1 e2
    have e3 : (fun ω => ((Real.exp (-srcLim s h₂ ω) : ℝ) : ℂ) * Complex.exp (Complex.I * (h₂ ω 0 : ℂ))) =
        Complex.ofRealCLM ∘ fun ω => Real.exp (-Y ω) := by
      funext ω
      simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, Function.comp_apply,
        Complex.ofRealCLM_apply, hYdef]
    rw [e3] at e1
    have e4 : ((P[fun ω => Real.exp (-Y ω) | 𝒢] ω : ℝ) : ℂ) = ((Real.exp (srcVar (H \ A ω) s / 2) : ℝ) : ℂ) := by
      have := e2.trans e1
      simp only [Function.comp_apply, Complex.ofRealCLM_apply] at this
      rw [this, covLim_zero (hD ω) sdiff_subset hs, show ((0 : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = 0 from rfl,
        GFF.zeroGFFTestCov_zero_zero, neg_zero]
      simp [cfVal]
    exact_mod_cast e4
  have hZeq : Z =ᵐ[P] (fun ω => Real.exp (-M₁ ω + b)) * fun ω => Real.exp (-Y ω) := by
    filter_upwards [hΛY] with ω hω
    simp only [hZdef, Pi.mul_apply, hω, ← Real.exp_add]
    congr 1; ring
  have hN : P[Z | 𝒢] =ᵐ[P] N := by
    have hfg : Integrable ((fun ω => Real.exp (-M₁ ω + b)) * fun ω => Real.exp (-Y ω)) P := hZi.congr hZeq
    filter_upwards [condExp_congr_ae hZeq, condExp_mul_of_stronglyMeasurable_left
      (f := fun ω => Real.exp (-M₁ ω + b)) (g := fun ω => Real.exp (-Y ω)) hEm hfg hYi, hcY] with ω e1 e2 e3
    rw [e1, e2, Pi.mul_apply, e3]
  -- Bayes and the tilt, test function by test function
  intro φ
  set Xφ : Ω → ℂ := fun ω => Complex.exp (Complex.I * ((h₂ ω + covLimDist (hD ω) sdiff_subset hs) φ : ℂ))
    with hXφ
  have hΓm : Measurable[𝒢] fun ω => covLim (H \ A ω) s φ := measurable_covLim hcovm φ
  have hXφm : AEStronglyMeasurable Xφ P := by
    have : Measurable fun ω => (h₂ ω + covLimDist (hD ω) sdiff_subset hs) φ := by
      simp only [add_apply, covLimDist_apply]
      exact ((measurable_distOn_apply φ).comp hh₂).add (hΓm.mono h𝒢 le_rfl)
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp this))).aestronglyMeasurable
  have hXφb : ∀ ω, ‖Xφ ω‖ ≤ 1 := fun ω => (norm_cexp_I_mul _).le
  have hbayes := condExp_withDensity_ae_eq h𝒢 hZm (fun ω => (Real.exp_pos _).le) hZi hNm hNpos hN hXφm hXφb
  set Fφ : Ω → ℂ := fun ω => ((Real.exp (-M₁ ω + b) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (covLim (H \ A ω) s φ : ℂ)) with hFφ
  set Gφ : Ω → ℂ := fun ω => ((Real.exp (-srcLim s h₂ ω) : ℝ) : ℂ) *
    Complex.exp (Complex.I * (h₂ ω φ : ℂ)) with hGφ
  have hZX : (fun ω => Z ω • Xφ ω) =ᵐ[P] fun ω => (ContinuousLinearMap.mul ℝ ℂ) (Fφ ω) (Gφ ω) := by
    filter_upwards [hZeq] with ω hω
    rw [hω, Complex.real_smul, hXφ, hFφ, hGφ, ContinuousLinearMap.mul_apply']
    simp only [Pi.mul_apply, add_apply, covLimDist_apply, Complex.ofReal_add, mul_add, Complex.exp_add,
      Complex.ofReal_mul, hYdef]
    ring
  have hFm : AEStronglyMeasurable[𝒢] Fφ P :=
    ((Complex.measurable_ofReal.comp hEm.measurable).mul
      (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hΓm)))).aestronglyMeasurable
  have hGi : Integrable Gφ P := by
    refine hYi.mono' (((Complex.measurable_ofReal.comp
      (measurable_srcLim hh₂).neg.exp).mul (Complex.measurable_exp.comp (measurable_const.mul
        (Complex.measurable_ofReal.comp ((measurable_distOn_apply φ).comp hh₂))))).aestronglyMeasurable)
      (ae_of_all _ fun ω => le_of_eq ?_)
    rw [hGφ, norm_mul, norm_cexp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hFGi : Integrable (fun ω => (ContinuousLinearMap.mul ℝ ℂ) (Fφ ω) (Gφ ω)) P := by
    refine hZi.mono' ((hFm.mono h𝒢).mul hGi.aestronglyMeasurable) ?_
    filter_upwards [hZX] with ω hω
    rw [ContinuousLinearMap.mul_apply'] at hω
    rw [ContinuousLinearMap.mul_apply', ← hω, norm_smul, norm_cexp_I_mul, mul_one, Real.norm_eq_abs]
    exact (abs_of_pos (Real.exp_pos _)).le
  have hpull := condExp_bilin_of_aestronglyMeasurable_left (m := 𝒢) (ContinuousLinearMap.mul ℝ ℂ) hFm hFGi hGi
  have htilt := condExp_exp_neg_srcLim_mul_cexp h𝒢 hD hcond hh₂ hcovm hs φ
  have hstep : (P.withDensity fun ω => ENNReal.ofReal (Z ω))[Xφ | 𝒢] =ᵐ[P.withDensity fun ω => ENNReal.ofReal (Z ω)]
      fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ) := by
    filter_upwards [hbayes, hQP.ae_le (condExp_congr_ae hZX), hQP.ae_le hpull, hQP.ae_le htilt]
      with ω e1 e2 e3 e4
    rw [e1, e2, e3, ContinuousLinearMap.mul_apply', e4, hFφ, hNdef, cfVal, Complex.real_smul]
    simp only [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_exp]
    have h1 : Complex.exp ((-M₁ ω + b : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
    have h2 : Complex.exp ((srcVar (H \ A ω) s / 2 : ℝ) : ℂ) ≠ 0 := Complex.exp_ne_zero _
    field_simp
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the tower property
  set c' : Ω → ℂ := fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ) with hc'def
  have hc'm : StronglyMeasurable[𝒢'] c' :=
    (Complex.measurable_ofReal.comp (Real.measurable_exp.comp ((hcov' φ).const_mul _))).stronglyMeasurable
  have hc'i : Integrable c' (P.withDensity fun ω => ENNReal.ofReal (Z ω)) := by
    refine Integrable.of_bound (hc'm.measurable.mono (h𝒢'.trans h𝒢) le_rfl).aestronglyMeasurable 1
      (ae_of_all _ fun ω => ?_)
    rw [hc'def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    have := zeroGFFTestCov_self_nonneg (hD ω) sdiff_subset φ
    nlinarith
  calc (P.withDensity fun ω => ENNReal.ofReal (Z ω))[Xφ | 𝒢']
      =ᵐ[P.withDensity fun ω => ENNReal.ofReal (Z ω)]
        (P.withDensity fun ω => ENNReal.ofReal (Z ω))[(P.withDensity fun ω => ENNReal.ofReal (Z ω))[Xφ | 𝒢] | 𝒢'] :=
        (condExp_condExp_of_le h𝒢' h𝒢).symm
    _ =ᵐ[P.withDensity fun ω => ENNReal.ofReal (Z ω)] (P.withDensity fun ω => ENNReal.ofReal (Z ω))[c' | 𝒢'] :=
        condExp_congr_ae hstep
    _ = c' := condExp_of_stronglyMeasurable (h𝒢'.trans h𝒢) hc'm hc'i

end CondTilt
/-! ### The tilt of a local set -/

section Tilt

/-- **A Cameron–Martin tilt preserves local sets** (step 5's locality; Aux. lemma 55, p. 250). If `A` is a local set of
`h` under `P`, `s_k` are energy-Cauchy test functions with `h(s_k) → Λ(h)` almost surely, `Z = exp(−Λ(h) + b)` is a
probability density, and `c` is a deterministic distribution with the Dirichlet pairings of the source
(`c(−Δg/2π) = lim_k ∫ s_k g` for `g ∈ C_c^∞(U)`, `U ⊆ ℍ` open), then `A` is a local set of `h + c` under `Z · P`. -/
theorem IsLocalSet.withDensity_exp_neg {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hloc : IsLocalSet A h P) (hhm : Measurable h) {s : ℕ → TestOn upperHalfPlaneOpens} (hs : IsCovCauchy s)
    {Λ : DistOn upperHalfPlaneOpens → ℝ} (hΛ : Measurable Λ)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun k => h ω (s k)) atTop (𝓝 (Λ (h ω))))
    {b : ℝ} (hZ : ∫⁻ ω, ENNReal.ofReal (Real.exp (-Λ (h ω) + b)) ∂P = 1)
    {c : DistOn upperHalfPlaneOpens}
    (hc : ∀ (U : Opens ℂ) (_ : U ≤ upperHalfPlaneOpens) (g : MarkovZB.zsSub (U : Set ℂ)),
      Tendsto (fun k => ∫ z, s k z * g.1 z) atTop (𝓝 (c (lapTest U g)))) :
    IsLocalSet A (fun ω => h ω + c) (P.withDensity fun ω => ENNReal.ofReal (Real.exp (-Λ (h ω) + b))) := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hAE, hsub, Ω', mΩ', P', hP', A', h₁, h₂, hA'm, hh₁m, hh₂m, hA'sub, hharm, hcond, hlaw⟩ := hloc
  have hzm : Measurable fun T : DistOn upperHalfPlaneOpens => Real.exp (-Λ T + b) := (hΛ.neg.add_const b).exp
  have hQP : (P.withDensity fun ω => ENNReal.ofReal (Real.exp (-Λ (h ω) + b))) ≪ P :=
    withDensity_absolutelyContinuous _ _
  have hF : Measurable fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 + c) :=
    measurable_fst.prodMk ((Coupling.measurable_add_distOnConst c).comp measurable_snd)
  -- the field of the model and its law
  have hXm : Measurable fun ω' => h₁ ω' + h₂ ω' := measurable_distOn_iff.2 fun φ => by
    simp only [add_apply]
    exact ((measurable_distOn_apply φ).comp hh₁m).add ((measurable_distOn_apply φ).comp hh₂m)
  have hg'm : Measurable fun ω' => (A' ω', h₁ ω' + h₂ ω') := hA'm.prodMk hXm
  have hlawX : P'.map (fun ω' => h₁ ω' + h₂ ω') = P.map h := by
    have h1 : P'.map (fun ω' => h₁ ω' + h₂ ω') = (P'.map fun ω' => (A' ω', h₁ ω' + h₂ ω')).map Prod.snd := by
      rw [Measure.map_map measurable_snd hg'm]; rfl
    have h2 : P.map h = (P.map fun ω => (A ω, h ω)).map Prod.snd := by
      rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hAE]; rfl
    rw [h1, h2, ← hlaw]
  -- the source pairing of the model's field
  have hSm : MeasurableSet {T : DistOn upperHalfPlaneOpens | Tendsto (fun k => T (s k) - Λ T) atTop (𝓝 0)} :=
    measurableSet_tendsto (𝓝 (0 : ℝ)) fun k => (measurable_distOn_apply (s k)).sub hΛ
  have hconvS : ∀ᵐ T ∂(P.map h), Tendsto (fun k => T (s k) - Λ T) atTop (𝓝 0) := by
    refine (ae_map_iff hhm.aemeasurable hSm).2 ?_
    filter_upwards [hconv] with ω hω
    exact tendsto_sub_nhds_zero_iff.2 hω
  have hconv' : ∀ᵐ ω' ∂P', Tendsto (fun k => (h₁ ω' + h₂ ω') (s k)) atTop (𝓝 (Λ (h₁ ω' + h₂ ω'))) := by
    rw [← hlawX] at hconvS
    filter_upwards [(ae_map_iff hXm.aemeasurable hSm).1 hconvS] with ω' hω'
    exact tendsto_sub_nhds_zero_iff.1 hω'
  have hZ' : ∫⁻ ω', ENNReal.ofReal (Real.exp (-Λ (h₁ ω' + h₂ ω') + b)) ∂P' = 1 := by
    calc ∫⁻ ω', ENNReal.ofReal (Real.exp (-Λ (h₁ ω' + h₂ ω') + b)) ∂P'
        = ∫⁻ T, ENNReal.ofReal (Real.exp (-Λ T + b)) ∂(P'.map fun ω' => h₁ ω' + h₂ ω') :=
          (lintegral_map (ENNReal.measurable_ofReal.comp hzm) hXm).symm
      _ = ∫⁻ T, ENNReal.ofReal (Real.exp (-Λ T + b)) ∂(P.map h) := by rw [hlawX]
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-Λ (h ω) + b)) ∂P :=
          lintegral_map (ENNReal.measurable_ofReal.comp hzm) hhm
      _ = 1 := hZ
  have hQ'P' : (P'.withDensity fun ω' => ENNReal.ofReal (Real.exp (-Λ (h₁ ω' + h₂ ω') + b))) ≪ P' :=
    withDensity_absolutelyContinuous _ _
  have hQ'prob : IsProbabilityMeasure
      (P'.withDensity fun ω' => ENNReal.ofReal (Real.exp (-Λ (h₁ ω' + h₂ ω') + b))) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hZ'⟩
  -- the conditioning σ-algebras of the model
  have hD : ∀ ω', IsOpen (H \ A' ω') := fun ω' => (hA'sub ω').2
  have hcovA : ∀ φ ψ : TestOn upperHalfPlaneOpens,
      Measurable[MeasurableSpace.comap A' hittingSigma] fun ω' => zeroGFFTestCov (H \ A' ω') φ ψ := by
    intro φ ψ
    have h1 := measurable_comap_zeroGFFTestCov_compl A' φ ψ
    have e : (fun ω' => zeroGFFTestCov (H \ relClosureH (A' ω')) φ ψ) =
        fun ω' => zeroGFFTestCov (H \ A' ω') φ ψ := by
      funext ω'; rw [relClosureH_eq (hA'sub ω').1 (hA'sub ω').2]
    rwa [e] at h1
  have h𝒢 : MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance ≤ mΩ' :=
    sup_le hA'm.comap_le hh₁m.comap_le
  have hh₁𝒢 : Measurable[MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance] h₁ :=
    (comap_measurable h₁).mono le_sup_right le_rfl
  have hcovm : ∀ φ ψ : TestOn upperHalfPlaneOpens,
      Measurable[MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance]
        fun ω' => zeroGFFTestCov (H \ A' ω') φ ψ :=
    fun φ ψ => (hcovA φ ψ).mono le_sup_left le_rfl
  -- the new fields
  have hΓφ : ∀ φ ω', covLimDist (hD ω') sdiff_subset hs φ = covLim (H \ A' ω') s φ :=
    fun φ ω' => covLimDist_apply _ _ _ φ
  have hh₁'𝒢 : Measurable[MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance]
      fun ω' => h₁ ω' + (c - covLimDist (hD ω') sdiff_subset hs) := by
    refine (@measurable_distOn_iff upperHalfPlaneOpens Ω'
      (MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance) _).2 fun φ => ?_
    simp only [add_apply, sub_apply, hΓφ]
    exact ((measurable_distOn_apply φ).comp hh₁𝒢).add (measurable_const.sub (measurable_covLim hcovm φ))
  have hh₁'m : Measurable fun ω' => h₁ ω' + (c - covLimDist (hD ω') sdiff_subset hs) := hh₁'𝒢.mono h𝒢 le_rfl
  have hh₂'m : Measurable fun ω' => h₂ ω' + covLimDist (hD ω') sdiff_subset hs :=
    measurable_distOn_iff.2 fun φ => by
      simp only [add_apply, hΓφ]
      exact ((measurable_distOn_apply φ).comp hh₂m).add ((measurable_covLim hcovm φ).mono h𝒢 le_rfl)
  have h𝒢'𝒢 : MeasurableSpace.comap A' hittingSigma ⊔
      MeasurableSpace.comap (fun ω' => h₁ ω' + (c - covLimDist (hD ω') sdiff_subset hs)) inferInstance ≤
      MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance :=
    sup_le le_sup_left hh₁'𝒢.comap_le
  refine ⟨hF.comp_aemeasurable (hAE.mono_ac hQP), hQP.ae_le hsub, Ω', mΩ',
    P'.withDensity fun ω' => ENNReal.ofReal (Real.exp (-Λ (h₁ ω' + h₂ ω') + b)), hQ'prob, A',
    fun ω' => h₁ ω' + (c - covLimDist (hD ω') sdiff_subset hs),
    fun ω' => h₂ ω' + covLimDist (hD ω') sdiff_subset hs, hA'm, hh₁'m, hh₂'m, hA'sub, ?_, ?_, ?_⟩
  · -- the new harmonic part
    filter_upwards [hQ'P'.ae_le hharm] with ω' hω'
    exact Coupling.IsHarmonicDistOn.add' (hD ω') hω'
      (isHarmonicDistOn_sub_covLimDist (hD ω') sdiff_subset hs hc)
  · -- the new zero-boundary part
    exact isCondZeroBoundaryGFF_withDensity_tilt h𝒢 h𝒢'𝒢 hD hh₁𝒢 hh₂m hcond hcovm
      (fun φ => (hcovA φ φ).mono le_sup_left le_rfl) hs hΛ hconv' hZ'
  · -- the law
    have e1 : (fun ω' => (A' ω', (h₁ ω' + (c - covLimDist (hD ω') sdiff_subset hs)) +
        (h₂ ω' + covLimDist (hD ω') sdiff_subset hs))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 + c)) ∘ fun ω' => (A' ω', h₁ ω' + h₂ ω') := by
      funext ω'
      simp only [Function.comp_apply, Prod.mk.injEq, true_and]
      abel
    have e2 : (fun ω => (A ω, h ω + c)) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => (p.1, p.2 + c)) ∘ fun ω => (A ω, h ω) := rfl
    have hfm : Measurable fun p : Set ℂ × DistOn upperHalfPlaneOpens => ENNReal.ofReal (Real.exp (-Λ p.2 + b)) :=
      ENNReal.measurable_ofReal.comp (hzm.comp measurable_snd)
    have e3 : (P'.withDensity fun ω' => ENNReal.ofReal (Real.exp (-Λ (h₁ ω' + h₂ ω') + b))).map
        (fun ω' => (A' ω', h₁ ω' + h₂ ω')) =
        (P.withDensity fun ω => ENNReal.ofReal (Real.exp (-Λ (h ω) + b))).map fun ω => (A ω, h ω) := by
      rw [map_withDensity_comp (f := fun p : Set ℂ × DistOn upperHalfPlaneOpens => ENNReal.ofReal (Real.exp (-Λ p.2 + b)))
        P' hg'm hfm, hlaw, ← map_withDensity_comp_of_aemeasurable P hAE hfm]
    rw [e1, ← Measure.map_map hF hg'm, e3, e2,
      AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (hAE.mono_ac hQP)]

end Tilt

end LocalExt

end InteractingSLE
