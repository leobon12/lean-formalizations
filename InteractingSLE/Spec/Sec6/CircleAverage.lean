/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.CircleAverageGreen
import InteractingSLE.GFF.LocalSets.SubdomainLaw
import InteractingSLE.GFF.LocalSets.SubdomainCov
import InteractingSLE.Spec.Coupling.Lemma311
import SupercriticalConformalCovariance.GM24.Bridge
import QuantumZipper.Proofs.Complex.KoebeCovering

/-!
# Lemma 6.4: the law of the conditional mean at a point

Packet PROVE-SEC6-A3 (specification §6.1, `source/spec/p145-192.md`, `#lem-6.4`, p. 157).

**Lemma 6.4.** Let `h` be a GFF on `D` with harmonic mean `𝒞`, `z ∈ D`, and `A` a local set of `h`
such that `D ∖ A` is simply connected and `C(z; D ∖ A)` is almost surely a constant `c > 0`. Then
`𝒞_A(z) ∼ N(𝒞(z), log C(z; D) − log C(z; D ∖ A))`.

Here `D = ℍ` (local sets of the project live on `ℍ`, ruling R19 (5)), so `C(z; ℍ) = 2 Im z`; `h` is a
measurable field with `h − F` a zero-boundary GFF on `ℍ` (`F` harmonic on `ℍ`, the frozen form of
`IsGFFWithBoundaryData`); the local-set mean `𝒞_A` is any `g` with `LocalSets.IsLocalSetMean A h P g`
(the characterization (iii) of Lemma 3.6, with the local-set information `germSigma A h`); the
hypothesis on the conformal radius is the source's definition: almost surely there is a conformal
`φ : 𝔻 → ℍ ∖ A` with `φ(0) = z` and `|φ'(0)| = c`. The value `𝒞_A(z)` is that of the harmonic
representative of `g` on `ℍ ∖ A`; it is the normalized pairing of `g` with a radial bump
`b = bump_{z,ε}` whose support stays in `ℍ ∖ A` (non-random `ε`, by Koebe's covering theorem).

## Proof (as in the source, with a radial bump instead of the circle average)

By Koebe, `B̄(z, ε) ⊆ ℍ ∖ A` a.s. for `ε = c/96`. Write `X = g(b)`, `Y = (h − g)(b)`. Conditionally on
the local-set information, `Y` is centred Gaussian with variance `Var_{ℍ∖A}(b)`, which by the
variance identity (`zeroGFFTestCov_sub_eq_log_confRadius`) is the non-random number
`Var_ℍ(b) − (∫ b)²(log(2 Im z) − log c)`; `X` is measurable for that information and
`X + Y = h(b) ∼ N((∫ b) F(z), Var_ℍ(b))` (mean value property for `F`). The characteristic
function of `X` is then the quotient (`map_eq_gaussianReal_of_condExp_charFun_const`, the
conditional form of Lemma 6.3), and `𝒞_A(z) = X / ∫ b` by the mean value property.

## Main results

* `map_eq_gaussianReal_of_condExp_charFun_const`: Gaussian deconvolution given a constant conditional
  characteristic function;
* `isOpen_of_isConformalBijection_ball`, `exists_isConformalBijection_inv`;
* `IsLocalSetMean.lemma64`: **Lemma 6.4**.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped NNReal ENNReal

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H zeroGFFTestCov)

namespace InteractingSLE.Sec6

/-! ### Gaussian deconvolution with a constant conditional characteristic function -/

section Deconvolution

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- If `X` is `𝒢`-measurable, the conditional characteristic function of `Y` given `𝒢` is the
non-random `exp(−t² s/2)`, and `X + Y ∼ N(μ, v)`, then `s ≤ v` and `X ∼ N(μ, v − s)` (Lemma 6.3 in
conditional form). -/
theorem map_eq_gaussianReal_of_condExp_charFun_const (h𝒢 : 𝒢 ≤ mΩ) {X Y : Ω → ℝ}
    (hX : Measurable[𝒢] X) (hY : Measurable Y) {s : ℝ≥0}
    (hcond : ∀ t : ℝ, P[fun ω => cexp (I * (t * Y ω : ℝ)) | 𝒢] =ᵐ[P]
      fun _ => ((Real.exp (-(1 / 2) * (t ^ 2 * s)) : ℝ) : ℂ))
    {μ : ℝ} {v : ℝ≥0} (hZ : P.map (fun ω => X ω + Y ω) = gaussianReal μ v) :
    s ≤ v ∧ P.map X = gaussianReal μ (v - s) := by
  have hXm : Measurable X := hX.mono h𝒢 le_rfl
  -- the characteristic function of `X + Y` factorizes
  have hfac : ∀ t : ℝ, charFun (P.map (fun ω => X ω + Y ω)) t =
      charFun (P.map X) t * ((Real.exp (-(1 / 2) * (t ^ 2 * s)) : ℝ) : ℂ) := by
    intro t
    have hZm : Measurable fun ω => X ω + Y ω := hXm.add hY
    rw [charFun_apply_real, charFun_apply_real]
    set f : Ω → ℂ := fun ω => cexp (t * X ω * I) with hf
    set g : Ω → ℂ := fun ω => cexp (I * (t * Y ω : ℝ)) with hg
    have hfm : StronglyMeasurable[𝒢] f := by
      refine (Measurable.stronglyMeasurable ?_)
      exact (by fun_prop : Measurable fun x : ℝ => cexp (t * x * I)).comp hX
    have hgi : Integrable g P := by
      refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun ω => ?_)
      rw [hg]; simp only
      rw [show I * ((t * Y ω : ℝ) : ℂ) = ((t * Y ω : ℝ) : ℂ) * I by ring,
        Complex.norm_exp_ofReal_mul_I]
    have hfgi : Integrable (fun ω => f ω * g ω) P := by
      refine Integrable.of_bound ((hfm.mono h𝒢).aestronglyMeasurable.mul hgi.1) 1
        (Eventually.of_forall fun ω => ?_)
      rw [hf, hg]; simp only
      rw [norm_mul, show (t : ℂ) * (X ω : ℂ) * I = ((t * X ω : ℝ) : ℂ) * I by push_cast; ring,
        show I * ((t * Y ω : ℝ) : ℂ) = ((t * Y ω : ℝ) : ℂ) * I by ring,
        Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I, one_mul]
    have e1 : (fun ω => cexp (t * (X ω + Y ω : ℝ) * I)) = fun ω => f ω * g ω := by
      funext ω
      rw [hf, hg, ← Complex.exp_add]
      congr 1; push_cast; ring
    have hpull : P[fun ω => f ω * g ω | 𝒢] =ᵐ[P] fun ω => f ω * (P[g | 𝒢]) ω :=
      condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) (m := 𝒢) (μ := P)
        hfm hfgi hgi
    calc ∫ x, cexp (t * x * I) ∂P.map (fun ω => X ω + Y ω)
        = ∫ ω, cexp (t * (X ω + Y ω : ℝ) * I) ∂P := by
          rw [integral_map hZm.aemeasurable (by fun_prop)]
      _ = ∫ ω, f ω * g ω ∂P := by rw [e1]
      _ = ∫ ω, (P[fun ω => f ω * g ω | 𝒢]) ω ∂P := (integral_condExp h𝒢).symm
      _ = ∫ ω, f ω * (P[g | 𝒢]) ω ∂P := integral_congr_ae hpull
      _ = ∫ ω, f ω * ((Real.exp (-(1 / 2) * (t ^ 2 * s)) : ℝ) : ℂ) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hcond t] with ω hω
          rw [hω]
      _ = (∫ x, cexp (t * x * I) ∂P.map X) * ((Real.exp (-(1 / 2) * (t ^ 2 * s)) : ℝ) : ℂ) := by
          rw [integral_mul_const, integral_map hXm.aemeasurable (by fun_prop)]
  -- the characteristic function of `X`
  have hφ : ∀ t : ℝ, charFun (P.map X) t =
      cexp (t * μ * I - ((v : ℝ) - (s : ℝ) : ℝ) * t ^ 2 / 2) := by
    intro t
    have h1 := hfac t
    rw [hZ, charFun_gaussianReal] at h1
    have hne : (((Real.exp (-(1 / 2) * (t ^ 2 * s)) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.exp_pos _).ne'
    have h2 : charFun (P.map X) t = cexp (t * μ * I - (v : ℝ) * t ^ 2 / 2) *
        (((Real.exp (-(1 / 2) * (t ^ 2 * s)) : ℝ) : ℂ))⁻¹ := by
      rw [h1, mul_inv_cancel_right₀ hne]
    rw [h2, Complex.ofReal_exp, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hle : s ≤ v := by
    have h1 := norm_charFun_le_one (μ := P.map X) (1 : ℝ)
    rw [hφ 1, Complex.norm_exp] at h1
    have hre : (((1 : ℝ) : ℂ) * (μ : ℂ) * I - (((v : ℝ) - (s : ℝ) : ℝ) : ℂ) * ((1 : ℝ) : ℂ) ^ 2 / 2).re
        = -(((v : ℝ) - (s : ℝ)) / 2) := by
      simp [Complex.sub_re, Complex.mul_re]
    rw [hre, Real.exp_le_one_iff] at h1
    have : (s : ℝ) ≤ v := by linarith
    exact_mod_cast this
  refine ⟨hle, Measure.ext_of_charFun ?_⟩
  ext t
  rw [hφ t, charFun_gaussianReal, NNReal.coe_sub hle]

end Deconvolution

/-! ### Conformal maps of the disk -/

/-- The image of the unit disk under a conformal bijection is open. -/
theorem isOpen_of_isConformalBijection_ball {U : Set ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ (ball 0 1) U) : IsOpen U := by
  have ha : AnalyticOnNhd ℂ φ (ball 0 1) := fun x hx => hφ.1.analyticAt (isOpen_ball.mem_nhds hx)
  rcases ha.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with ⟨w, hw⟩ | ho
  · exfalso
    have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    have h1 : ((1 : ℂ) / 2) ∈ ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]; norm_num
    have := hφ.2.injOn h0 h1 ((hw 0 h0).trans (hw _ h1).symm)
    norm_num at this
  · rw [← hφ.2.image_eq]
    exact ho _ subset_rfl isOpen_ball

/-- The inverse of a conformal map `φ : 𝔻 → U` with `φ(0) = z` and `|φ'(0)| = c > 0` is a conformal
map `ψ : U → 𝔻` with `ψ(z) = 0` and `|ψ'(z)| = c⁻¹`. -/
theorem exists_isConformalBijection_inv {U : Set ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ (ball 0 1) U) {z : ℂ} (hφ0 : φ 0 = z) {c : ℝ}
    (hc : ‖deriv φ 0‖ = c) (hc0 : 0 < c) :
    ∃ ψ : ℂ → ℂ, IsConformalBijection ψ U (ball 0 1) ∧ ψ z = 0 ∧ ‖deriv ψ z‖ = c⁻¹ := by
  have hUo : IsOpen U := isOpen_of_isConformalBijection_ball hφ
  set B : Opens ℂ := ⟨ball 0 1, isOpen_ball⟩
  set V : Opens ℂ := ⟨U, hUo⟩
  have hφ' : IsConformalBijection φ B V := hφ
  have hψ := SupercriticalConformalCovariance.GM24.isConformalBijection_invFunOn hφ'
  set ψ := Function.invFunOn φ (B : Set ℂ) with hψdef
  have h0B : (0 : ℂ) ∈ (B : Set ℂ) := mem_ball_self one_pos
  have hzU : z ∈ U := hφ0 ▸ hφ.2.mapsTo h0B
  have hψz : ψ z = 0 := by
    rw [← hφ0]; exact hφ.2.injOn.leftInvOn_invFunOn h0B
  have hφψ : ∀ y ∈ U, φ (ψ y) = y := fun y hy => Function.invFunOn_eq (hφ.2.surjOn hy)
  have hder : HasDerivAt ψ (deriv φ 0)⁻¹ z := by
    have hψc : ContinuousAt ψ z := (hψ.1.differentiableAt (hUo.mem_nhds hzU)).continuousAt
    have hf : HasDerivAt φ (deriv φ (ψ z)) (ψ z) := by
      rw [hψz]
      exact (hφ.1.differentiableAt (isOpen_ball.mem_nhds h0B)).hasDerivAt
    have hne : deriv φ (ψ z) ≠ 0 := by
      rw [hψz]; intro h; rw [h, norm_zero] at hc; linarith
    have := HasDerivAt.of_local_left_inverse hψc hf hne
      (Filter.eventually_of_mem (hUo.mem_nhds hzU) hφψ)
    rwa [hψz] at this
  refine ⟨ψ, hψ, hψz, ?_⟩
  rw [hder.deriv, norm_inv, hc]

/-! ### Lemma 6.4 -/

open LocalSets in
/-- **Lemma 6.4** (law of the conditional mean at a point). Let `h` be a measurable random
distribution on `ℍ` with `h − F` a zero-boundary GFF on `ℍ`, `F` harmonic on `ℍ`, let `A` be a
random set with local-set mean `g` (`IsLocalSetMean A h P g`, i.e. `𝒞_A`), and let `z ∈ ℍ`.
Suppose that almost surely `ℍ ∖ A` is the image of a conformal map `φ : 𝔻 → ℍ ∖ A` with `φ(0) = z`
and `|φ'(0)| = c` (so `ℍ ∖ A` is simply connected and `C(z; ℍ ∖ A) = c`), with `c > 0` non-random.
Then there is a non-random `ε > 0` with `B̄(z, ε) ⊆ ℍ ∖ A` almost surely such that:
* `c ≤ 2 Im z`, i.e. the variance below is non-negative;
* the normalized pairing `𝒞_A(z) := (∫ b)⁻¹ g(b)` with the radial bump `b = bump_{z,ε}` has the law
  `N(F(z), log C(z; ℍ) − log C(z; ℍ ∖ A)) = N(F(z), log(2 Im z) − log c)`;
* almost surely it is the value at `z` of every harmonic representative of `g` on `ℍ ∖ A`. -/
theorem exists_map_localSetMean_eq_gaussianReal {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Ω → Set ℂ}
    {h g : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {F : ℂ → ℝ}
    (hh : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ x, F x * φ x) P)
    (hhm : Measurable h) (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hA : Measurable[mΩ, hittingSigma] A) (hg : IsLocalSetMean A h P g) {z : ℂ} {c : ℝ}
    (hc : 0 < c)
    (hC : ∀ᵐ ω ∂P, ∃ φ : ℂ → ℂ, IsConformalBijection φ (ball 0 1) (H \ A ω) ∧ φ 0 = z ∧
      ‖deriv φ 0‖ = c) :
    ∃ (ε : ℝ) (hε : 0 < ε) (hεH : closedBall z ε ⊆ upperHalfPlaneOpens),
      (∀ᵐ ω ∂P, closedBall z ε ⊆ H \ A ω) ∧ Real.log c ≤ Real.log (2 * z.im) ∧
      P.map (fun ω => (ε ^ 2 * GFF.bumpMass)⁻¹ * g ω (GFF.bumpTest z hε hεH)) =
        gaussianReal (F z) (Real.log (2 * z.im) - Real.log c).toNNReal ∧
      ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
        (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
          g ω φ = ∫ x, v x * φ x) →
        v z = (ε ^ 2 * GFF.bumpMass)⁻¹ * g ω (GFF.bumpTest z hε hεH) := by
  -- the radius, by Koebe's covering theorem
  set ε : ℝ := QuantumZipper.CA.Koebe.koebeCovConst * c / 2 with hεdef
  have hk0 := QuantumZipper.CA.Koebe.koebeCovConst_pos
  have hε : 0 < ε := by positivity
  have hball : ∀ᵐ ω ∂P, closedBall z ε ⊆ H \ A ω := by
    filter_upwards [hC] with ω hω
    obtain ⟨φ, hφ, hφ0, hφc⟩ := hω
    have hk := QuantumZipper.CA.Koebe.ball_subset_image_koebe (c := 0) (r := 1) hφ.1 hφ.2.injOn
    rw [hφ.2.image_eq, hφ0, hφc] at hk
    refine (closedBall_subset_ball ?_).trans hk
    rw [hεdef]; nlinarith
  obtain ⟨ω₀, hω₀⟩ := hball.exists
  have hεH : closedBall z ε ⊆ upperHalfPlaneOpens := hω₀.trans sdiff_subset
  have hz : 0 < z.im := hεH (mem_closedBall_self hε.le)
  set b : LQGMetric.TestOn upperHalfPlaneOpens := GFF.bumpTest z hε hεH with hbdef
  have hbcoe : ⇑b = GFF.bumpFun z ε := rfl
  set M := ε ^ 2 * GFF.bumpMass with hMdef
  have hM : 0 < M := mul_pos (by positivity) GFF.bumpMass_pos
  set L := Real.log (2 * z.im) - Real.log c with hLdef
  set VH := zeroGFFTestCov upperHalfPlaneOpens b b with hVHdef
  have hVH0 : 0 ≤ VH :=
    LQGMetric.zeroGFFTestCov_self_nonneg (LQGMetric.zbAdmissible_of_subset_H subset_rfl) b
  set s : ℝ := VH - M ^ 2 * L with hsdef
  -- the conditional variance is almost surely the constant `s`
  have hvar : ∀ᵐ ω ∂P, IsOpen (H \ A ω) ∧ closedBall z ε ⊆ H \ A ω ∧
      zeroGFFTestCov (H \ A ω) b b = s := by
    filter_upwards [hC, hball] with ω hω hb
    obtain ⟨φ, hφ, hφ0, hφc⟩ := hω
    have hUo := isOpen_of_isConformalBijection_ball hφ
    obtain ⟨ψ, hψ, hψz, hψd⟩ := exists_isConformalBijection_inv hφ hφ0 hφc hc
    have key := zeroGFFTestCov_sub_eq_log_confRadius (U := ⟨H \ A ω, hUo⟩) sdiff_subset hψ hψz hε
      hb
    rw [hψd, Real.log_inv] at key
    refine ⟨hUo, hb, ?_⟩
    change zeroGFFTestCov (H \ A ω) (GFF.bumpFun z ε) (GFF.bumpFun z ε) = s
    rw [hsdef, hVHdef, hbcoe, hLdef]
    change zeroGFFTestCov upperHalfPlaneOpens (GFF.bumpFun z ε) (GFF.bumpFun z ε) -
      zeroGFFTestCov (H \ A ω) (GFF.bumpFun z ε) (GFF.bumpFun z ε) = _ at key
    linarith
  have hs0 : 0 ≤ s := by
    obtain ⟨ω₁, hUo, hb, hv⟩ := hvar.exists
    rw [← hv]
    have := LQGMetric.zeroGFFTestCov_self_nonneg
      (LQGMetric.zbAdmissible_of_subset_H (U := ⟨H \ A ω₁, hUo⟩) sdiff_subset)
      (GFF.bumpTest z hε hb)
    exact this
  -- the two parts of the pairing
  have h𝒢 : germSigma A h ≤ mΩ := germSigma_le hA hhm
  set X : Ω → ℝ := fun ω => g ω b with hXdef
  set Y : Ω → ℝ := fun ω => h ω b - g ω b with hYdef
  have hX : Measurable[germSigma A h] X := (LQGMetric.measurable_distOn_apply b).comp hg.1
  have hgm : Measurable g := hg.1.mono h𝒢 le_rfl
  have hY : Measurable Y :=
    ((LQGMetric.measurable_distOn_apply b).comp hhm).sub
      ((LQGMetric.measurable_distOn_apply b).comp hgm)
  -- the conditional characteristic function of `Y`
  have hcond : ∀ t : ℝ, P[fun ω => cexp (I * (t * Y ω : ℝ)) | germSigma A h] =ᵐ[P]
      fun _ => ((Real.exp (-(1 / 2) * (t ^ 2 * (s.toNNReal : ℝ)))) : ℂ) := by
    intro t
    have hc' := hg.2.2 (t • b)
    have e1 : (fun ω => cexp (I * (((h ω - g ω) (t • b) : ℝ) : ℂ))) =
        fun ω => cexp (I * ((t * Y ω : ℝ) : ℂ)) := by
      funext ω
      congr 3
      simp only [hYdef, sub_apply, map_smul, smul_eq_mul, mul_sub]
    rw [e1] at hc'
    filter_upwards [hc', hvar] with ω hω hv
    obtain ⟨hUo, -, hv⟩ := hv
    rw [hω, LocalSets.zeroGFFTestCov_smul_self hUo sdiff_subset t b, hv,
      Real.coe_toNNReal _ hs0]
  -- the law of `X + Y = h(b)`
  have hFb : ∫ x, F x * b x = F z * M := by
    rw [hbcoe]
    exact GFF.integral_mul_bumpFun_of_harmonic QuantumZipper.isOpen_H hF hε hεH
  have hZ : P.map (fun ω => X ω + Y ω) = gaussianReal (F z * M) VH.toNNReal := by
    have e : (fun ω => X ω + Y ω) = fun ω => h ω b := by
      funext ω; simp only [hXdef, hYdef]; ring
    rw [e, Coupling.map_eval_eq_gaussianReal_of_isZBGFFProcess hh b, hFb]
  -- deconvolution
  obtain ⟨hsv, hlaw⟩ := map_eq_gaussianReal_of_condExp_charFun_const h𝒢 hX hY hcond hZ
  have hL0 : 0 ≤ L := by
    have h1 : s ≤ VH := by
      have := (Real.toNNReal_le_toNNReal_iff hVH0).1 hsv
      exact this
    have h2 : 0 ≤ M ^ 2 * L := by rw [hsdef] at h1; linarith
    by_contra hneg
    have := mul_neg_of_pos_of_neg (by positivity : (0 : ℝ) < M ^ 2) (lt_of_not_ge hneg)
    linarith
  have hvdiff : VH.toNNReal - s.toNNReal = (M ^ 2 * L).toNNReal := by
    rw [NNReal.sub_def, Real.coe_toNNReal _ hVH0, Real.coe_toNNReal _ hs0, hsdef]
    congr 1; ring
  refine ⟨ε, hε, hεH, hball, by rw [hLdef] at hL0; linarith, ?_, ?_⟩
  · have hXm : Measurable X := hX.mono h𝒢 le_rfl
    have e : (fun ω => M⁻¹ * g ω (GFF.bumpTest z hε hεH)) = (fun x => M⁻¹ * x) ∘ X := rfl
    rw [e, ← Measure.map_map (measurable_const_mul _) hXm, hlaw, hvdiff,
      gaussianReal_map_const_mul]
    congr 1
    · field_simp
    · apply NNReal.eq
      rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal', Real.coe_toNNReal']
      have hM2 : M⁻¹ ^ 2 * M ^ 2 = 1 := by
        rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hM.ne')]
      rcases le_total 0 L with hL | hL
      · rw [max_eq_left (mul_nonneg (sq_nonneg M) hL), max_eq_left hL, ← mul_assoc, hM2,
          one_mul]
      · rw [max_eq_right (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg M) hL), max_eq_right hL,
          mul_zero]
  · filter_upwards [hvar] with ω hv v hvh hrep
    obtain ⟨hUo, hb, -⟩ := hv
    have h1 := hrep b ((GFF.tsupport_bumpFun_subset hε).trans hb)
    have h2 := GFF.integral_mul_bumpFun_of_harmonic hUo hvh hε hb
    rw [h1, hbcoe, h2]
    have hm0 := GFF.bumpMass_pos.ne'
    field_simp

end InteractingSLE.Sec6
