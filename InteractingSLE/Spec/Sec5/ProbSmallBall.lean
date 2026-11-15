/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.BrownianMotion.Basic
import InteractingSLE.Stochastic.Bessel.Estimate
import InteractingSLE.Foundations.Brownian.Exit
import InteractingSLE.Foundations.Brownian.Harmonic

/-!
# Lemma 5.10: Brownian small-ball positivity

Packet PROVE-SEC5-B (specification §5.2, proof of Lemma 5.10, `source/spec/p097-144.md` L929–L959, and the
corrected crossing lemma, `source/spec/p433-480.md` §2.2: "a bounded-drift Girsanov comparison with ordinary
Brownian motion gives a positive lower bound", "Brownian small-ball positivity").

For a pre-Brownian motion `β` with continuous paths started at `0`, and `r > 0`,
`ℙ[sup_{t ≤ T} |β_t| < r] ≥ exp(−π² T / (8 r²))`.

Proof (the principal Dirichlet eigenfunction of `½ d²/dx²` on `(−r, r)`): with `c = π/(2r)`,
`M_t = e^{c² t/2} cos(c β_t)` is a martingale of the natural filtration (the increment `β_t − β_s` is
independent of the past and `N(0, t − s)`, whose cosine and sine transforms are `e^{−c²(t−s)/2}` and `0`).
Optional stopping at `σ = T ∧ (exit time of (−r, r))` gives `1 = 𝔼[M_σ]`. On exit before `T`, `|β_σ| = r`
and `cos(c β_σ) = cos(±π/2) = 0`; otherwise `M_σ ≤ e^{c² T/2}`. Hence `1 ≤ e^{c² T/2} ℙ[σ = T, no exit]`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

noncomputable section

namespace InteractingSLE

namespace Sec5

/-! ### Cosine and sine transforms of a centred Gaussian -/

theorem integral_cexp_gaussianReal (v : ℝ≥0) (c : ℝ) :
    ∫ x, Complex.exp (((c * x : ℝ) : ℂ) * Complex.I) ∂(gaussianReal 0 v)
      = ((Real.exp (-((v : ℝ) * c ^ 2 / 2)) : ℝ) : ℂ) := by
  have h := charFun_gaussianReal (μ := 0) (v := v) c
  rw [charFun_apply_real] at h
  have e : ∀ x : ℝ, Complex.exp (((c * x : ℝ) : ℂ) * Complex.I) = Complex.exp (c * x * Complex.I) :=
    fun x => by push_cast; ring_nf
  simp only [e, h]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem integrable_cexp_gaussianReal (v : ℝ≥0) (c : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (((c * x : ℝ) : ℂ) * Complex.I)) (gaussianReal 0 v) := by
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

/-- `𝔼[cos(c X)] = e^{−v c²/2}` for `X ~ N(0, v)`. -/
theorem integral_cos_gaussianReal (v : ℝ≥0) (c : ℝ) :
    ∫ x, Real.cos (c * x) ∂(gaussianReal 0 v) = Real.exp (-((v : ℝ) * c ^ 2 / 2)) := by
  have h := congrArg Complex.re (integral_cexp_gaussianReal v c)
  rw [← Complex.reCLM_apply, ← (Complex.reCLM).integral_comp_comm
    (integrable_cexp_gaussianReal v c)] at h
  simpa only [Complex.reCLM_apply, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re] using h

/-- `𝔼[sin(c X)] = 0` for `X ~ N(0, v)`. -/
theorem integral_sin_gaussianReal (v : ℝ≥0) (c : ℝ) :
    ∫ x, Real.sin (c * x) ∂(gaussianReal 0 v) = 0 := by
  have h := congrArg Complex.im (integral_cexp_gaussianReal v c)
  rw [← Complex.imCLM_apply, ← (Complex.imCLM).integral_comp_comm
    (integrable_cexp_gaussianReal v c)] at h
  simpa only [Complex.imCLM_apply, Complex.exp_ofReal_mul_I_im, Complex.ofReal_im] using h

/-! ### The cosine martingale -/

section Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {β : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure P] in
/-- A function of the past `σ(β_u : u ≤ s)` is independent of a function of the increment `β_t − β_s`
(the weak Markov property, `IsPreBrownianReal.indepFun_shift`). -/
theorem indepFun_natFilt_incr (hβ : IsPreBrownianReal β P) (hβm : ∀ t, Measurable (β t))
    {s t : ℝ≥0} (hst : s ≤ t) {f : Ω → ℝ} (hf : Measurable[Bessel.natFilt hβm s] f) {g : ℝ → ℝ}
    (hg : Measurable g) : IndepFun f (fun ω => g (β t ω - β s ω)) P := by
  have h := (hβ.indepFun_shift s).symm
  rw [IndepFun_iff_Indep] at h ⊢
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right h ?_) ?_
  · have h1 : (fun ω => g (β t ω - β s ω))
        = (fun F : ℝ≥0 → ℝ => g (F (t - s))) ∘ (fun ω u => β (s + u) ω - β s ω) := by
      funext ω
      simp [add_tsub_cancel_of_le hst]
    rw [h1]
    exact ((hg.comp (measurable_pi_apply _)).comp (Measurable.of_comap_le le_rfl)).comap_le
  · exact (hf.mono (Bessel.natFilt_le_past hβm s) le_rfl).comap_le

theorem integrable_of_abs_le_one {f : Ω → ℝ} (hf : Measurable f) (h : ∀ ω, |f ω| ≤ 1) :
    Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]; exact h ω)

/-- **The cosine transform of a Brownian step, conditionally on the past**: for `A ∈ σ(β_u : u ≤ s)`,
`∫_A cos(c β_t) = e^{−(t−s)c²/2} ∫_A cos(c β_s)`. -/
theorem setIntegral_cos_eq (hβ : IsPreBrownianReal β P) (hβm : ∀ t, Measurable (β t))
    {s t : ℝ≥0} (hst : s ≤ t) (c : ℝ) {A : Set Ω} (hA : MeasurableSet[Bessel.natFilt hβm s] A) :
    ∫ ω in A, Real.cos (c * β t ω) ∂P
      = Real.exp (-(((t : ℝ) - s) * c ^ 2 / 2)) * ∫ ω in A, Real.cos (c * β s ω) ∂P := by
  have hAm : MeasurableSet A := (Bessel.natFilt hβm).le s _ hA
  have hβs : Measurable[Bessel.natFilt hβm s] (β s) := Bessel.natFilt_adapted hβm s
  set f₁ : Ω → ℝ := A.indicator fun ω => Real.cos (c * β s ω) with hf₁def
  set g₁ : Ω → ℝ := A.indicator fun ω => Real.sin (c * β s ω) with hg₁def
  have hf₁ : Measurable[Bessel.natFilt hβm s] f₁ :=
    (Real.continuous_cos.measurable.comp (hβs.const_mul c)).indicator hA
  have hg₁ : Measurable[Bessel.natFilt hβm s] g₁ :=
    (Real.continuous_sin.measurable.comp (hβs.const_mul c)).indicator hA
  have hcm : Measurable fun x : ℝ => Real.cos (c * x) :=
    Real.continuous_cos.measurable.comp (measurable_const_mul c)
  have hsm : Measurable fun x : ℝ => Real.sin (c * x) :=
    Real.continuous_sin.measurable.comp (measurable_const_mul c)
  have i1 := indepFun_natFilt_incr hβ hβm hst hf₁ hcm
  have i2 := indepFun_natFilt_incr hβ hβm hst hg₁ hsm
  have hDm : Measurable fun ω => β t ω - β s ω := (hβm t).sub (hβm s)
  have hf₁m : Measurable f₁ := hf₁.mono ((Bessel.natFilt hβm).le s) le_rfl
  have hg₁m : Measurable g₁ := hg₁.mono ((Bessel.natFilt hβm).le s) le_rfl
  have hlaw := hβ.hasLaw_sub t s
  have hv : ((nndist t.1 s.1 : ℝ≥0) : ℝ) = (t : ℝ) - s := by
    rw [coe_nndist, Real.dist_eq, NNReal.val_eq_coe, NNReal.val_eq_coe,
      abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hst))]
  have hcos : ∫ ω, Real.cos (c * (β t ω - β s ω)) ∂P = Real.exp (-(((t : ℝ) - s) * c ^ 2 / 2)) := by
    have h := hlaw.integral_comp (f := fun x => Real.cos (c * x)) hcm.aestronglyMeasurable
    simp only [Function.comp_def, Pi.sub_apply] at h
    rw [h, integral_cos_gaussianReal, hv]
  have hsin : ∫ ω, Real.sin (c * (β t ω - β s ω)) ∂P = 0 := by
    have h := hlaw.integral_comp (f := fun x => Real.sin (c * x)) hsm.aestronglyMeasurable
    simp only [Function.comp_def, Pi.sub_apply] at h
    rw [h, integral_sin_gaussianReal]
  have hsplit : A.indicator (fun ω => Real.cos (c * β t ω))
      = fun ω => f₁ ω * Real.cos (c * (β t ω - β s ω)) - g₁ ω * Real.sin (c * (β t ω - β s ω)) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [hf₁def, hg₁def, Set.indicator_of_mem hω]
      rw [← Real.cos_add]
      ring_nf
    · simp [hf₁def, hg₁def, Set.indicator_of_notMem hω]
  have hint1 : Integrable (fun ω => f₁ ω * Real.cos (c * (β t ω - β s ω))) P := by
    refine integrable_of_abs_le_one (hf₁m.mul (hcm.comp hDm)) fun ω => ?_
    rw [abs_mul]
    refine (mul_le_mul ?_ (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    simp only [hf₁def, Set.indicator]
    split_ifs
    · exact Real.abs_cos_le_one _
    · simp
  have hint2 : Integrable (fun ω => g₁ ω * Real.sin (c * (β t ω - β s ω))) P := by
    refine integrable_of_abs_le_one (hg₁m.mul (hsm.comp hDm)) fun ω => ?_
    rw [abs_mul]
    refine (mul_le_mul ?_ (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    simp only [hg₁def, Set.indicator]
    split_ifs
    · exact Real.abs_sin_le_one _
    · simp
  rw [← integral_indicator hAm, hsplit, integral_sub hint1 hint2,
    i1.integral_fun_mul_eq_mul_integral hf₁m.aestronglyMeasurable (hcm.comp hDm).aestronglyMeasurable,
    i2.integral_fun_mul_eq_mul_integral hg₁m.aestronglyMeasurable (hsm.comp hDm).aestronglyMeasurable,
    hcos, hsin, mul_zero, sub_zero, hf₁def, integral_indicator hAm, mul_comm]

/-- The cosine martingale `M_t = e^{c² t/2} cos(c β_t)`. -/
def cosMart (c : ℝ) (β : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c ^ 2 * t / 2) * Real.cos (c * β t ω)

theorem measurable_cosMart (hβm : ∀ t, Measurable (β t)) (c : ℝ) (t : ℝ≥0) :
    Measurable[Bessel.natFilt hβm t] (cosMart c β t) :=
  measurable_const.mul (Real.continuous_cos.measurable.comp
    ((Bessel.natFilt_adapted hβm t).const_mul c))

theorem abs_cosMart_le (c : ℝ) {T t : ℝ≥0} (ht : t ≤ T) (ω : Ω) :
    |cosMart c β t ω| ≤ Real.exp (c ^ 2 * T / 2) := by
  rw [cosMart, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (c ^ 2 * t / 2) * |Real.cos (c * β t ω)| ≤ Real.exp (c ^ 2 * t / 2) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (c ^ 2 * T / 2) := by
        rw [mul_one, Real.exp_le_exp]
        have : (t : ℝ) ≤ T := by exact_mod_cast ht
        have := sq_nonneg c
        nlinarith

/-- **The cosine martingale** of a pre-Brownian motion in its natural filtration. -/
theorem martingale_cosMart (hβ : IsPreBrownianReal β P) (hβm : ∀ t, Measurable (β t)) (c : ℝ) :
    Martingale (cosMart c β) (Bessel.natFilt hβm) P := by
  refine ⟨fun t => (measurable_cosMart hβm c t).stronglyMeasurable, fun s t hst => ?_⟩
  have hint : ∀ u, Integrable (cosMart c β u) P := fun u =>
    Integrable.of_bound ((measurable_cosMart hβm c u).mono ((Bessel.natFilt hβm).le u)
      le_rfl).aestronglyMeasurable _ (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]; exact abs_cosMart_le c le_rfl ω)
  refine (ae_eq_condExp_of_forall_setIntegral_eq ((Bessel.natFilt hβm).le s) (hint t)
    (fun A _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (measurable_cosMart hβm c s).stronglyMeasurable.aestronglyMeasurable).symm
  simp only [cosMart]
  rw [integral_const_mul, integral_const_mul, setIntegral_cos_eq hβ hβm hst c hA, ← mul_assoc,
    ← Real.exp_add]
  congr 2
  ring

end Martingale

/-! ### The small-ball bound -/

section SmallBall

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {β : ℝ≥0 → Ω → ℝ}

/-- The open strip `|Re z| < r`, the domain whose exit time is the exit time of `β` from `(−r, r)`. -/
def reStrip (r : ℝ) : Set ℂ := {z | |z.re| < r}

theorem isOpen_reStrip (r : ℝ) : IsOpen (reStrip r) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const

theorem closure_reStrip_subset (r : ℝ) : closure (reStrip r) ⊆ {z | |z.re| ≤ r} :=
  closure_minimal (fun _ hz => le_of_lt (show _ < r from hz))
    (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const)

/-- **Brownian small-ball positivity.** For a pre-Brownian motion with measurable coordinates and
continuous paths started at `0`, `ℙ[∀ t ≤ T, |β_t| < r] ≥ exp(−π² T / (8 r²))`. -/
theorem exp_le_measureReal_forall_abs_lt (hβ : IsPreBrownianReal β P) (hβm : ∀ t, Measurable (β t))
    (hβc : ∀ ω, Continuous (β · ω)) (hβ0 : ∀ ω, β 0 ω = 0) {r : ℝ} (hr : 0 < r) (T : ℝ≥0) :
    Real.exp (-(Real.pi ^ 2 * T / (8 * r ^ 2))) ≤ P.real {ω | ∀ t ≤ T, |β t ω| < r} := by
  set c : ℝ := Real.pi / (2 * r) with hc
  set 𝓖 := Bessel.natFilt hβm
  set Z : ℝ≥0 → Ω → ℂ := fun t ω => (β t ω : ℂ) with hZ
  have hZm : ∀ t, Measurable[𝓖 t] (Z t) := fun t =>
    Complex.continuous_ofReal.measurable.comp (Bessel.natFilt_adapted hβm t)
  have hZc : ∀ ω, Continuous (Z · ω) := fun ω => Complex.continuous_ofReal.comp (hβc ω)
  set ex : Ω → ℝ≥0∞ := fun ω => exitTime (reStrip r) (Z · ω) with hex
  have hexst : IsStoppingTime 𝓖 ex := isStoppingTime_exitTime hZm hZc (isOpen_reStrip r)
  set σ : Ω → ℝ≥0∞ := fun ω => min (ex ω) T with hσdef
  have hσ : IsStoppingTime 𝓖 σ := hexst.min (isStoppingTime_const 𝓖 T)
  have hσT : ∀ ω, σ ω ≤ T := fun ω => min_le_right _ _
  have hM := martingale_cosMart hβ hβm c
  have hMc : ∀ ω, Continuous (cosMart c β · ω) := fun ω =>
    ((Real.continuous_exp.comp ((continuous_const.mul NNReal.continuous_coe).div_const 2))).mul
      (Real.continuous_cos.comp (continuous_const.mul (hβc ω)))
  have hos := integral_untopA_eq_of_le hM hMc (fun t ht ω => abs_cosMart_le c ht ω) hσ hσT
  have h0 : ∫ ω, cosMart c β 0 ω ∂P = 1 := by
    simp [cosMart, hβ0]
  rw [h0] at hos
  set E : Set Ω := {ω | (T : ℝ≥0∞) < ex ω} with hE
  have hEm : MeasurableSet E :=
    measurableSet_lt measurable_const (measurable_exitTime (fun t => (hZm t).mono (𝓖.le t) le_rfl)
      hZc (isOpen_reStrip r))
  have hD0 : ∀ ω, Z 0 ω ∈ reStrip r := fun ω => by
    simp [hZ, reStrip, hβ0, hr]
  -- pointwise bound `M_σ ≤ e^{c² T/2} 1_E`
  have hbound : ∀ ω, cosMart c β (σ ω).toNNReal ω ≤ E.indicator (fun _ => Real.exp (c ^ 2 * T / 2)) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      exact (le_abs_self _).trans (abs_cosMart_le c (by
        have := hσT ω
        exact (ENNReal.toNNReal_le_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top this)
          ENNReal.coe_ne_top).2 this) ω)
    · rw [Set.indicator_of_notMem hω]
      have hle : ex ω ≤ T := le_of_not_gt hω
      have hfin : ex ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
      have hσω : σ ω = ex ω := min_eq_left hle
      have hnot : exitPoint (reStrip r) (Z · ω) ∉ reStrip r :=
        exitPoint_not_mem (isOpen_reStrip r) (hZc ω) hfin
      have hcl := closure_reStrip_subset r
        (exitPoint_mem_closure (isOpen_reStrip r) (hZc ω) (hD0 ω) hfin)
      have e1 : (exitPoint (reStrip r) (Z · ω)).re = β (ex ω).toNNReal ω := by
        simp [exitPoint, hZ, hex]
      have habs : |β (ex ω).toNNReal ω| = r := by
        have h1 : ¬ |(exitPoint (reStrip r) (Z · ω)).re| < r := hnot
        have h2 : |(exitPoint (reStrip r) (Z · ω)).re| ≤ r := hcl
        rw [e1] at h1 h2
        exact le_antisymm h2 (not_lt.1 h1)
      have hcr : c * r = Real.pi / 2 := by
        rw [hc]; field_simp
      have hcos : Real.cos (c * β (ex ω).toNNReal ω) = 0 := by
        rcases (abs_eq hr.le).1 habs with h | h
        · rw [h, hcr, Real.cos_pi_div_two]
        · rw [h, mul_neg, hcr, Real.cos_neg, Real.cos_pi_div_two]
      rw [hσω, cosMart, hcos, mul_zero]
  have hMσm : Integrable (fun ω => cosMart c β (σ ω).toNNReal ω) P := by
    by_contra hni
    rw [integral_undef hni] at hos
    exact zero_ne_one hos
  have hind : Integrable (E.indicator fun _ => Real.exp (c ^ 2 * T / 2)) P :=
    (integrable_const _).indicator hEm
  have h1 : 1 ≤ Real.exp (c ^ 2 * T / 2) * P.real E := by
    calc (1 : ℝ) = ∫ ω, cosMart c β (σ ω).toNNReal ω ∂P := hos.symm
      _ ≤ ∫ ω, E.indicator (fun _ => Real.exp (c ^ 2 * T / 2)) ω ∂P :=
          integral_mono hMσm hind hbound
      _ = Real.exp (c ^ 2 * T / 2) * P.real E := by
          rw [integral_indicator_const _ hEm, smul_eq_mul, mul_comm]
  have hsub : E ⊆ {ω | ∀ t ≤ T, |β t ω| < r} := by
    intro ω hω t ht
    have hlt : (t : ℝ≥0∞) < ex ω := lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hω
    have := mem_of_lt_exitTime hlt
    simpa [reStrip, hZ] using this
  have hexp : Real.exp (-(Real.pi ^ 2 * T / (8 * r ^ 2))) = (Real.exp (c ^ 2 * T / 2))⁻¹ := by
    rw [← Real.exp_neg, hc]
    congr 1
    field_simp
    ring
  rw [hexp]
  calc (Real.exp (c ^ 2 * T / 2))⁻¹ ≤ P.real E := by
        rw [inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
        linarith
    _ ≤ P.real {ω | ∀ t ≤ T, |β t ω| < r} := measureReal_mono hsub

end SmallBall

end Sec5

end InteractingSLE
