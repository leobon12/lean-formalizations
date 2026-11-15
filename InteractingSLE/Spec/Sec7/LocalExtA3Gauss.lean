/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtA2Pair
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# The local comparison of Aux. lemma 55: the complex tilt of a conditionally Gaussian pair

Packet PROVE-LOCEXT-A3 (step 5's kernel input, `SrcJointKernelStatement`). Source: Aux. lemma 55, proof
(`source/spec/p241-288.md` L196–L206, p. 250): "Conditional Cameron–Martin shifting changes the mean to `C_{K_t} − P_t f`
and leaves this covariance unchanged."

Abstract probability used for the conditional Cameron–Martin shift:

* `exists_subseq_ae_tendsto_condExp`: bounded a.s. convergence `f_k → g` gives a.s. convergence of the conditional
  expectations along a subsequence (`L¹` contraction of `condExp`, convergence in measure);
* `ae_condExp_cexp_of_tendsto_on`: a conditional Gaussian characteristic function on an event `D` (not necessarily
  measurable) passes to limits of the variables and of the parameters;
* `integral_tilt_of_charFun`: if a probability measure `ν` on `ℝ × ℝ` has the characteristic function of a Gaussian
  pair (means `μ₁, μ₂`, covariances `s₁₁, s₁₂, s₂₂`) at every rational frequency, then
  `∫ e^{−y₂} e^{i y₁} dν = e^{−μ₂ + s₂₂/2} · exp(i(μ₁ − s₁₂) − s₁₁/2)` (each projection `s y₁ − y₂` is Gaussian, so the
  tilted first marginal and the shifted Gaussian `e^{−μ₂+s₂₂/2} N(μ₁ − s₁₂, s₁₁)` have the same moment generating
  function, hence the same complex one, `ProbabilityTheory.eqOn_complexMGF_of_mgf'`);
* **`ae_condExp_tilt_of_joint`**: the conditional version, through the regular conditional distribution of `(Y₁, Y₂)`
  given `m` (`ProbabilityTheory.condDistrib` along `id : (Ω, mΩ) → (Ω, m)`), pointwise on `D`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

/-! ### Conditional expectations along a subsequence -/

section Subseq

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Bounded a.s. convergence passes to conditional expectations along a subsequence.** -/
theorem exists_subseq_ae_tendsto_condExp [IsFiniteMeasure P] {f : ℕ → Ω → ℂ} {g : Ω → ℂ}
    (hfm : ∀ k, AEStronglyMeasurable (f k) P) (hb : ∀ k, ∀ᵐ ω ∂P, ‖f k ω‖ ≤ 1)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 (g ω))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => (P[f (ns k) | m]) ω) atTop (𝓝 ((P[g | m]) ω)) := by
  have hgm : AEStronglyMeasurable g P := aestronglyMeasurable_of_tendsto_ae _ hfm hlim
  have hgb : ∀ᵐ ω ∂P, ‖g ω‖ ≤ 1 := by
    filter_upwards [hlim, ae_all_iff.2 hb] with ω h1 h2
    exact le_of_tendsto' ((continuous_norm.tendsto _).comp h1) h2
  have hfi : ∀ k, Integrable (f k) P := fun k => Integrable.of_bound (hfm k) 1 (hb k)
  have hgi : Integrable g P := Integrable.of_bound hgm 1 hgb
  have hL : Tendsto (fun k => ∫⁻ ω, ENNReal.ofReal ‖f k ω - g ω‖ ∂P) atTop (𝓝 0) :=
    tendsto_lintegral_norm_of_dominated_convergence hfm (hasFiniteIntegral_const 1) hb hlim
  have hL' : Tendsto (fun k => eLpNorm (f k - g) 1 P) atTop (𝓝 0) := by
    refine hL.congr fun k => ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp only [Pi.sub_apply, ofReal_norm]
  have hC : Tendsto (fun k => eLpNorm (P[f k | m] - P[g | m]) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL' (fun _ => bot_le) fun k => ?_
    have e : P[f k | m] - P[g | m] =ᵐ[P] P[f k - g | m] := (condExp_sub (hfi k) hgi m).symm
    rw [eLpNorm_congr_ae e]
    exact eLpNorm_condExp_le_eLpNorm _ le_rfl
  have hM : TendstoInMeasure P (fun k => P[f k | m]) atTop (P[g | m]) :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero (fun k => integrable_condExp.aestronglyMeasurable)
      integrable_condExp.aestronglyMeasurable hC
  exact hM.exists_seq_tendsto_ae

/-- **A conditional Gaussian characteristic function on an event passes to limits.** If
`E[e^{i Y_k} | m] = exp(i a_k − q_k/2)` almost surely on `D`, `Y_k → Y` almost surely, and `a_k → a`, `q_k → q`
almost surely on `D`, then `E[e^{i Y} | m] = exp(i a − q/2)` almost surely on `D` (`D` need not be measurable). -/
theorem ae_condExp_cexp_of_tendsto_on [IsFiniteMeasure P] {Y : ℕ → Ω → ℝ} {Y' : Ω → ℝ}
    {a q : ℕ → Ω → ℝ} {a' q' : Ω → ℝ} {D : Set Ω} (hYm : ∀ k, AEMeasurable (Y k) P)
    (hk : ∀ k, ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω => Complex.exp (Complex.I * (Y k ω : ℂ)) | m]) ω = cfVal (a k ω) (q k ω))
    (hY : ∀ᵐ ω ∂P, Tendsto (fun k => Y k ω) atTop (𝓝 (Y' ω)))
    (haq : ∀ᵐ ω ∂P, ω ∈ D → Tendsto (fun k => a k ω) atTop (𝓝 (a' ω)) ∧
      Tendsto (fun k => q k ω) atTop (𝓝 (q' ω))) :
    ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω => Complex.exp (Complex.I * (Y' ω : ℂ)) | m]) ω = cfVal (a' ω) (q' ω) := by
  have hfm : ∀ k, AEStronglyMeasurable (fun ω => Complex.exp (Complex.I * (Y k ω : ℂ))) P := fun k =>
    (Complex.measurable_exp.comp_aemeasurable
      (aemeasurable_const.mul (Complex.measurable_ofReal.comp_aemeasurable (hYm k)))).aestronglyMeasurable
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun k => Complex.exp (Complex.I * (Y k ω : ℂ))) atTop
      (𝓝 (Complex.exp (Complex.I * (Y' ω : ℂ)))) := by
    filter_upwards [hY] with ω h1
    exact (Complex.continuous_exp.tendsto _).comp
      (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp h1))
  obtain ⟨ns, hns, hsub⟩ := exists_subseq_ae_tendsto_condExp (m := m) hfm
    (fun k => ae_of_all _ fun ω => (norm_cexp_I_mul _).le) hlim
  filter_upwards [hsub, ae_all_iff.2 hk, haq] with ω h1 h2 h3 hD
  obtain ⟨ha, hq⟩ := h3 hD
  have h4 : Tendsto (fun k => cfVal (a (ns k) ω) (q (ns k) ω)) atTop (𝓝 (cfVal (a' ω) (q' ω))) :=
    (continuous_cfVal.tendsto _).comp ((ha.comp hns.tendsto_atTop).prodMk_nhds (hq.comp hns.tendsto_atTop))
  exact tendsto_nhds_unique (h1.congr fun k => h2 (ns k) hD) h4

end Subseq

/-! ### The complex tilt of a Gaussian pair -/

section Tilt

/-- The characteristic function of a probability measure on `ℝ × ℝ` is continuous in the frequency. -/
theorem continuous_integral_cexp_pair (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] :
    Continuous fun p : ℝ × ℝ => ∫ y, Complex.exp (Complex.I * ((p.1 * y.1 + p.2 * y.2 : ℝ) : ℂ)) ∂ν := by
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun p => ?_) (fun p => ae_of_all _ fun y => ?_)
    (integrable_const 1) (ae_of_all _ fun y => ?_)
  · exact (by fun_prop : Continuous fun y : ℝ × ℝ =>
      Complex.exp (Complex.I * ((p.1 * y.1 + p.2 * y.2 : ℝ) : ℂ))).aestronglyMeasurable
  · exact (norm_cexp_I_mul _).le
  · fun_prop

variable {ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure ν] {μ₁ μ₂ s₁₁ s₁₂ s₂₂ : ℝ}

/-- A Gaussian characteristic function at the rational frequencies is one at every frequency. -/
theorem integral_cexp_pair_eq_of_rat
    (hν : ∀ a b : ℚ, ∫ y, Complex.exp (Complex.I * (((a : ℝ) * y.1 + (b : ℝ) * y.2 : ℝ) : ℂ)) ∂ν =
      cfVal ((a : ℝ) * μ₁ + (b : ℝ) * μ₂) ((a : ℝ) ^ 2 * s₁₁ + 2 * (a : ℝ) * (b : ℝ) * s₁₂ + (b : ℝ) ^ 2 * s₂₂))
    (a b : ℝ) :
    ∫ y, Complex.exp (Complex.I * ((a * y.1 + b * y.2 : ℝ) : ℂ)) ∂ν =
      cfVal (a * μ₁ + b * μ₂) (a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂) := by
  have hg : Continuous fun p : ℝ × ℝ =>
      cfVal (p.1 * μ₁ + p.2 * μ₂) (p.1 ^ 2 * s₁₁ + 2 * p.1 * p.2 * s₁₂ + p.2 ^ 2 * s₂₂) :=
    continuous_cfVal.comp (f := fun p : ℝ × ℝ =>
      (p.1 * μ₁ + p.2 * μ₂, p.1 ^ 2 * s₁₁ + 2 * p.1 * p.2 * s₁₂ + p.2 ^ 2 * s₂₂)) (by fun_prop)
  have hd : DenseRange (Prod.map (Rat.cast : ℚ → ℝ) (Rat.cast : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h := Continuous.ext_on hd (continuous_integral_cexp_pair ν) hg (by
    rintro _ ⟨q, rfl⟩
    exact hν q.1 q.2)
  exact congrFun h (a, b)

/-- **Every projection of a Gaussian pair is Gaussian**: `ν ∘ (a y₁ + b y₂)⁻¹ = N(a μ₁ + b μ₂, q(a, b))`. -/
theorem exists_map_eq_gaussianReal
    (hν : ∀ a b : ℝ, ∫ y, Complex.exp (Complex.I * ((a * y.1 + b * y.2 : ℝ) : ℂ)) ∂ν =
      cfVal (a * μ₁ + b * μ₂) (a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂)) (a b : ℝ) :
    0 ≤ a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂ ∧
      ν.map (fun y => a * y.1 + b * y.2) =
        gaussianReal (a * μ₁ + b * μ₂) (a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂).toNNReal := by
  have hq : 0 ≤ a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂ := by
    have h1 : ‖∫ y, Complex.exp (Complex.I * ((a * y.1 + b * y.2 : ℝ) : ℂ)) ∂ν‖ ≤ 1 := by
      have := norm_integral_le_of_norm_le_const (μ := ν) (C := 1)
        (f := fun y : ℝ × ℝ => Complex.exp (Complex.I * ((a * y.1 + b * y.2 : ℝ) : ℂ)))
        (ae_of_all _ fun y => (norm_cexp_I_mul _).le)
      simpa using this
    rw [hν, norm_cfVal, Real.exp_le_one_iff] at h1
    linarith
  refine ⟨hq, ?_⟩
  apply Measure.ext_of_charFun
  funext t
  have hL : Measurable fun y : ℝ × ℝ => a * y.1 + b * y.2 := by fun_prop
  rw [charFun_apply_real, integral_map hL.aemeasurable (by fun_prop), charFun_gaussianReal]
  have e : ∀ y : ℝ × ℝ, Complex.exp (↑t * ↑(a * y.1 + b * y.2) * Complex.I) =
      Complex.exp (Complex.I * (((t * a) * y.1 + (t * b) * y.2 : ℝ) : ℂ)) := fun y => by
    congr 1; push_cast; ring
  simp_rw [e]
  rw [hν, cfVal, Real.coe_toNNReal _ hq]
  congr 1
  push_cast
  ring

/-- **The exponential moments of a Gaussian pair.** -/
theorem integrable_exp_and_integral_of_charFun
    (hν : ∀ a b : ℝ, ∫ y, Complex.exp (Complex.I * ((a * y.1 + b * y.2 : ℝ) : ℂ)) ∂ν =
      cfVal (a * μ₁ + b * μ₂) (a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂)) (a b : ℝ) :
    Integrable (fun y : ℝ × ℝ => Real.exp (a * y.1 + b * y.2)) ν ∧
      ∫ y, Real.exp (a * y.1 + b * y.2) ∂ν =
        Real.exp (a * μ₁ + b * μ₂ + (a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂) / 2) := by
  obtain ⟨hq, hmap⟩ := exists_map_eq_gaussianReal hν a b
  have hL : Measurable fun y : ℝ × ℝ => a * y.1 + b * y.2 := by fun_prop
  have hi : Integrable (fun x : ℝ => Real.exp x) (ν.map fun y => a * y.1 + b * y.2) := by
    rw [hmap]
    simpa using integrable_exp_mul_gaussianReal (μ := a * μ₁ + b * μ₂) (v := (a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂).toNNReal) 1
  refine ⟨(integrable_map_measure (by fun_prop) hL.aemeasurable).1 hi, ?_⟩
  have h1 : ∫ y, Real.exp (a * y.1 + b * y.2) ∂ν =
      ∫ x, Real.exp x ∂(ν.map fun y => a * y.1 + b * y.2) :=
    (integral_map hL.aemeasurable (by fun_prop)).symm
  rw [h1, hmap]
  have h2 := congrFun (mgf_id_gaussianReal (μ := a * μ₁ + b * μ₂) (v := (a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂).toNNReal)) 1
  simp only [mgf, id, one_mul, mul_one, one_pow, Real.coe_toNNReal _ hq] at h2
  exact h2

/-- **The complex tilt of a Gaussian pair**: if `ν` has the characteristic function of a Gaussian pair (means
`μ₁, μ₂`, covariances `s₁₁, s₁₂, s₂₂`), then `∫ e^{−y₂} e^{i y₁} dν = e^{−μ₂ + s₂₂/2} · exp(i(μ₁ − s₁₂) − s₁₁/2)`. -/
theorem integral_tilt_of_charFun
    (hν : ∀ a b : ℝ, ∫ y, Complex.exp (Complex.I * ((a * y.1 + b * y.2 : ℝ) : ℂ)) ∂ν =
      cfVal (a * μ₁ + b * μ₂) (a ^ 2 * s₁₁ + 2 * a * b * s₁₂ + b ^ 2 * s₂₂)) :
    ∫ y, ((Real.exp (-y.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (y.1 : ℂ)) ∂ν =
      ((Real.exp (-μ₂ + s₂₂ / 2) : ℝ) : ℂ) * cfVal (μ₁ - s₁₂) s₁₁ := by
  have hs11 : 0 ≤ s₁₁ := by
    obtain ⟨hq, -⟩ := exists_map_eq_gaussianReal hν 1 0
    simpa using hq
  set f : ℝ × ℝ → ℝ≥0 := fun y => (Real.exp (-y.2)).toNNReal with hf_def
  have hf : Measurable f := by fun_prop
  have hfv : ∀ y, (f y : ℝ) = Real.exp (-y.2) := fun y => Real.coe_toNNReal _ (Real.exp_pos _).le
  set ρ : Measure (ℝ × ℝ) := ν.withDensity fun y => (f y : ℝ≥0∞) with hρ
  set c : ℝ := Real.exp (-μ₂ + s₂₂ / 2) with hc
  set ρ' : Measure ℝ := ENNReal.ofReal c • gaussianReal (μ₁ - s₁₂) s₁₁.toNNReal with hρ'
  have hρs : ∀ s : ℝ, (∀ g : ℝ × ℝ → ℝ, ∫ y, g y ∂ρ = ∫ y, Real.exp (-y.2) * g y ∂ν) := fun s g => by
    rw [hρ, integral_withDensity_eq_integral_smul hf]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show f y • g y = Real.exp (-y.2) * g y
    rw [NNReal.smul_def, smul_eq_mul, hfv]
  have hexp : ∀ s y, Real.exp (-(y : ℝ × ℝ).2) * Real.exp (s * y.1) = Real.exp (s * y.1 + (-1) * y.2) :=
    fun s y => by rw [← Real.exp_add]; ring_nf
  have hmgf1 : ∀ s, mgf Prod.fst ρ s =
      Real.exp (s * μ₁ + (-1) * μ₂ + (s ^ 2 * s₁₁ + 2 * s * (-1) * s₁₂ + (-1) ^ 2 * s₂₂) / 2) := fun s => by
    rw [mgf, hρs s]
    simp_rw [hexp s]
    exact (integrable_exp_and_integral_of_charFun hν s (-1)).2
  have hmgf : mgf Prod.fst ρ = mgf id ρ' := by
    funext s
    rw [hmgf1, hρ', mgf, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    have h2 := congrFun (mgf_id_gaussianReal (μ := μ₁ - s₁₂) (v := s₁₁.toNNReal)) s
    rw [mgf] at h2
    rw [h2, Real.coe_toNNReal _ hs11, smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  have hρ0 : ρ ≠ 0 := fun h => by
    have := hmgf1 0
    rw [h] at this
    simp only [mgf, integral_zero_measure] at this
    exact (Real.exp_pos _).ne' this.symm
  have hρ'0 : ρ' ≠ 0 := fun h => by
    have := hmgf1 0
    rw [hmgf, h] at this
    simp only [mgf, integral_zero_measure] at this
    exact (Real.exp_pos _).ne' this.symm
  have hset : integrableExpSet Prod.fst ρ = univ := by
    ext s
    simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
    rw [hρ, integrable_withDensity_iff_integrable_smul hf]
    refine (integrable_exp_and_integral_of_charFun hν s (-1)).1.congr (ae_of_all _ fun y => ?_)
    show Real.exp (s * y.1 + -1 * y.2) = f y • Real.exp (s * y.1)
    rw [NNReal.smul_def, smul_eq_mul, hfv, hexp]
  have hEq := eqOn_complexMGF_of_mgf' hmgf (iff_of_false hρ0 hρ'0)
    (show Complex.I ∈ {z : ℂ | z.re ∈ interior (integrableExpSet Prod.fst ρ)} by
      simp [hset])
  have hL : complexMGF Prod.fst ρ Complex.I =
      ∫ y, ((Real.exp (-y.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (y.1 : ℂ)) ∂ν := by
    rw [complexMGF, hρ, integral_withDensity_eq_integral_smul hf]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show f y • Complex.exp (Complex.I * (y.1 : ℂ)) = _
    rw [NNReal.smul_def, Complex.real_smul, hfv]
  have hR : complexMGF id ρ' Complex.I = ((c : ℝ) : ℂ) * cfVal (μ₁ - s₁₂) s₁₁ := by
    rw [hρ', complexMGF, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, ← complexMGF,
      complexMGF_id_gaussianReal, Complex.real_smul, cfVal, Real.coe_toNNReal _ hs11]
    congr 2
    push_cast
    rw [Complex.I_sq]
    ring
  rw [← hL, hEq, hR]

end Tilt

/-! ### The conditional version -/

section Cond

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

variable (m) in
/-- **The regular conditional distribution** of `Y : Ω → ℝ × ℝ` given the sub-σ-algebra `m`, at `ω`
(`ProbabilityTheory.condDistrib` along `id : (Ω, mΩ) → (Ω, m)`). -/
def condLaw (Y : Ω → ℝ × ℝ) (P : Measure Ω) [IsFiniteMeasure P] (ω : Ω) : Measure (ℝ × ℝ) :=
  @condDistrib Ω Ω (ℝ × ℝ) _ _ _ mΩ m Y id P _ ω

instance isProbabilityMeasure_condLaw [IsFiniteMeasure P] (Y : Ω → ℝ × ℝ) (ω : Ω) :
    IsProbabilityMeasure (condLaw m Y P ω) := by
  unfold condLaw; infer_instance

/-- Conditional expectations given `m` are integrals against `condLaw`. -/
theorem condExp_ae_eq_integral_condLaw [IsFiniteMeasure P] (hm : m ≤ mΩ) {Y : Ω → ℝ × ℝ}
    (hY : Measurable Y) {f : ℝ × ℝ → ℂ} (hf : StronglyMeasurable f)
    (hint : Integrable (fun ω => f (Y ω)) P) :
    P[fun ω => f (Y ω) | m] =ᵐ[P] fun ω => ∫ y, f y ∂condLaw m Y P ω := by
  have h := condExp_ae_eq_integral_condDistrib (mβ := m) (X := (id : Ω → Ω)) (measurable_id'' hm)
    hY.aemeasurable hf hint
  rwa [MeasurableSpace.comap_id] at h

/-- **The conditional complex tilt of a conditionally Gaussian pair.** If, almost surely on an event `D` (not
necessarily measurable), `(Y₁, Y₂)` has given `m` the characteristic function of a Gaussian pair with means
`μ₁, μ₂` and covariances `s₁₁, s₁₂, s₂₂`, then almost surely on `D`
`E[e^{−Y₂} e^{i Y₁} | m] = e^{−μ₂ + s₂₂/2} · exp(i(μ₁ − s₁₂) − s₁₁/2)`. -/
theorem ae_condExp_tilt_of_joint [IsProbabilityMeasure P] (hm : m ≤ mΩ) {Y₁ Y₂ : Ω → ℝ}
    (hY₁ : Measurable Y₁) (hY₂ : Measurable Y₂) (hint : Integrable (fun ω => Real.exp (-Y₂ ω)) P)
    {D : Set Ω} {μ₁ μ₂ s₁₁ s₁₂ s₂₂ : Ω → ℝ}
    (hjoint : ∀ a b : ℝ, ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => Complex.exp (Complex.I * ((a * Y₁ ω' + b * Y₂ ω' : ℝ) : ℂ)) | m]) ω =
        cfVal (a * μ₁ ω + b * μ₂ ω) (a ^ 2 * s₁₁ ω + 2 * a * b * s₁₂ ω + b ^ 2 * s₂₂ ω)) :
    ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => ((Real.exp (-Y₂ ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (Y₁ ω' : ℂ)) | m]) ω =
        ((Real.exp (-μ₂ ω + s₂₂ ω / 2) : ℝ) : ℂ) * cfVal (μ₁ ω - s₁₂ ω) (s₁₁ ω) := by
  set Y : Ω → ℝ × ℝ := fun ω => (Y₁ ω, Y₂ ω) with hYdef
  have hY : Measurable Y := hY₁.prodMk hY₂
  have h1 : ∀ q : ℚ × ℚ,
      P[fun ω' => Complex.exp (Complex.I * (((q.1 : ℝ) * Y₁ ω' + (q.2 : ℝ) * Y₂ ω' : ℝ) : ℂ)) | m] =ᵐ[P]
        fun ω => ∫ y, Complex.exp (Complex.I * (((q.1 : ℝ) * y.1 + (q.2 : ℝ) * y.2 : ℝ) : ℂ)) ∂condLaw m Y P ω :=
    fun q => by
      have hc : Continuous fun y : ℝ × ℝ =>
          Complex.exp (Complex.I * (((q.1 : ℝ) * y.1 + (q.2 : ℝ) * y.2 : ℝ) : ℂ)) := by fun_prop
      refine condExp_ae_eq_integral_condLaw hm hY hc.stronglyMeasurable ?_
      exact Integrable.of_bound (hc.measurable.comp hY).aestronglyMeasurable 1
        (ae_of_all _ fun ω => (norm_cexp_I_mul _).le)
  have h2 : P[fun ω' => ((Real.exp (-Y₂ ω') : ℝ) : ℂ) * Complex.exp (Complex.I * (Y₁ ω' : ℂ)) | m] =ᵐ[P]
      fun ω => ∫ y, ((Real.exp (-y.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (y.1 : ℂ)) ∂condLaw m Y P ω := by
    have hc : Continuous fun y : ℝ × ℝ => ((Real.exp (-y.2) : ℝ) : ℂ) * Complex.exp (Complex.I * (y.1 : ℂ)) := by
      fun_prop
    refine condExp_ae_eq_integral_condLaw hm hY hc.stronglyMeasurable ?_
    refine hint.mono' (hc.measurable.comp hY).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), norm_cexp_I_mul, mul_one, le_refl, hYdef]
  have h3 : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P, ω ∈ D →
      (P[fun ω' => Complex.exp (Complex.I * (((q.1 : ℝ) * Y₁ ω' + (q.2 : ℝ) * Y₂ ω' : ℝ) : ℂ)) | m]) ω =
        cfVal ((q.1 : ℝ) * μ₁ ω + (q.2 : ℝ) * μ₂ ω)
          ((q.1 : ℝ) ^ 2 * s₁₁ ω + 2 * (q.1 : ℝ) * (q.2 : ℝ) * s₁₂ ω + (q.2 : ℝ) ^ 2 * s₂₂ ω) :=
    fun q => hjoint q.1 q.2
  filter_upwards [ae_all_iff.2 h1, h2, ae_all_iff.2 h3] with ω e1 e2 e3 hD
  rw [e2]
  exact integral_tilt_of_charFun (integral_cexp_pair_eq_of_rat fun a b =>
    (e1 (a, b)).symm.trans (e3 (a, b) hD))

end Cond

end LocalExt

end InteractingSLE
