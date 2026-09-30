import QuantumZipper.Statements.Thm11
import QuantumZipper.Proofs.Thm11.CharFunFwd
import QuantumZipper.Proofs.GFF.K3.GreenH

/-!
# Theorem 1.1 addendum, AD-8: a conditional zero-boundary GFF has a.s. linear pairings

For `IsCondZeroBoundaryGFFH U Y X' P` with `U ω` open and `U ω ⊆ ℍ`, the raw pairings of `X'`
are almost surely linear in the test function (`linearPairingH_of_condGFF`).

Proof (own elementary argument; standard Gaussian fact): the covariance `zeroGFFTestCov U` is the
Gram form of the vectors `u σ = R(σ⁺|_U) − R(σ⁻|_U)` (`R` = Riesz representative in the gradient
space, as in `K3.zeroGFFTestCov_psd`), and `σ ↦ u σ` is linear on test functions because
`⟪u σ, ∇f⟫ = ∫_U σ f` for `f ∈ zeroSpace U`. So for `ρ₃ = aρ₁ + ρ₂` the conditional variance of
`Z = a⟨X',ρ₁⟩ + ⟨X',ρ₂⟩ − ⟨X',ρ₃⟩` vanishes, `E e^{isZ} = 1` for all `s`, and `Z = 0` a.s. by
injectivity of the characteristic function.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set
open scoped RealInnerProductSpace ENNReal NNReal

namespace QuantumZipper
namespace Thm11Asm

open K3

/-- The Gram vector `u σ = R(σ⁺|_U) − R(σ⁻|_U)` of a test function. -/
def covVec (U : Set ℂ) (σ : ℂ → ℝ) : GradSpace U :=
  rieszVec U (zeroSpace U) ((testMeasPos σ).restrict U) -
    rieszVec U (zeroSpace U) ((testMeasNeg σ).restrict U)

theorem zeroGFFTestCov_eq_inner {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) (σ τ : TestFun H) :
    zeroGFFTestCov U σ.1 τ.1 = ⟪covVec U σ.1, covVec U τ.1⟫ := by
  obtain ⟨hσp, hσn⟩ := isAdmissibleH_testMeas_of_testFun σ
  obtain ⟨hτp, hτn⟩ := isAdmissibleH_testMeas_of_testFun τ
  unfold zeroGFFTestCov covVec
  rw [dualCov_eq_inner_of_subset_H hU hUH hσp hτp, dualCov_eq_inner_of_subset_H hU hUH hσp hτn,
    dualCov_eq_inner_of_subset_H hU hUH hσn hτp, dualCov_eq_inner_of_subset_H hU hUH hσn hτn]
  simp only [inner_sub_left, inner_sub_right]
  ring

theorem covVec_mem (U : Set ℂ) (σ : ℂ → ℝ) : covVec U σ ∈ gradClosure U (zeroSpace U) :=
  sub_mem rieszVec_mem rieszVec_mem

theorem integral_testMeas_restrict {σ f : ℂ → ℝ} (hσ : Continuous σ) (hf : Continuous f)
    (hfc : HasCompactSupport f) {U : Set ℂ} (hU : MeasurableSet U) :
    ∫ z, f z ∂((testMeasPos σ).restrict U) - ∫ z, f z ∂((testMeasNeg σ).restrict U) =
      ∫ z in U, σ z * f z := by
  have i1 : Integrable (fun z => max (σ z) 0 * f z) (volume.restrict U) :=
    (((hσ.max continuous_const).mul hf).integrable_of_hasCompactSupport
      (hfc.mul_left (f := fun z => max (σ z) 0))).integrableOn
  have i2 : Integrable (fun z => max (-σ z) 0 * f z) (volume.restrict U) :=
    (((hσ.neg.max continuous_const).mul hf).integrable_of_hasCompactSupport
      (hfc.mul_left (f := fun z => max (-σ z) 0))).integrableOn
  rw [testMeasPos, testMeasNeg, restrict_withDensity hU, restrict_withDensity hU,
    integral_withDensity_eq_integral_toReal_smul (f := fun z => ENNReal.ofReal (σ z))
      hσ.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (f := fun z => ENNReal.ofReal (-σ z))
      hσ.measurable.neg.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]
  rw [← integral_sub i1 i2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rcases le_total 0 (σ z) with hz | hz
  · rw [max_eq_left hz, max_eq_right (by linarith)]; ring
  · rw [max_eq_right hz, max_eq_left (by linarith)]; ring

theorem inner_covVec_gradFeat {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) (σ : TestFun H)
    (hpos : ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g) {f : ℂ → ℝ} (hf : f ∈ zeroSpace U) :
    ⟪covVec U σ.1, gradFeat U f⟫ = ∫ z in U, σ.1 z * f z := by
  obtain ⟨hσp, hσn⟩ := isAdmissibleH_testMeas_of_testFun σ
  have hV := isDNSpace_zeroSpace U
  rw [covVec, inner_sub_left,
    pair_rieszVec hV (isAdmissibleDual_restrict_of_subset_H hU hUH hσp) hpos f hf,
    pair_rieszVec hV (isAdmissibleDual_restrict_of_subset_H hU hUH hσn) hpos f hf]
  exact integral_testMeas_restrict σ.2.1.continuous hf.1.continuous hf.2.1 hU.measurableSet

theorem eq_zero_of_inner_gradFeat {U : Set ℂ} {w : GradSpace U}
    (hw : w ∈ gradClosure U (zeroSpace U)) (h : ∀ f ∈ zeroSpace U, ⟪w, gradFeat U f⟫ = 0) :
    w = 0 := by
  have hle : gradClosure U (zeroSpace U) ≤ LinearMap.ker (innerₛₗ ℝ w) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨f, hf, rfl⟩
      simpa using h f hf
    · have e : ((LinearMap.ker (innerₛₗ ℝ w) : Submodule ℝ (GradSpace U)) : Set (GradSpace U)) =
          {v | ⟪w, v⟫ = 0} := by
        ext v; simp
      rw [e]
      exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have := hle hw
  simpa using this

theorem covVec_lin {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) (ρ₁ ρ₂ ρ₃ : TestFun H) (a : ℝ)
    (h : ∀ z, ρ₃.1 z = a * ρ₁.1 z + ρ₂.1 z) :
    covVec U ρ₃.1 = a • covVec U ρ₁.1 + covVec U ρ₂.1 := by
  have hmem : a • covVec U ρ₁.1 + covVec U ρ₂.1 - covVec U ρ₃.1 ∈ gradClosure U (zeroSpace U) :=
    sub_mem (add_mem (Submodule.smul_mem _ _ (covVec_mem _ _)) (covVec_mem _ _)) (covVec_mem _ _)
  refine (sub_eq_zero.1 ?_).symm
  by_cases hpos : ∃ g ∈ zeroSpace U, 0 < dirichletEnergyOn U g
  · refine eq_zero_of_inner_gradFeat hmem fun f hf => ?_
    have hi : ∀ σ : TestFun H, Integrable (fun z => σ.1 z * f z) (volume.restrict U) :=
      fun σ => ((σ.2.1.continuous.mul hf.1.continuous).integrable_of_hasCompactSupport
        (hf.2.1.mul_left (f := σ.1))).integrableOn
    rw [inner_sub_left, inner_add_left, real_inner_smul_left, inner_covVec_gradFeat hU hUH ρ₁ hpos hf,
      inner_covVec_gradFeat hU hUH ρ₂ hpos hf, inner_covVec_gradFeat hU hUH ρ₃ hpos hf,
      show (∫ z in U, ρ₃.1 z * f z) = ∫ z in U, (a * (ρ₁.1 z * f z) + ρ₂.1 z * f z) from
        integral_congr_ae (ae_of_all _ fun z => by simp only; rw [h z]; ring),
      integral_add ((hi ρ₁).const_mul a) (hi ρ₂), integral_const_mul]
    ring
  · exact eq_zero_of_mem_gradClosure_of_nopos (isDNSpace_zeroSpace U) hpos hmem

/-- The conditional covariance of `s(a⟨·,ρ₁⟩ + ⟨·,ρ₂⟩ − ⟨·,ρ₃⟩)` vanishes. -/
theorem quadForm_lin_eq_zero {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) (ρ₁ ρ₂ ρ₃ : TestFun H)
    (a s : ℝ) (h : ∀ z, ρ₃.1 z = a * ρ₁.1 z + ρ₂.1 z) :
    ∑ j, ∑ k, (![s * a, s, -s] : Fin 3 → ℝ) j * (![s * a, s, -s] : Fin 3 → ℝ) k *
      zeroGFFTestCov U (![ρ₁, ρ₂, ρ₃] j).1 (![ρ₁, ρ₂, ρ₃] k).1 = 0 := by
  simp only [zeroGFFTestCov_eq_inner hU hUH, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    covVec_lin hU hUH ρ₁ ρ₂ ρ₃ a h, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm (covVec U ρ₁.1) (covVec U ρ₂.1)]
  ring

/-- **Linearity of a conditional zero-boundary GFF.** -/
theorem linearPairingH_of_condGFF {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → Set ℂ} {Y : Ω → E}
    {X' : Ω → FieldSample} (hU : ∀ ω, IsOpen (U ω)) (hUH : ∀ ω, U ω ⊆ H)
    (hX' : IsCondZeroBoundaryGFFH U Y X' P) : CharFunFwd.LinearPairingH X' P := by
  intro ρ₁ ρ₂ ρ₃ a h
  set Z : Ω → ℝ := fun ω =>
    a * pairRaw (X' ω) ρ₁.1 + pairRaw (X' ω) ρ₂.1 - pairRaw (X' ω) ρ₃.1 with hZ
  have hm : ∀ ρ : TestFun H, Measurable fun ω => pairRaw (X' ω) ρ.1 := fun ρ =>
    measurable_pairRaw_comp hX'.measurable_coord ρ.1
  have hZm : Measurable Z := ((measurable_const.mul (hm ρ₁)).add (hm ρ₂)).sub (hm ρ₃)
  have hchar : charFun (P.map Z) = charFun (Measure.dirac (0 : ℝ)) := by
    funext s
    have hc := hX'.condCharFun 3 ![ρ₁, ρ₂, ρ₃] ![s * a, s, -s] (fun _ => 1) measurable_const
      ⟨1, fun _ => by simp⟩
    simp only [quadForm_lin_eq_zero (hU _) (hUH _) ρ₁ ρ₂ ρ₃ a s h, mul_zero, Real.exp_zero,
      Complex.ofReal_one, one_mul, integral_const, probReal_univ, one_smul] at hc
    rw [charFun_dirac, charFun_apply_real, integral_map hZm.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => cexp (s * x * I)) (P.map Z))]
    simp only [inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    rw [← hc]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hZ]
    congr 1
    push_cast
    ring
  have hmap : P.map Z = Measure.dirac 0 := Measure.ext_of_charFun hchar
  have hae : ∀ᵐ x ∂(P.map Z), x = 0 := by
    rw [hmap, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  filter_upwards [ae_of_ae_map hZm.aemeasurable hae] with ω hω
  simp only [hZ] at hω
  linarith

end Thm11Asm
end QuantumZipper
