/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafFreezeLap
import InteractingSLE.Spec.Coupling.Locality11Gauss

/-!
# Passing a weighted Dirichlet identity to the Markov projection

The approximation input is separated from its source. This lets the
localized Gaussian identity use the existing Markov approximation and
bounded-weight characteristic-function convergence tools.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace

namespace InteractingSLE.WFS

open LQGMetric LQGMetric.MarkovZB LocalSets WholeField QuantumZipper
open QuantumZipper.K3 QuantumZipper.Thm11Asm

/-- A weighted identity on Dirichlet tests passes to all Markov pairings. -/
theorem integral_exp_markov_eq_of_lapIdentity
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {U : Opens ℂ}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} {W : Ω → ℂ}
    (hU : U ≤ upperHalfPlaneOpens) (hhm : Measurable h) (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (hWm : Measurable W) (hWb : ∀ ω, ‖W ω‖ ≤ 1)
    (Ψ : TestOn upperHalfPlaneOpens) (J : ℂ)
    (hJ : ∀ f f' : zsSub (U : Set ℂ),
      ∫ ω, W ω * Complex.exp (Complex.I * (h ω (lapTest U f - lapTest U f' + Ψ) : ℂ)) ∂P =
        ((Real.exp (-(1 / 2) * (‖gradFeat U f.1 - gradFeat U f'.1‖ ^ 2 +
          2 * ⟪gradFeat U f.1 - gradFeat U f'.1, covVec U Ψ⟫)) : ℝ) : ℂ) * J)
    (Φ : TestOn upperHalfPlaneOpens) :
    ∫ ω, W ω * Complex.exp (Complex.I *
        ((G (h ω) Φ + markovCompl G (h ω) Ψ : ℝ) : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * (‖covVec U Φ - covVec U Ψ‖ ^ 2 +
        2 * ⟪covVec U Φ - covVec U Ψ, covVec U Ψ⟫)) : ℝ) : ℂ) * J := by
  obtain ⟨f, hf, hf2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd Φ
  obtain ⟨f', hf', hf2'⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hU hd Ψ
  let a : ℕ → Ω → ℝ := fun n ω => h ω (lapTest U (f n) - lapTest U (f' n) + Ψ)
  let b : Ω → ℝ := fun ω => G (h ω) Φ + markovCompl G (h ω) Ψ
  let L : ℕ → ℂ := fun n => ∫ ω, W ω * Complex.exp (Complex.I * (a n ω : ℂ)) ∂P
  have he : ∀ n ω, a n ω - b ω = (G (h ω) Ψ - h ω (lapTest U (f' n))) -
      (G (h ω) Φ - h ω (lapTest U (f n))) := by
    intro n ω
    simp only [a, b, markovCompl, map_add, map_sub, sub_apply]
    ring
  have hmem : ∀ n, MemLp (fun ω => a n ω - b ω) 2 P := fun n => by
    simp_rw [he]
    exact (memLp_markov_sub_lapTest hU hd Ψ (f' n)).sub (memLp_markov_sub_lapTest hU hd Φ (f n))
  have hsq : Tendsto (fun n => ∫ ω, (a n ω - b ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n =>
        2 * (∫ ω, (G (h ω) Ψ - h ω (lapTest U (f' n))) ^ 2 ∂P) +
          2 * (∫ ω, (G (h ω) Φ - h ω (lapTest U (f n))) ^ 2 ∂P)) atTop (𝓝 0) := by
      simpa using (hf2'.const_mul 2).add (hf2.const_mul 2)
    refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) (fun n => ?_) hlim
    have i1 := (memLp_markov_sub_lapTest hU hd Ψ (f' n)).integrable_sq
    have i2 := (memLp_markov_sub_lapTest hU hd Φ (f n)).integrable_sq
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
    refine integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
      ((i1.const_mul 2).add (i2.const_mul 2)) (Eventually.of_forall fun ω => ?_)
    change (a n ω - b ω) ^ 2 ≤ 2 * (G (h ω) Ψ - h ω (lapTest U (f' n))) ^ 2 +
      2 * (G (h ω) Φ - h ω (lapTest U (f n))) ^ 2
    rw [he]
    nlinarith only [sq_nonneg ((G (h ω) Ψ - h ω (lapTest U (f' n))) +
      (G (h ω) Φ - h ω (lapTest U (f n))))]
  have ham : ∀ n, Measurable (a n) := fun n => (measurable_distOn_apply _).comp hhm
  have hbm : Measurable b := ((measurable_distOn_apply Φ).comp (hG.comp hhm)).add
    ((measurable_distOn_apply Ψ).comp ((measurable_markovCompl hG).comp hhm))
  have hleft : Tendsto L atTop
      (𝓝 (∫ ω, W ω * Complex.exp (Complex.I * (b ω : ℂ)) ∂P)) := by
    simpa only [L, mul_comm] using Coupling.tendsto_integral_cexp_mul_of_tendsto_integral_sq
      hmem hsq hWb
      (fun n => ((GFF.measurable_exp_I_mul (ham n)).mul hWm).aestronglyMeasurable)
      (((GFF.measurable_exp_I_mul hbm).mul hWm).aestronglyMeasurable)
  have hright : Tendsto L atTop (𝓝 (((Real.exp (-(1 / 2) *
      (‖covVec U Φ - covVec U Ψ‖ ^ 2 +
        2 * ⟪covVec U Φ - covVec U Ψ, covVec U Ψ⟫)) : ℝ) : ℂ) * J)) := by
    have heq : L = fun n => ((Real.exp (-(1 / 2) *
        (‖gradFeat U (f n).1 - gradFeat U (f' n).1‖ ^ 2 +
          2 * ⟪gradFeat U (f n).1 - gradFeat U (f' n).1, covVec U Ψ⟫)) : ℝ) : ℂ) * J :=
      funext fun n => hJ (f n) (f' n)
    rw [heq]
    have hconv := hf.sub hf'
    refine Tendsto.mul_const J (Complex.continuous_ofReal.continuousAt.tendsto.comp ?_)
    refine Real.continuous_exp.continuousAt.tendsto.comp (Tendsto.const_mul _ ?_)
    exact ((continuous_norm.tendsto _).comp hconv).pow 2 |>.add
      (Tendsto.const_mul _ (hconv.inner tendsto_const_nhds))
  exact tendsto_nhds_unique hleft hright

/-- The localized retained kernel factors the Markov projection against the
weight and the complementary projection. -/
theorem integral_mul_exp_markov_of_kernel_on
    {Ω : Type*} {𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h M : Ω → DistOn upperHalfPlaneOpens}
    {U : Opens ℂ} {V : Ω → Set ℂ} {W : Ω → ℂ}
    (h𝒦 : 𝒦 ≤ mΩ) (hU : U ≤ upperHalfPlaneOpens)
    (hV : ∀ᵐ ω ∂P, W ω ≠ 0 → IsOpen (V ω) ∧ V ω ⊆ H ∧
      (U : Set ℂ) ⊆ V ω ∧ IsHarmonicDistOn (M ω) (V ω))
    (hker : ∀ χ : TestOn upperHalfPlaneOpens,
      P[fun ω => Complex.exp (Complex.I * (h ω χ : ℂ)) | 𝒦] =ᵐ[P]
        fun ω => rangeKerCF (M ω) (V ω) χ)
    (hhm : Measurable h) {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hG : Measurable G)
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P)
    (hWm : StronglyMeasurable[𝒦] W) (hWb : ∀ ω, ‖W ω‖ ≤ 1)
    (Φ Ψ : TestOn upperHalfPlaneOpens) :
    ∫ ω, W ω * (Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
        Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ))) ∂P =
      (∫ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) ∂P) *
        (∫ ω, W ω * Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) ∂P) := by
  obtain ⟨J, hJ⟩ := exists_const_integral_exp_lapTest_of_kernel_on h𝒦 hU hV hker hhm hWm hWb Ψ
  have hΦ := integral_exp_markov_eq_of_lapIdentity hU hhm hG hd (hWm.mono h𝒦).measurable hWb Ψ J hJ Φ
  have h0 := integral_exp_markov_eq_of_lapIdentity hU hhm hG hd (hWm.mono h𝒦).measurable hWb Ψ J hJ 0
  have hcov0 : covVec (U : Set ℂ) ⇑(0 : TestOn upperHalfPlaneOpens) = 0 := covVec_zero _ U.isOpen hU
  simp only [map_zero, zero_add, hcov0] at h0
  rw [norm_sub_sq_add_two_inner] at hΦ h0
  have he : ∀ ω, Complex.exp (Complex.I * (G (h ω) Φ : ℂ)) *
      Complex.exp (Complex.I * (markovCompl G (h ω) Ψ : ℂ)) =
      Complex.exp (Complex.I * ((G (h ω) Φ + markovCompl G (h ω) Ψ : ℝ) : ℂ)) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [hΦ, h0, integral_exp_markov hU hd Φ]
  rw [show -(1 / 2 : ℝ) * (‖covVec U Φ‖ ^ 2 - ‖covVec U Ψ‖ ^ 2) =
      -(1 / 2) * ‖covVec U Φ‖ ^ 2 +
        -(1 / 2) * (‖(0 : GradSpace U)‖ ^ 2 - ‖covVec U Ψ‖ ^ 2) by simp; ring, Real.exp_add]
  push_cast
  ring

end InteractingSLE.WFS
