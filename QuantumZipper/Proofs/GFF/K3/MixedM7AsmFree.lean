import QuantumZipper.Proofs.GFF.K3.MixedM7AsmPois

/-!
# K3-mixed M7-b, part 2: the free-field half of the harmonic correction

`exists_freeHarmonicPart`: for a free field `X` and a half-disc `ball t r ∩ H`, `0 < r' < r`,
there is `h : Ω → ℂ → ℝ` such that

* `h ω ∘ foldH` is harmonic on a neighbourhood of `closedBall t r'` for **every** `ω`;
* `h · z` is measurable for the outside σ-algebra `outsideSigma X t r` (node L2);
* for every admissible `μ` carried by `closedBall t r'`, almost surely
  `X μ = Z μ + ∫ h dμ + μ(ℂ) · X(P_t)` (`Z = markovZ X t r`, the local part).

This is the free-field Markov decomposition `markov_decomposition` (Sheffield, *Gaussian free
fields for mathematicians*, PTRF 139 (2007), Thm 2.17, in its half-disc/Neumann form, node L2)
with the continuous, almost surely harmonic version `harmH` replaced by its Poisson smoothing
`poisSm` (`MixedM7AsmPois.lean`), which is harmonic for every sample and has the same
measurability. It is the free half of the correction `g` of M7
(`MixedFreeCouplingHalfDiscStmt`). Own elementary assembly.
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped Real Topology ComplexConjugate ENNReal NNReal

namespace QuantumZipper.K3

/-- **The free harmonic part, harmonic for every sample.** -/
theorem exists_freeHarmonicPart {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {t r r' : ℝ}
    (hr' : 0 < r') (hr'r : r' < r) :
    ∃ h : Ω → ℂ → ℝ,
      (∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => h ω (foldH z)) (closedBall (t : ℂ) r')) ∧
      (∀ z, Measurable[outsideSigma X t r] fun ω => h ω z) ∧
      ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
        ∀ᵐ ω ∂P, X ω μ = markovZ X t r ω μ + ∫ z, h ω z ∂μ +
          (μ Set.univ).toReal * X ω (halfDiscPoisson t r (t : ℂ)) := by
  set δ : ℝ := (r - r') / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ρ₁ : ℝ := r' + δ with hρ₁
  set s : ℝ := r' + 2 * δ with hs
  set r₂ : ℝ := r' + 3 * δ with hr₂
  have hr : 0 < r := hr'.trans hr'r
  have hρ₁0 : 0 < ρ₁ := by linarith
  have hρ₁s : ρ₁ < s := by linarith
  have hsr₂ : s < r₂ := by linarith
  have hr₂0 : 0 < r₂ := by linarith
  have hr₂r : r₂ < r := by rw [hr₂, hδ]; linarith
  have hr'ρ₁ : r' < ρ₁ := by linarith
  have hc : ∀ ω, Continuous (harmH X t r r₂ ω) := fun ω =>
    continuous_harmH (P := P) hX hr hr₂0 hr₂r ω
  refine ⟨fun ω => poisSm t s ρ₁ (harmH X t r r₂ ω), fun ω => ?_, fun z => ?_,
    fun μ hμ hμr => ?_⟩
  · exact harmonicOnNhd_poisSm_foldH (hc ω) hρ₁0 hρ₁s hr'ρ₁
  · exact measurable_poisSm (outsideSigma X t r) hc
      (fun w => measurable_harmH_outside hr hr₂0 hr₂r w) t s ρ₁ z
  · have hμr₂ : μ (closedBall (t : ℂ) r₂)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.2 (closedBall_subset_closedBall (by linarith))) hμr
    filter_upwards [markov_decomposition hX hr hr₂0 hr₂r hμ hμr₂,
      ae_harmonicOnNhd_harmH hX hr hr₂0 hr₂r] with ω h1 h2
    have hae : (fun z => poisSm t s ρ₁ (harmH X t r r₂ ω) z) =ᵐ[μ] harmH X t r r₂ ω := by
      filter_upwards [ae_mem_Hbar_of_admissible hμ, (mem_ae_iff.2 hμr :
        closedBall (t : ℂ) r' ∈ ae μ)] with z hzH hzB
      exact poisSm_eq_of_harmonic hρ₁s
        (fun x hx => h2 x (closedBall_subset_ball hsr₂ hx))
        (fun x _ => harmH_conj (X := X) t r r₂ ω x) hzH
        ((mem_closedBall_iff_norm.1 hzB).trans hr'ρ₁.le)
    rw [integral_congr_ae hae]
    exact h1

end QuantumZipper.K3
