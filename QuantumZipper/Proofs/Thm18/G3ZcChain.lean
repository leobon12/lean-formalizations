import QuantumZipper.Proofs.Thm18.G3ZcJoint
import QuantumZipper.Proofs.Thm18.G3Cv2Setup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C (c), step 3: the one-point G0 chain for a *given* coupled field

`exists_pullSetup` (G3CvSetup), `exists_g0Model` (G3Cv2Model) and `exists_g0Setup` (G3Cv2Setup)
each start from an existential coupling. For the two-point zoom the same field `W` must be coupled
at two points (`exists_twoCouplings`, G3ZcJoint), so the three steps are restated here for given
coupling data (same proofs, with the existential replaced by hypotheses):

* `pullSetup_of`: the harmonic smoothing of the coupling's harmonic part (Poisson integral);
* `g0Model_of`: the circle-data identity for the zoom through `ψ` (the log-derivative term);
* `g0Setup_of`: the D3⁺ `Setup` with the gauge fixed on a reference circle, and the a.s. agreement
  near `0` of the normalized zoom with the D3⁺ model.

Sources as in the original files (Sheffield, *GFF for mathematicians* (2007) §2.2, Thm. 2.17;
Sheffield arXiv:1012.4797 pp. 70–71). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm D3Plus

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- `exists_pullSetup` for given coupling data. -/
theorem pullSetup_of (hD : PullData Φ b r₀ ρ r₁ m M) (hr₁0 : 0 < r₁) {r' : ℝ}
    (hr' : 0 < r') (hr'r : r' < r₁) {E' : Type} [MeasurableSpace E']
    {W X' : (ℕ → ℝ) → FieldSample} {Ξ : (ℕ → ℝ) → E'} {g : (ℕ → ℝ) → ℂ → ℝ}
    (hgc : ∀ ω, ContinuousOn (g ω) Hbar)
    (hgh : ∀ᵐ ω ∂stdP, InnerProductSpace.HarmonicOnNhd (fun z => g ω (foldH z)) (ball (b : ℂ) r₁))
    (hgm : ∀ z ∈ Hbar, Measurable[MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X' b ρ]
      fun ω => g ω z)
    (hid : ∀ μ μ' : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH μ' → μ Set.univ = μ' Set.univ →
      μ (closedBall (b : ℂ) r₁)ᶜ = 0 → μ' (closedBall (b : ℂ) r₁)ᶜ = 0 →
      ∀ᵐ ω ∂stdP, W ω (μ.map Φ) - W ω (μ'.map Φ) =
        X' ω μ - X' ω μ' + ((∫ z, g ω z ∂μ) - ∫ z, g ω z ∂μ')) :
    ∃ g' : (ℕ → ℝ) → ℂ → ℝ,
      (∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => g' ω (foldH z)) (closedBall (b : ℂ) r')) ∧
      (∀ z, Measurable[MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X' b ρ]
        fun ω => g' ω z) ∧
      ∀ μ μ' : Measure ℂ, IsAdmissibleH μ → IsAdmissibleH μ' → μ Set.univ = μ' Set.univ →
        μ (closedBall (b : ℂ) r')ᶜ = 0 → μ' (closedBall (b : ℂ) r')ᶜ = 0 →
        ∀ᵐ ω ∂stdP, W ω (μ.map Φ) - W ω (μ'.map Φ) =
          X' ω μ - X' ω μ' + ((∫ z, g' ω z ∂μ) - ∫ z, g' ω z ∂μ') := by
  set δ : ℝ := (r₁ - r') / 3 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set ρ₁ : ℝ := r' + δ with hρ₁
  set s : ℝ := r' + 2 * δ with hs
  have hρ₁0 : 0 < ρ₁ := by linarith
  have hρ₁s : ρ₁ < s := by linarith
  have hr'ρ₁ : r' < ρ₁ := by linarith
  have hsr₁ : s < r₁ := by rw [hs, hδ]; linarith
  set G : (ℕ → ℝ) → ℂ → ℝ := fun ω w => g ω (foldH w) with hG
  have hGc : ∀ ω, Continuous (G ω) := fun ω =>
    (hgc ω).comp_continuous CircleFubini.continuous_foldH' CircleFubini.foldH_mem_Hbar'
  have hGm : ∀ w, Measurable[MeasurableSpace.comap Ξ inferInstance ⊔ outsideSigma X' b ρ]
      fun ω => G ω w := fun w => hgm (foldH w) (CircleFubini.foldH_mem_Hbar' w)
  refine ⟨fun ω => poisSm b s ρ₁ (G ω),
    fun ω => harmonicOnNhd_poisSm_foldH (hGc ω) hρ₁0 hρ₁s hr'ρ₁,
    fun z => measurable_poisSm _ hGc hGm b s ρ₁ z, ?_⟩
  intro μ μ' hμA hμ'A hm hμc hμ'c
  have hsub : (closedBall (b : ℂ) r₁)ᶜ ⊆ (closedBall (b : ℂ) r')ᶜ :=
    compl_subset_compl.2 (closedBall_subset_closedBall hr'r.le)
  have hK : ∀ α : Measure ℂ, IsAdmissibleH α → α (closedBall (b : ℂ) r')ᶜ = 0 →
      ∀ᵐ z ∂α, z ∈ closedBall (b : ℂ) r' ∩ Hbar := fun α hα hαc => by
    filter_upwards [ae_mem_Hbar_of_admissible hα, ae_mem_of_compl_null_g3cv hαc] with z h1 h2
    exact ⟨h2, h1⟩
  filter_upwards [hid μ μ' hμA hμ'A hm (measure_mono_null hsub hμc)
    (measure_mono_null hsub hμ'c), hgh] with ω h1 h2
  have hGh : InnerProductSpace.HarmonicOnNhd (G ω) (closedBall (b : ℂ) s) := fun z hz =>
    h2 z (closedBall_subset_ball hsr₁ hz)
  have heq : ∀ α : Measure ℂ, IsAdmissibleH α → α (closedBall (b : ℂ) r')ᶜ = 0 →
      ∫ z, poisSm b s ρ₁ (G ω) z ∂α = ∫ z, g ω z ∂α := fun α hα hαc =>
    integral_congr_ae ((hK α hα hαc).mono fun z hz => by
      rw [poisSm_eq_of_harmonic hρ₁s hGh (fun x _ => by simp only [hG, foldH_conj_k3]) hz.2
        ((mem_closedBall_iff_norm.1 hz.1).trans hr'ρ₁.le)]
      simp only [hG, CircleFubini.foldH_of_mem' hz.2])
  rw [heq μ hμA hμc, heq μ' hμ'A hμ'c]
  exact h1

end G3Cv
end QuantumZipper
