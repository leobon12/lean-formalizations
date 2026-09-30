import QuantumZipper.Proofs.GFF.K3.MixedM7B4

/-!
# K3-mixed M7-b, part 1: Poisson smoothing gives everywhere-harmonic versions

For a continuous `h : ℂ → ℝ` and radii `0 < ρ₁ < s`, the **Poisson smoothing**

  `poisSm t s ρ₁ h z = ∫ h dP^s_{retr z}`   (`P^s_y = halfDiscPoisson t s y`)

is continuous on `ℂ`, even (`poisSm ∘ foldH = poisSm`), and harmonic on `ball t ρ₁`
(`harmonicOnNhd_poisSm`), for **every** `h`: no probability is involved. If `h` is itself harmonic
on a neighbourhood of `closedBall t s` and even on the circle, `poisSm` reproduces `h` on
`closedBall t ρ₁ ∩ Hbar` (`poisSm_eq_of_harmonic`). If `h = G ω` depends on a parameter `ω`
continuously in `z` and `m`-measurably in `ω`, then `ω ↦ poisSm t s ρ₁ (G ω) z` is
`m`-measurable (`measurable_poisSm`).

This turns a continuous version that is only *almost surely* harmonic into a version that is
harmonic for every `ω`, without enlarging the σ-algebra: this is how the harmonic correction of
M7 (`MixedFreeCouplingHalfDiscStmt`) is made harmonic for every sample.

Sources: the half-disc Poisson formula (`integral_halfDiscPoisson_of_harmonic`; Axler–Bourdon–
Ramey, *Harmonic Function Theory*, 2nd ed., Thm 1.17), the circle-average identity
`∫ P_w dσ_{z,ρ}(w) = P_z` (`bind_circleUnif_halfDiscPoisson`), and Weyl's lemma in mean-value
form (`harmonicOnNhd_of_meanValue`). The assembly (Poisson integral of a continuous version, in
place of Werner–Powell, arXiv:2004.04720, Prop. 4.3's harmonic version) is an own elementary
argument.
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped Real Topology ComplexConjugate ENNReal NNReal

namespace QuantumZipper.K3

/-- **Poisson smoothing** of `h` on the half-disc of radius `s`, evaluated at the retraction
of `z` onto `closedBall t ρ₁ ∩ Hbar`. -/
def poisSm (t s ρ₁ : ℝ) (h : ℂ → ℝ) (z : ℂ) : ℝ :=
  ∫ x, h x ∂halfDiscPoisson t s (retr t ρ₁ z)

/-- The polar integrand of the Poisson integral, jointly in the point and the angle. -/
def poisSmPolar (t s δ : ℝ) (h : ℂ → ℝ) (y : ℂ) (θ : ℝ) : ℝ :=
  (s ^ 2 - ‖y - t‖ ^ 2) / max (‖circleMap (t : ℂ) s θ - y‖ ^ 2) (δ ^ 2) *
    h (foldH (circleMap (t : ℂ) s θ))

theorem continuous_poisSmPolar_m7as {h : ℂ → ℝ} (hh : Continuous h) (t s : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : Continuous (Function.uncurry (poisSmPolar t s δ h)) := by
  have hcm : Continuous fun q : ℂ × ℝ => circleMap (t : ℂ) s q.2 := by
    unfold circleMap; fun_prop
  unfold poisSmPolar
  refine (((continuous_const.sub (((continuous_fst.sub continuous_const).norm).pow 2)).div
    (((hcm.sub continuous_fst).norm.pow 2).max continuous_const) fun q => ?_).mul
      (hh.comp (continuous_foldH_K3.comp hcm)))
  exact (lt_of_lt_of_le (by positivity) (le_max_right _ _)).ne'

theorem poisSm_eq_polar_m7as {h : ℂ → ℝ} (hh : Continuous h) {t s ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ₁s : ρ₁ < s) (z : ℂ) :
    poisSm t s ρ₁ h z =
      (2 * π)⁻¹ * ∫ θ in Icc (-π) π, poisSmPolar t s (s - ρ₁) h (retr t ρ₁ z) θ := by
  rw [poisSm, integral_halfDiscPoisson_eq_polar_m7b hh (norm_retr_sub_le hρ₁ z) hρ₁s le_rfl]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
  simp only [poissonPolar, poisSmPolar, max_self]

/-- `poisSm` is continuous on `ℂ`. -/
theorem continuous_poisSm {h : ℂ → ℝ} (hh : Continuous h) {t s ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ₁s : ρ₁ < s) : Continuous (poisSm t s ρ₁ h) := by
  have e : poisSm t s ρ₁ h = fun z =>
      (2 * π)⁻¹ * ∫ θ in Icc (-π) π, poisSmPolar t s (s - ρ₁) h (retr t ρ₁ z) θ :=
    funext (poisSm_eq_polar_m7as hh hρ₁ hρ₁s)
  rw [e]
  refine continuous_const.mul ?_
  have hc : Continuous (Function.uncurry fun (y : ℂ) (θ : ℝ) =>
      poisSmPolar t s (s - ρ₁) h (retr t ρ₁ y) θ) :=
    ((continuous_poisSmPolar_m7as hh t s (sub_pos.2 hρ₁s)).comp
      ((continuous_retr_m7b t hρ₁).prodMap continuous_id)).congr fun p => rfl
  exact continuous_parametric_integral_of_continuous (μ := volume) hc isCompact_Icc

theorem poisSm_foldH (t s ρ₁ : ℝ) (h : ℂ → ℝ) (z : ℂ) :
    poisSm t s ρ₁ h (foldH z) = poisSm t s ρ₁ h z := by
  simp only [poisSm, retr_foldH_m7b]

theorem poisSm_conj (t s ρ₁ : ℝ) (h : ℂ → ℝ) (z : ℂ) :
    poisSm t s ρ₁ h (conj z) = poisSm t s ρ₁ h z := by
  simp only [poisSm, retr_conj_m7b]

/-- Fubini for the half-disc Poisson kernel. -/
theorem integral_bind_halfDiscPoisson_m7as {t s : ℝ} (ν : Measure ℂ) [IsFiniteMeasure ν]
    {f : ℂ → ℝ} (hf : Integrable f (ν.bind (halfDiscPoisson t s))) :
    ∫ x, f x ∂(ν.bind (halfDiscPoisson t s)) = ∫ w, ∫ x, f x ∂halfDiscPoisson t s w ∂ν := by
  have e : halfDiscPoisson t s = fun z => halfDiscPoissonKernel t s z :=
    funext fun z => (halfDiscPoissonKernel_apply t s z).symm
  rw [e] at hf ⊢
  change Integrable f (halfDiscPoissonKernel t s ∘ₘ ν) at hf
  change ∫ x, f x ∂(halfDiscPoissonKernel t s ∘ₘ ν) = _
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [ProbabilityTheory.Kernel.integral_comp hf]
  simp

/-- The mean-value property of `poisSm` over folded circles centred in `Hbar`. -/
theorem integral_foldedCircle_poisSm {h : ℂ → ℝ} (hh : Continuous h) {t s ρ₁ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) {z : ℂ} (hz : z ∈ Hbar) {σ : ℝ} (hσ : 0 < σ)
    (hzσ : ‖z - t‖ + σ < ρ₁) :
    ∫ x, poisSm t s ρ₁ h x ∂foldedCircle z σ = poisSm t s ρ₁ h z := by
  have hs : 0 < s := hρ₁.trans hρ₁s
  have hK : foldedCircle z σ (closedBall (t : ℂ) ρ₁ ∩ Hbar)ᶜ = 0 := by
    refine measure_mono_null (compl_subset_compl.2 fun x hx => ⟨?_, hx.2⟩)
      (foldedCircle_compl_eq_zero hz hσ.le)
    have hx1 := mem_closedBall_iff_norm.1 hx.1
    rw [mem_closedBall_iff_norm]
    calc ‖x - t‖ = ‖(x - z) + (z - t)‖ := by ring_nf
      _ ≤ ‖x - z‖ + ‖z - t‖ := norm_add_le _ _
      _ ≤ ρ₁ := by linarith
  have hae : (fun x => poisSm t s ρ₁ h x) =ᵐ[foldedCircle z σ]
      fun x => ∫ y, h y ∂halfDiscPoisson t s x := by
    filter_upwards [mem_ae_iff.2 hK] with x hx
    rw [poisSm, retr_eq_self hx.2 (mem_closedBall_iff_norm.1 hx.1)]
  have hbind := bind_foldedCircle_halfDiscPoisson hs hσ (by linarith : ‖z - t‖ + σ < s)
  have hzb : z ∈ ball (t : ℂ) s := mem_ball_iff_norm.2 (by linarith)
  have := isProbabilityMeasure_halfDiscPoisson hs hzb
  have hint : Integrable h ((foldedCircle z σ).bind (halfDiscPoisson t s)) := by
    rw [hbind]
    have hKc : IsCompact (sphere (t : ℂ) s ∩ Hbar) := (isCompact_sphere _ _).inter_right
      isClosed_Hbar
    have hIK : IntegrableOn h (sphere (t : ℂ) s ∩ Hbar) (halfDiscPoisson t s z) :=
      hh.continuousOn.integrableOn_compact hKc
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_halfDiscPoisson_mem hs z)] at hIK
  rw [integral_congr_ae hae, ← integral_bind_halfDiscPoisson_m7as _ hint, hbind, poisSm,
    retr_eq_self hz (by linarith)]

/-- **Weyl step.** `poisSm t s ρ₁ h` is harmonic on `ball t ρ₁`. -/
theorem harmonicOnNhd_poisSm {h : ℂ → ℝ} (hh : Continuous h) {t s ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ₁s : ρ₁ < s) : InnerProductSpace.HarmonicOnNhd (poisSm t s ρ₁ h) (ball (t : ℂ) ρ₁) := by
  have hcont := continuous_poisSm hh (t := t) hρ₁ hρ₁s
  refine harmonicOnNhd_of_meanValue hcont isOpen_ball fun z _ σ hσ hball => ?_
  have hzσ := add_lt_of_closedBall_subset_ball hσ hball
  have hfold : ∫ x, poisSm t s ρ₁ h x ∂circleUnif z σ =
      ∫ x, poisSm t s ρ₁ h x ∂foldedCircle z σ := by
    rw [foldedCircle, integral_map measurable_foldH.aemeasurable hcont.aestronglyMeasurable]
    simp only [poisSm_foldH]
  rw [hfold]
  by_cases hz : z ∈ Hbar
  · exact integral_foldedCircle_poisSm hh hρ₁ hρ₁s hz hσ hzσ
  · have hz' : conj z ∈ Hbar := by
      have : z.im < 0 := lt_of_not_ge hz
      show 0 ≤ (conj z).im
      simp only [Complex.conj_im]; linarith
    rw [← CoordReg.integral_foldedCircle_conj hcont.measurable,
      integral_foldedCircle_poisSm hh hρ₁ hρ₁s hz' hσ
        (by rw [norm_conj_sub_ofReal_k3]; exact hzσ), poisSm_conj]

/-- The even extension `poisSm ∘ foldH` is harmonic on a neighbourhood of `closedBall t r'`
for `r' < ρ₁`. -/
theorem harmonicOnNhd_poisSm_foldH {h : ℂ → ℝ} (hh : Continuous h) {t s ρ₁ r' : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁s : ρ₁ < s) (hr' : r' < ρ₁) :
    InnerProductSpace.HarmonicOnNhd (fun z => poisSm t s ρ₁ h (foldH z))
      (closedBall (t : ℂ) r') := by
  simp only [poisSm_foldH]
  exact fun z hz => harmonicOnNhd_poisSm hh hρ₁ hρ₁s z (closedBall_subset_ball hr' hz)

/-- **Reproduction.** If `h` is harmonic on a neighbourhood of `closedBall t s` and even on the
circle, then `poisSm t s ρ₁ h = h` on `closedBall t ρ₁ ∩ Hbar`. -/
theorem poisSm_eq_of_harmonic {h : ℂ → ℝ} {t s ρ₁ : ℝ} (hρ₁s : ρ₁ < s)
    (hh : InnerProductSpace.HarmonicOnNhd h (closedBall (t : ℂ) s))
    (heven : ∀ x ∈ sphere (t : ℂ) s, h (conj x) = h x) {z : ℂ} (hz : z ∈ Hbar)
    (hzt : ‖z - t‖ ≤ ρ₁) : poisSm t s ρ₁ h z = h z := by
  have hs : 0 < s := lt_of_le_of_lt ((norm_nonneg _).trans hzt) hρ₁s
  rw [poisSm, retr_eq_self hz hzt]
  exact integral_halfDiscPoisson_of_harmonic hs (mem_ball_iff_norm.2 (by linarith)) hh heven

/-- **Measurability in the parameter.** If `G ω` is continuous for every `ω` and every
`ω ↦ G ω w` is `m`-measurable, so is `ω ↦ poisSm t s ρ₁ (G ω) z`. -/
theorem measurable_poisSm {Ω : Type*} (m : MeasurableSpace Ω) {G : Ω → ℂ → ℝ}
    (hGc : ∀ ω, Continuous (G ω)) (hGm : ∀ w, Measurable[m] fun ω => G ω w) (t s ρ₁ : ℝ)
    (z : ℂ) : Measurable[m] fun ω => poisSm t s ρ₁ (G ω) z := by
  have hu : Measurable (Function.uncurry fun (w : ℂ) (ω : Ω) => G ω w) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hGc ω) hGm
  have : SFinite (halfDiscPoisson t s (retr t ρ₁ z)) := by
    unfold halfDiscPoisson; infer_instance
  have hs := StronglyMeasurable.integral_prod_left (μ := halfDiscPoisson t s (retr t ρ₁ z))
    hu.stronglyMeasurable
  exact hs.measurable

end QuantumZipper.K3
