import QuantumZipper.Proofs.Thm18.G3CvOut
import QuantumZipper.Proofs.GFF.K3.MixedM7AsmLip
import QuantumZipper.Proofs.GFF.K3.MixedM7B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1g: Lipschitz variance of the pulled-back harmonic part

For `z, w ∈ closedBall b r₂` (`r₂ < ρ`), the pushed-forward Poisson measures `Φ_*P_z, Φ_*P_w`
satisfy `kernelCov2 neumannH (Φ_*P_z, Φ_*P_w) (Φ_*P_z, Φ_*P_w) ≤ C ‖z − w‖`
(`kernelCov2_pullPoisson_le`): the Neumann part is the free bound
`kernelCov2_halfDiscPoisson_le`, and the correction `kPull` contributes
`∫ (hk z − hk w) d(P_z − P_w)`, bounded by the Lipschitz bound of Poisson integrals
(`abs_integral_halfDiscPoisson_sub_le`). With the Gaussian law of the increments this gives the
eighth-moment Kolmogorov bound `momentBound_pullIncr` for the harmonic part
`z ↦ W(Φ_*P_z) − W(Φ_*P_b)` of the pulled-back field (as `momentBound_harmIncr` for the free
field). Own adaptation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

theorem kPull_symm (Φ : ℂ → ℂ) (z w : ℂ) : kPull Φ z w = kPull Φ w z := by
  simp only [kPull, neumannH_symm (Φ z), neumannH_symm z]

theorem halfDiscPoisson_closedBall_compl {t r : ℝ} (hr : 0 < r) (z : ℂ) :
    halfDiscPoisson t r z (closedBall (t : ℂ) r)ᶜ = 0 := by
  have h := ae_iff.1 (ae_halfDiscPoisson_mem (t := t) hr z)
  refine measure_mono_null (fun x hx => ?_) h
  intro hx'
  exact hx (sphere_subset_closedBall hx'.1)

/-- **Lipschitz variance of the pulled-back Poisson increments.** -/
theorem kernelCov2_pullPoisson_le (hD : PullData Φ b r₀ ρ r₁ m M) {r₂ : ℝ} (hr₂ : 0 ≤ r₂)
    (hr₂ρ : r₂ < ρ) {z w : ℂ} (hz : ‖z - b‖ ≤ r₂) (hw : ‖w - b‖ ≤ r₂) :
    kernelCov2 neumannH ((halfDiscPoisson b ρ z).map Φ, (halfDiscPoisson b ρ w).map Φ)
      ((halfDiscPoisson b ρ z).map Φ, (halfDiscPoisson b ρ w).map Φ) ≤
      (2 * (lipρ ρ r₂ * Bv b ρ r₂) + poisLk ρ r₂ * (2 * (2 * (|Real.log m| + |Real.log M|)))) *
        ‖z - w‖ := by
  have hρ := hD.hρ
  have hzb := mem_ball_of_le_k3 hr₂ρ hz
  have hwb := mem_ball_of_le_k3 hr₂ρ hw
  have := isProbabilityMeasure_halfDiscPoisson hρ hzb
  have := isProbabilityMeasure_halfDiscPoisson hρ hwb
  set Pz := halfDiscPoisson b ρ z
  set Pw := halfDiscPoisson b ρ w
  have az := isAdmissibleH_halfDiscPoisson hρ hr₂ρ hz
  have aw := isAdmissibleH_halfDiscPoisson hρ hr₂ρ hw
  have cz := halfDiscPoisson_closedBall_compl (t := b) hρ z
  have cw := halfDiscPoisson_closedBall_compl (t := b) hρ w
  set K : ℝ := 2 * (|Real.log m| + |Real.log M|) with hK
  have hsub : closedBall (b : ℂ) ρ ⊆ ball (b : ℂ) r₀ := closedBall_subset_ball hD.hρr
  -- the continuous harmonic representatives
  have hret := continuous_retr_m7b b hρ
  have hretK : ∀ x, retr b ρ x ∈ closedBall (b : ℂ) ρ := fun x =>
    mem_closedBall_iff_norm.2 (norm_retr_sub_le hρ x)
  have hzB : z ∈ ball (b : ℂ) r₀ := hsub (ball_subset_closedBall hzb)
  have hwB : w ∈ ball (b : ℂ) r₀ := hsub (ball_subset_closedBall hwb)
  have hcont : ∀ a ∈ ball (b : ℂ) r₀, Continuous fun x => hk Φ a (retr b ρ x) := fun a ha =>
    ContinuousOn.comp_continuous (fun v hv => (harmonicAt_hk hD.conf ha hv).1.continuousAt
      |>.continuousWithinAt) hret fun x => hsub (hretK x)
  -- `kPull x a = hk a (retr x)` on the support of the Poisson measures
  have hon : ∀ a : ℂ, ‖a - (b : ℂ)‖ ≤ r₂ → ∀ x ∈ sphere (b : ℂ) ρ ∩ Hbar,
      kPull Φ x a = hk Φ a (retr b ρ x) := by
    intro a ha x hx
    have hxr : retr b ρ x = x := retr_eq_self hx.2 (le_of_eq (mem_sphere_iff_norm.1 hx.1))
    have haB : a ∈ ball (b : ℂ) r₀ := hsub (ball_subset_closedBall (mem_ball_of_le_k3 hr₂ρ ha))
    have hxa : x ≠ a := by
      rintro rfl; have := mem_sphere_iff_norm.1 hx.1; linarith
    have hxa' : x ≠ conj a := by
      rintro rfl
      have := mem_sphere_iff_norm.1 hx.1
      rw [norm_conj_sub_ofReal_k3] at this; linarith
    rw [hxr, kPull_symm, kPull_eq_hk hD.conf haB (hsub (sphere_subset_closedBall hx.1)) hxa hxa']
  -- `kernelCov kPull α P_a = ∫ hk a ∘ retr dα` for `α ∈ {P_z, P_w}`
  have hkc : ∀ (α : Measure ℂ), α (closedBall (b : ℂ) ρ)ᶜ = 0 →
      (∀ᵐ x ∂α, x ∈ sphere (b : ℂ) ρ ∩ Hbar) →
      ∀ a : ℂ, ‖a - (b : ℂ)‖ ≤ r₂ → kernelCov (kPull Φ) α (halfDiscPoisson b ρ a) =
        ∫ x, hk Φ a (retr b ρ x) ∂α := by
    intro α hαc hαS a ha
    unfold kernelCov
    refine integral_congr_ae ?_
    filter_upwards [hαS] with x hx
    have hab := mem_ball_of_le_k3 hr₂ρ ha
    have hxa : a ≠ x := by
      rintro rfl; have := mem_sphere_iff_norm.1 hx.1; linarith
    have hxa' : a ≠ conj x := by
      rintro rfl
      have := mem_sphere_iff_norm.1 hx.1
      rw [norm_conj_sub_ofReal_k3] at ha; linarith
    rw [integral_kPull_poisson hD.conf hρ hD.hρr (sphere_subset_closedBall hx.1) hab hxa hxa',
      hon a ha x hx]
  have sz := ae_halfDiscPoisson_mem (t := b) hρ z
  have sw := ae_halfDiscPoisson_mem (t := b) hρ w
  -- the correction part
  set h : ℂ → ℝ := fun x => hk Φ z (retr b ρ x) - hk Φ w (retr b ρ x) with hh
  have hhc : Continuous h := (hcont z hzB).sub (hcont w hwB)
  have hbd : ∀ a ∈ ball (b : ℂ) r₀, ∃ C, ∀ x, |hk Φ a (retr b ρ x)| ≤ C := by
    intro a ha
    obtain ⟨C, hC⟩ := (isCompact_closedBall (b : ℂ) ρ).exists_bound_of_continuousOn
      (fun v hv => (harmonicAt_hk hD.conf ha (hsub hv)).1.continuousAt.continuousWithinAt)
    exact ⟨C, fun x => hC _ (hretK x)⟩
  have hint : ∀ a ∈ ball (b : ℂ) r₀, ∀ (α : Measure ℂ) [IsFiniteMeasure α],
      Integrable (fun x => hk Φ a (retr b ρ x)) α := by
    intro a ha α _
    obtain ⟨C, hC⟩ := hbd a ha
    exact Integrable.of_bound (hcont a ha).aestronglyMeasurable C
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hM : ∀ x ∈ sphere (b : ℂ) ρ, |h (foldH x)| ≤ 2 * K := by
    intro x hx
    have hfx : foldH x ∈ sphere (b : ℂ) ρ ∩ Hbar :=
      ⟨K3.foldH_mem_sphere_k3 hx, CircleFubini.foldH_mem_Hbar' x⟩
    simp only [hh]
    rw [← hon z hz _ hfx, ← hon w hw _ hfx]
    have h1 := abs_kPull_le hD.conf hD.hρr hD.bl (sphere_subset_closedBall hfx.1)
      (closedBall_subset_closedBall hr₂ρ.le (mem_closedBall_iff_norm.2 hz))
    have h2 := abs_kPull_le hD.conf hD.hρr hD.bl (sphere_subset_closedBall hfx.1)
      (closedBall_subset_closedBall hr₂ρ.le (mem_closedBall_iff_norm.2 hw))
    calc _ ≤ |kPull Φ (foldH x) z| + |kPull Φ (foldH x) w| := abs_sub _ _
      _ ≤ K + K := add_le_add h1 h2
      _ = 2 * K := by ring
  have hlip := abs_integral_halfDiscPoisson_sub_le hr₂ hr₂ρ hhc hM hz hw
  have hNb := kernelCov2_halfDiscPoisson_le hρ hr₂ hr₂ρ hz hw
  -- assemble
  have hsplit : kernelCov2 neumannH (Pz.map Φ, Pw.map Φ) (Pz.map Φ, Pw.map Φ) =
      kernelCov2 neumannH (Pz, Pw) (Pz, Pw) +
        ((∫ x, h x ∂Pz) - ∫ x, h x ∂Pw) := by
    simp only [kernelCov2]
    rw [kernelCov_map_g3cv hD.conf, kernelCov_map_g3cv hD.conf, kernelCov_map_g3cv hD.conf,
      kernelCov_map_g3cv hD.conf,
      kernelCov_pull_split hD.conf hD.hρr hD.bl az az cz cz,
      kernelCov_pull_split hD.conf hD.hρr hD.bl az aw cz cw,
      kernelCov_pull_split hD.conf hD.hρr hD.bl aw az cw cz,
      kernelCov_pull_split hD.conf hD.hρr hD.bl aw aw cw cw,
      hkc Pz cz sz z hz, hkc Pz cz sz w hw, hkc Pw cw sw z hz, hkc Pw cw sw w hw]
    simp only [hh]
    rw [integral_sub (hint z hzB Pz) (hint w hwB Pz), integral_sub (hint z hzB Pw) (hint w hwB Pw)]
    ring
  rw [hsplit]
  have hlip' := (abs_le.1 hlip).2
  have hK0 : 0 ≤ K := by positivity
  nlinarith [norm_nonneg (z - w)]

/-- The increments `z ↦ W(Φ_*P_{retr z}) − W(Φ_*P_b)` of the harmonic part of the pulled-back
field. -/
def pullIncr {Ω : Type*} (W : Ω → FieldSample) (Φ : ℂ → ℂ) (b ρ r₂ : ℝ) : ℂ → Ω → ℝ :=
  fun z ω => W ω ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ) -
    W ω ((halfDiscPoisson b ρ (b : ℂ)).map Φ)

/-- The constant of the Lipschitz variance bound. -/
def pullLipC (ρ r₂ m M b : ℝ) : ℝ :=
  2 * (lipρ ρ r₂ * Bv b ρ r₂) + poisLk ρ r₂ * (2 * (2 * (|Real.log m| + |Real.log M|)))

theorem pullLipC_nonneg {ρ r₂ m M b : ℝ} (hr₂ : 0 ≤ r₂) (hr₂ρ : r₂ < ρ) :
    0 ≤ pullLipC ρ r₂ m M b := by
  unfold pullLipC
  have h1 : 0 ≤ lipρ ρ r₂ * Bv b ρ r₂ := mul_nonneg (lipρ_nonneg hr₂ hr₂ρ) ENNReal.toReal_nonneg
  have h2 := poisLk_nonneg hr₂ hr₂ρ
  positivity

/-- **Eighth-moment Kolmogorov bound** for the pulled-back harmonic increments. -/
theorem momentBound_pullIncr {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : Ω → FieldSample} (hW : IsFreeGFFModConstH W P) (hD : PullData Φ b r₀ ρ r₁ m M)
    {r₂ : ℝ} (hr₂ : 0 < r₂) (hr₂ρ : r₂ < ρ) :
    CircleCont.MomentBound (pullIncr W Φ b ρ r₂) P
      ((4 * pullLipC ρ r₂ m M b) ^ 4 * gaussianAbsMoment 8) := by
  intro z _ w _
  have hz := norm_retr_sub_le (t := b) hr₂ z
  have hw := norm_retr_sub_le (t := b) hr₂ w
  have hρ := hD.hρ
  have := isProbabilityMeasure_halfDiscPoisson hρ (mem_ball_of_le_k3 hr₂ρ hz)
  have := isProbabilityMeasure_halfDiscPoisson hρ (mem_ball_of_le_k3 hr₂ρ hw)
  have az := hD.adm_map (isAdmissibleH_halfDiscPoisson hρ hr₂ρ hz)
    (halfDiscPoisson_closedBall_compl hρ _)
  have aw := hD.adm_map (isAdmissibleH_halfDiscPoisson hρ hr₂ρ hw)
    (halfDiscPoisson_closedBall_compl hρ _)
  have hmass : ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ) Set.univ =
      ((halfDiscPoisson b ρ (retr b r₂ w)).map Φ) Set.univ := by
    rw [Measure.map_apply hD.conf.meas MeasurableSet.univ,
      Measure.map_apply hD.conf.meas MeasurableSet.univ, preimage_univ, measure_univ,
      measure_univ]
  have e : ∀ ω, pullIncr W Φ b ρ r₂ z ω - pullIncr W Φ b ρ r₂ w ω =
      W ω ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ) -
        W ω ((halfDiscPoisson b ρ (retr b r₂ w)).map Φ) :=
    fun ω => by simp only [pullIncr]; ring
  simp only [e]
  rw [CircleCont.lintegral_pow8_of_map_eq (U := fun ω =>
      W ω ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ) -
        W ω ((halfDiscPoisson b ρ (retr b r₂ w)).map Φ))
    ((hW.measurable_coord _).sub (hW.measurable_coord _))
    (map_diff_eq_gaussianReal_k3 hW az aw hmass)]
  apply ENNReal.ofReal_le_ofReal
  have hL := pullLipC_nonneg (ρ := ρ) (m := m) (M := M) (b := b) hr₂.le hr₂ρ
  have hkb := kernelCov2_pullPoisson_le hD hr₂.le hr₂ρ hz hw
  have hlip := norm_retr_sub_retr_le (t := b) hr₂ z w
  have hkb' : kernelCov2 neumannH ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ,
      (halfDiscPoisson b ρ (retr b r₂ w)).map Φ) ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ,
      (halfDiscPoisson b ρ (retr b r₂ w)).map Φ) ≤ 4 * pullLipC ρ r₂ m M b * ‖z - w‖ := by
    have : kernelCov2 neumannH ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ,
      (halfDiscPoisson b ρ (retr b r₂ w)).map Φ) ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ,
      (halfDiscPoisson b ρ (retr b r₂ w)).map Φ) ≤
        pullLipC ρ r₂ m M b * ‖retr b r₂ z - retr b r₂ w‖ := hkb
    nlinarith [mul_le_mul_of_nonneg_left hlip hL, norm_nonneg (z - w)]
  have hnn : 0 ≤ 4 * pullLipC ρ r₂ m M b * ‖z - w‖ :=
    mul_nonneg (mul_nonneg (by norm_num) hL) (norm_nonneg _)
  have hv : ((kernelCov2 neumannH ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ,
      (halfDiscPoisson b ρ (retr b r₂ w)).map Φ) ((halfDiscPoisson b ρ (retr b r₂ z)).map Φ,
      (halfDiscPoisson b ρ (retr b r₂ w)).map Φ)).toNNReal : ℝ) ≤
        4 * pullLipC ρ r₂ m M b * ‖z - w‖ := by
    rw [Real.coe_toNNReal']; exact max_le hkb' hnn
  have h4 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 4
  calc _ ≤ (4 * pullLipC ρ r₂ m M b * ‖z - w‖) ^ 4 * gaussianAbsMoment 8 :=
        mul_le_mul_of_nonneg_right h4 (gaussianAbsMoment_nonneg 8)
    _ = (4 * pullLipC ρ r₂ m M b) ^ 4 * gaussianAbsMoment 8 * ‖z - w‖ ^ 4 := by ring

end G3Cv
end QuantumZipper
