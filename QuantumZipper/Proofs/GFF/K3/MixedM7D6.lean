import QuantumZipper.Proofs.GFF.K3.MixedM7D5
import QuantumZipper.Proofs.GFF.K3.KernelForm
import QuantumZipper.Proofs.Complex.BasicsCayley

/-!
# K3-mixed M7-a3, half-disc covariance, step D6: the disc through the Cayley map

The map `discMap t r z = cayleyInv ((z − t)/r)`, `cayleyInv w = i(1 + w)/(1 − w)`, is a conformal
map of the disc `ball t r` onto `ℍ` (`isConformalOnto_discMap_m7d`), and the symmetrized local
measures push forward to admissible measures on `ℍ` (`isAdmissibleH_map_sym_m7d`). Hence, by the
conformal kernel form of the dual norm (node C2, `dualCov_conformal_eq_kernel`; Sheffield,
*Gaussian free fields for mathematicians* (2007), §2.2),

  `dualCov B (zeroSpace B) μ̃ ν̃ = ∫_B ∫_B G_ℍ(φ x, φ y) dν̃ dμ̃`,

and the disc-kernel node `HalfDiscDiscKernelStmt` reduces to the explicit integral identity
`HalfDiscGreenIdStmt` (`halfDiscDiscKernel_of_greenId`).
-/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Real Topology ComplexConjugate ENNReal

namespace QuantumZipper.K3

/-- The Cayley map of the disc `ball t r` onto `ℍ`. -/
def discMap (t r : ℝ) (z : ℂ) : ℂ := CA.cayleyInv ((z - t) / r)

theorem ne_one_of_norm_lt_m7d {w : ℂ} (hw : ‖w‖ < 1) : w ≠ 1 := by
  rintro rfl; simp at hw

theorem bijOn_cayleyInv_ball_m7d : BijOn CA.cayleyInv (ball (0 : ℂ) 1) H :=
  CA.bijOn_cayley_H.symm ⟨fun w hw => CA.cayley_cayleyInv
      (ne_one_of_norm_lt_m7d (mem_ball_zero_iff.1 hw)),
    fun z hz => CA.cayleyInv_cayley (CA.add_I_ne_zero_of_im_nonneg (le_of_lt hz))⟩

theorem norm_aff_m7d {t r : ℝ} (hr : 0 < r) (z : ℂ) : ‖(z - t) / (r : ℂ)‖ = ‖z - t‖ / r := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]

theorem cayleyInv_sub_m7d {a b : ℂ} (ha : a ≠ 1) (hb : b ≠ 1) :
    CA.cayleyInv a - CA.cayleyInv b = 2 * Complex.I * (a - b) / ((1 - a) * (1 - b)) := by
  unfold CA.cayleyInv
  have ha' : 1 - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  have hb' : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  field_simp
  ring

theorem hasDerivAt_cayleyInv_m7d {w : ℂ} (hw : w ≠ 1) :
    HasDerivAt CA.cayleyInv (2 * Complex.I / (1 - w) ^ 2) w := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.I * (1 + w)) Complex.I w := by
    simpa using ((hasDerivAt_id w).const_add 1).const_mul Complex.I
  have h2 : HasDerivAt (fun w : ℂ => 1 - w) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have hne : 1 - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  exact (h1.div h2 hne).congr_deriv (by field_simp; ring)

theorem aff_mem_ball_m7d {t r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ ball (t : ℂ) r) :
    (z - t) / (r : ℂ) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_eq_norm] at hz
  rw [mem_ball_zero_iff, norm_aff_m7d hr, div_lt_one hr]; exact hz

theorem hasDerivAt_discMap_m7d {t r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ ball (t : ℂ) r) :
    HasDerivAt (discMap t r) (2 * Complex.I / (1 - (z - t) / r) ^ 2 * (1 / r)) z := by
  have hw := ne_one_of_norm_lt_m7d (mem_ball_zero_iff.1 (aff_mem_ball_m7d hr hz))
  have hin : HasDerivAt (fun z : ℂ => (z - t) / (r : ℂ)) (1 / r) z := by
    simpa using ((hasDerivAt_id z).sub_const (t : ℂ)).div_const (r : ℂ)
  exact (hasDerivAt_cayleyInv_m7d hw).comp z hin

theorem discMap_mem_H_m7d {t r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ ball (t : ℂ) r) :
    discMap t r z ∈ H :=
  bijOn_cayleyInv_ball_m7d.mapsTo (aff_mem_ball_m7d hr hz)

/-- **The Cayley map of the disc is conformal onto `ℍ`.** -/
theorem isConformalOnto_discMap_m7d {t r : ℝ} (hr : 0 < r) :
    IsConformalOnto (discMap t r) (ball (t : ℂ) r) H := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  refine ⟨isOpen_ball, fun z hz => (hasDerivAt_discMap_m7d hr hz).differentiableAt
    |>.differentiableWithinAt, ?_, ?_, fun z hz => ?_⟩
  · intro x hx y hy hxy
    have h := bijOn_cayleyInv_ball_m7d.injOn (aff_mem_ball_m7d hr hx) (aff_mem_ball_m7d hr hy) hxy
    exact sub_left_inj.1 ((div_left_inj' hr0).1 h)
  · have himg : (fun z : ℂ => (z - t) / (r : ℂ)) '' ball (t : ℂ) r = ball (0 : ℂ) 1 := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩; exact aff_mem_ball_m7d hr hz
      · intro hw
        refine ⟨t + r * w, ?_, by field_simp; ring⟩
        rw [mem_ball_zero_iff] at hw
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hr.le]
        nlinarith
    rw [show discMap t r '' ball (t : ℂ) r =
        CA.cayleyInv '' ((fun z : ℂ => (z - t) / (r : ℂ)) '' ball (t : ℂ) r) by
      rw [image_image]; rfl, himg, bijOn_cayleyInv_ball_m7d.image_eq]
  · rw [(hasDerivAt_discMap_m7d hr hz).deriv]
    have hw := ne_one_of_norm_lt_m7d (mem_ball_zero_iff.1 (aff_mem_ball_m7d hr hz))
    have h1 : 1 - (z - t) / (r : ℂ) ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
    simp [hr0, h1, Complex.I_ne_zero]

/-- Lower Lipschitz bound of the Cayley map on `closedBall t r'`. -/
theorem lower_lip_discMap_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r) :
    ∀ x ∈ closedBall (t : ℂ) r', ∀ y ∈ closedBall (t : ℂ) r',
      (1 / (2 * r)) * ‖x - y‖ ≤ ‖discMap t r x - discMap t r y‖ := by
  have hr : 0 < r := hr'.trans hr'r
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  intro x hx y hy
  have hxB := closedBall_subset_ball hr'r hx
  have hyB := closedBall_subset_ball hr'r hy
  set a := (x - t) / (r : ℂ)
  set b := (y - t) / (r : ℂ)
  have ha1 : ‖a‖ < 1 := mem_ball_zero_iff.1 (aff_mem_ball_m7d hr hxB)
  have hb1 : ‖b‖ < 1 := mem_ball_zero_iff.1 (aff_mem_ball_m7d hr hyB)
  have ha := ne_one_of_norm_lt_m7d ha1
  have hb := ne_one_of_norm_lt_m7d hb1
  have hab : a - b = (x - y) / r := by simp only [a, b]; field_simp; ring
  have hna : 0 < ‖1 - a‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm ha))
  have hnb : 0 < ‖1 - b‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hb))
  have hna2 : ‖1 - a‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) a; rw [norm_one] at this; linarith
  have hnb2 : ‖1 - b‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) b; rw [norm_one] at this; linarith
  unfold discMap
  rw [cayleyInv_sub_m7d ha hb, hab, norm_div, norm_mul, norm_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hr.le, norm_mul, Complex.norm_I, Complex.norm_two, mul_one]
  rw [le_div_iff₀ (mul_pos hna hnb)]
  have h4 : ‖1 - a‖ * ‖1 - b‖ ≤ 4 := by nlinarith
  have hxy := norm_nonneg (x - y)
  calc 1 / (2 * r) * ‖x - y‖ * (‖1 - a‖ * ‖1 - b‖) ≤ 1 / (2 * r) * ‖x - y‖ * 4 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2 * (‖x - y‖ / r) := by field_simp; ring

theorem measurable_discMap_m7d (t r : ℝ) : Measurable (discMap t r) := by
  unfold discMap CA.cayleyInv; fun_prop

theorem continuousOn_discMap_m7d {t r : ℝ} (hr : 0 < r) :
    ContinuousOn (discMap t r) (ball (t : ℂ) r) := fun _ hz =>
  (hasDerivAt_discMap_m7d hr hz).continuousAt.continuousWithinAt

/-- The Cayley pushforward of a symmetrized local measure is admissible on `ℍ`. -/
theorem isAdmissibleH_map_sym_m7d {t r r' : ℝ} (hr' : 0 < r') (hr'r : r' < r)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0) :
    IsAdmissibleH (((μ + μ.map conj).restrict (ball (t : ℂ) r)).map (discMap t r)) := by
  have hr : 0 < r := hr'.trans hr'r
  have hconjm : Measurable (conj : ℂ → ℂ) := Complex.continuous_conj.measurable
  have hφm := measurable_discMap_m7d t r
  have := hμ.1
  have hKB : closedBall (t : ℂ) r' ⊆ ball (t : ℂ) r := closedBall_subset_ball hr'r
  have hconjK : ∀ z ∈ closedBall (t : ℂ) r', conj z ∈ closedBall (t : ℂ) r' := fun z hz => by
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm, norm_conj_sub_ofReal_k3]; exact hz
  have hrestr : (μ + μ.map conj).restrict (ball (t : ℂ) r) = μ + μ.map conj := by
    refine Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff (s := ball (t : ℂ) r)).2 ?_)
    rw [Measure.add_apply, Measure.map_apply hconjm isOpen_ball.measurableSet.compl]
    have h1 : μ (ball (t : ℂ) r)ᶜ = 0 := measure_mono_null (compl_subset_compl.2 hKB) hμK
    have h2 : conj ⁻¹' (ball (t : ℂ) r)ᶜ = (ball (t : ℂ) r)ᶜ := by
      ext z; simp [mem_ball, dist_eq_norm, norm_conj_sub_ofReal_k3]
    rw [h2, h1, add_zero]
  rw [hrestr, Measure.map_add _ _ hφm, Measure.map_map hφm hconjm]
  have hc : (0 : ℝ) < 1 / (2 * r) := by positivity
  refine isAdmissibleH_add (isAdmissibleH_map hμ (isCompact_closedBall _ _) hμK hφm
    ((continuousOn_discMap_m7d hr).mono hKB) ?_ hc (lower_lip_discMap_m7d hr' hr'r))
    (isAdmissibleH_map hμ (isCompact_closedBall _ _) hμK (hφm.comp hconjm)
      (((continuousOn_discMap_m7d hr).mono hKB).comp Complex.continuous_conj.continuousOn
        fun z hz => hconjK z hz) ?_ hc ?_)
  · rintro _ ⟨z, hz, rfl⟩
    exact le_of_lt (show (0 : ℝ) < (discMap t r z).im from discMap_mem_H_m7d hr (hKB hz))
  · rintro _ ⟨z, hz, rfl⟩
    exact le_of_lt (show (0 : ℝ) < (discMap t r (conj z)).im from
      discMap_mem_H_m7d hr (hKB (hconjK z hz)))
  · intro x hx y hy
    have := lower_lip_discMap_m7d hr' hr'r (conj x) (hconjK x hx) (conj y) (hconjK y hy)
    rwa [← map_sub, Complex.norm_conj] at this

/-- **Remaining node (explicit Green identity).** For local admissible `μ, ν`, the Green energy
of the symmetrized measures for `G_B = G_ℍ ∘ (φ × φ)` is twice the half-disc Green kernel
(`G_U(z,w) = G_B(z,w) + G_B(z,w̄)`). -/
def HalfDiscGreenIdStmt (t r r' : ℝ) : Prop :=
  0 < r' → r' < r → ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
    IsAdmissibleH ν → ν (closedBall (t : ℂ) r')ᶜ = 0 →
      ∫ x in ball (t : ℂ) r, ∫ y in ball (t : ℂ) r, greenH (discMap t r x) (discMap t r y)
          ∂(ν + ν.map conj) ∂(μ + μ.map conj) = 2 * kernelCov (halfDiscGreen t r) μ ν

/-- **D6: the disc-kernel node from the explicit Green identity** (conformal invariance). -/
theorem halfDiscDiscKernel_of_greenId {t r r' : ℝ} (h : HalfDiscGreenIdStmt t r r') :
    HalfDiscDiscKernelStmt t r r' := by
  intro hr' hr'r μ ν hμ hμK hν hνK
  have := hμ.1; have := hν.1
  rw [dualCov_conformal_eq_kernel (isConformalOnto_discMap_m7d (hr'.trans hr'r))
    (isAdmissibleH_map_sym_m7d hr' hr'r hμ hμK) (isAdmissibleH_map_sym_m7d hr' hr'r hν hνK)]
  exact h hr' hr'r μ ν hμ hμK hν hνK

/-- **The half-disc covariance from the explicit Green identity.** -/
theorem halfDiscMixedCov_of_greenId {t r r' : ℝ} (h : HalfDiscGreenIdStmt t r r') :
    HalfDiscMixedCovStmt t r r' :=
  halfDiscMixedCov_of_discKernel (halfDiscDiscKernel_of_greenId h)

end QuantumZipper.K3
