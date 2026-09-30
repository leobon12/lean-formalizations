import QuantumZipper.Proofs.Thm18.ASep3Box
import QuantumZipper.Proofs.Zipper.JointModFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 7): `GenFam` for pushed circles, and with the scale

The regularization of the rescaled field `rescale X Q s` at a pushed circle `fc(c, ρ).map f_t⁻¹`
reads `X` at the dilated pushed circles `(fc(c, ρ).map f_t⁻¹).map (s ·)`. For the joint witness
of the unzipped rescaled field (the scale analogue of `ASep.ae_exists_joint_witness_fixed`), these
must form a Kolmogorov family in `(t, c, ρ, s)`.

* `genFam_νT`: parameters `p = (t, Re c, Im c)` in a set `S` with `t ∈ [0,T]`, `‖c‖ ≤ R₀`, radius
  `r₀ + ρ`, `ρ ∈ [0,1]`: `GenFam` from the time and space moduli `abs_kernelCov2_νT_time_unif`,
  `abs_kernelCov2_νT_space_unif` (JointModKolm.lean);
* **`genFam_νT_dil`**: the same family dilated by `s ∈ [s₀, s₁]` (`genFam_dil`, with the uniform
  Frostman bound `RegUnif.νT_box_facts`).

Own bookkeeping (moduli: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open GenUC

/-- The centre coordinate of a parameter `(t, Re c, Im c)`. -/
def cpt (p : Fin 3 → ℝ) : ℂ := ⟨p 1, p 2⟩

/-- The pushed-circle family with radius `r₀ + ρ`. -/
abbrev nuTFam (W : ℝ → ℝ) (r₀ : ℝ) (p : Fin 3 → ℝ) (ρ : ℝ) : Measure ℂ :=
  RegCont.νT W (cpt p) (r₀ + ρ) (p 0)

theorem norm_cpt_sub_le (p p' : Fin 3 → ℝ) : ‖cpt p - cpt p'‖ ≤ 2 * dist p p' := by
  have h1 := dist_le_pi_dist p p' 1
  have h2 := dist_le_pi_dist p p' 2
  rw [Real.dist_eq] at h1 h2
  have e : cpt p - cpt p' = ⟨p 1 - p' 1, p 2 - p' 2⟩ := by
    apply Complex.ext <;> simp [cpt]
  rw [e]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only
  linarith

/-- **`GenFam` for pushed circles.** -/
theorem genFam_νT {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T a CH : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hCH : 0 ≤ CH)
    (hH : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 →
      |W t - W t'| ≤ CH * |t - t'| ^ a)
    {r₀ R₀ : ℝ} (hr₀ : 0 < r₀) {S : Set (Fin 3 → ℝ)}
    (hS : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ ‖cpt p‖ ≤ R₀) :
    ∃ K c : ℝ, GenUC.GenFam S (nuTFam W r₀) 1 K c := by
  obtain ⟨M, hM⟩ := RegCont.exists_abs_le_on_Icc hW T
  set Rr : ℝ := R₀ + r₀ + 1 with hRr
  set β : ℝ := a / 12 with hβ
  have hβ0 : 0 < β := by positivity
  have hβ1 : β ≤ 1 / 12 := by rw [hβ]; linarith
  have hr : ∀ ρ ∈ Icc (0 : ℝ) 1, r₀ ≤ r₀ + ρ := fun ρ hρ => by linarith [hρ.1]
  have hwR : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1, ‖cpt p‖ + (r₀ + ρ) ≤ Rr := fun p hp ρ hρ => by
    have := (hS p hp).2; rw [hRr]; linarith [hρ.2]
  have hfacts : ∀ p ∈ S, ∀ ρ ∈ Icc (0 : ℝ) 1,
      IsAdmissibleH (nuTFam W r₀ p ρ) ∧ nuTFam W r₀ p ρ univ = 1 := fun p hp ρ hρ => by
    obtain ⟨i1, f1, b1⟩ := RegUnif.νT_box_facts hW hW0 hr₀ hM (hS p hp).1 (hr ρ hρ)
      (hwR p hp ρ hρ)
    have := i1
    refine ⟨FrostmanReg.isAdmissibleH_of_frostman (R := RegCont.revBound (2 * M) T Rr) ?_ f1
      (by norm_num), measure_univ⟩
    have h1 : ∀ᵐ x ∂nuTFam W r₀ p ρ, x ∈ closedBall (0 : ℂ) (RegCont.revBound (2 * M) T Rr) ∩ Hbar :=
      b1.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
    exact ae_iff.1 h1
  set Kt := RegUnif.timeK M T r₀ Rr CH
  set Ks := RegUnif.spaceK M T r₀ Rr
  have hT : ∀ p ∈ S, 0 ≤ T := fun p hp => (hS p hp).1.1.trans (hS p hp).1.2
  have hM0 : ∀ p ∈ S, 0 ≤ M := fun p hp => (abs_nonneg _).trans (hM 0 ⟨le_rfl, hT p hp⟩)
  by_cases hSne : S.Nonempty
  swap
  · refine ⟨0, 1, ⟨fun p hp => absurd ⟨p, hp⟩ hSne, fun p hp => absurd ⟨p, hp⟩ hSne, le_rfl,
      one_pos, fun p hp => absurd ⟨p, hp⟩ hSne⟩⟩
  obtain ⟨p₀, hp₀⟩ := hSne
  have hKt0 : 0 ≤ Kt := by
    have := RegUnif.timeConst_nonneg (R := Rr) (hM0 p₀ hp₀) (hT p₀ hp₀) hr₀
    have := RegUnif.potC_nonneg (R := Rr) (hM0 p₀ hp₀) (hT p₀ hp₀) hr₀
    unfold Kt RegUnif.timeK; positivity
  have hKs0 : 0 ≤ Ks := by
    have := RegUnif.spaceConst_nonneg (R := Rr) (hM0 p₀ hp₀) (hT p₀ hp₀) hr₀
    have := RegUnif.potC_nonneg (R := Rr) (hM0 p₀ hp₀) (hT p₀ hp₀) hr₀
    unfold Ks RegUnif.spaceK; positivity
  refine ⟨2 * Kt + 2 * Ks * 2 ^ β, β, ⟨fun p hp ρ hρ => (hfacts p hp ρ hρ).1,
    fun p hp ρ hρ => (hfacts p hp ρ hρ).2, by positivity, hβ0,
    fun p hp p' hp' ρ hρ ρ' hρ' => ?_⟩⟩
  -- intermediate: circle of `p`, time of `p'`
  set m1 := nuTFam W r₀ p ρ
  set m2 := RegCont.νT W (cpt p) (r₀ + ρ) (p' 0)
  set m3 := nuTFam W r₀ p' ρ'
  obtain ⟨i2, f2, b2⟩ := RegUnif.νT_box_facts hW hW0 hr₀ hM (hS p' hp').1 (hr ρ hρ)
    (hwR p hp ρ hρ)
  have := i2
  have ad2 : IsAdmissibleH m2 := by
    refine FrostmanReg.isAdmissibleH_of_frostman (R := RegCont.revBound (2 * M) T Rr) ?_ f2 (by norm_num)
    have h1 : ∀ᵐ x ∂m2, x ∈ closedBall (0 : ℂ) (RegCont.revBound (2 * M) T Rr) ∩ Hbar :=
      b2.mono fun z hz => ⟨mem_closedBall_zero_iff.2 hz.2, (show (0 : ℝ) < z.im from hz.1).le⟩
    exact ae_iff.1 h1
  have hm2 : m2 univ = 1 := measure_univ
  have ad1 := (hfacts p hp ρ hρ).1
  have ad3 := (hfacts p' hp' ρ' hρ').1
  have hm1 := (hfacts p hp ρ hρ).2
  have hm3 := (hfacts p' hp' ρ' hρ').2
  have htri := RegUnif.kernelCov2_self_triangle ad1 ad2 ad3 (hm1.trans hm2.symm)
    (hm2.trans hm3.symm)
  have hnn : 0 ≤ kernelCov2 neumannH (m1, m3) (m1, m3) := by
    rw [RegUnif.kernelCov2_self_eq_norm_sq ad1 ad3 (hm1.trans hm3.symm)]; positivity
  set x := dist p p' + |ρ - ρ'| with hx
  have hx0 : 0 ≤ x := by positivity
  have v1 : |kernelCov2 neumannH (m1, m2) (m1, m2)| ≤ Kt * x ^ β := by
    refine (RegUnif.abs_kernelCov2_νT_time_unif hW hW0 hr₀ hM ha ha1 hCH hH (hr ρ hρ)
      (hwR p hp ρ hρ) (hS p hp).1 (hS p' hp').1).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) ?_ hβ0.le) hKt0
    have := dist_le_pi_dist p p' 0
    rw [Real.dist_eq] at this
    linarith [abs_nonneg (ρ - ρ')]
  have v2 : |kernelCov2 neumannH (m2, m3) (m2, m3)| ≤ Ks * 2 ^ β * x ^ β := by
    refine (RegUnif.abs_kernelCov2_νT_space_unif hW hW0 hr₀ hM hβ0.le hβ1 (hS p' hp').1
      (hr ρ hρ) (hr ρ' hρ') (hwR p hp ρ hρ) (hwR p' hp' ρ' hρ')).trans ?_
    have hd : ‖cpt p - cpt p'‖ + |r₀ + ρ - (r₀ + ρ')| ≤ 2 * x := by
      have := norm_cpt_sub_le p p'
      rw [show r₀ + ρ - (r₀ + ρ') = ρ - ρ' by ring, hx]
      linarith [abs_nonneg (ρ - ρ')]
    calc Ks * (‖cpt p - cpt p'‖ + |r₀ + ρ - (r₀ + ρ')|) ^ β ≤ Ks * (2 * x) ^ β :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hd hβ0.le) hKs0
      _ = Ks * 2 ^ β * x ^ β := by rw [Real.mul_rpow (by norm_num) hx0]; ring
  rw [abs_of_nonneg hnn]
  have := (le_abs_self _).trans v1
  have := (le_abs_self _).trans v2
  linarith

end ASep
end QuantumZipper
