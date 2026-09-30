import QuantumZipper.Proofs.LQG.CoordChangeW

/-!
# M4-T4, step 4: the two-radius lemma along the image of the interval

In `t`-coordinates, compare the density at the variable radius `ψ'(t) 2^{-k}` around `ψ(t)`
(`wProc`) with the dyadic density at radius `2^{j-k}` around `ψ(t)` (`bU`, coarser since
`ψ' ≤ 2^j`). The Gaussian hypotheses `TRLHyp` hold with decorrelation length
`δ = 2·2^{j-k}/m`, because `|ψ t − ψ u| ≥ m |t − u|` (`trlHyp_coordChange`), and `trl_bound`
gives an `L¹` bound with a geometric rate in `k` (`trl_coordChange_bound`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate Real
open scoped ENNReal NNReal

namespace QuantumZipper
namespace CoordChange

open GaussTK BdryExist TwoRadius

variable {Ω : Type*} [MeasurableSpace Ω]

theorem fcPairCov_incr_gen {s ε ε' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') :
    fcPairCov ((s : ℂ), ε, (s : ℂ), ε') ((s : ℂ), ε, (s : ℂ), ε') = 2 * log (ε' / ε) := by
  have hε' : 0 < ε' := hε.trans_le hεε'
  simp only [fcPairCov, kernelCov2]
  rw [kernelCov_fc_real_sameCenter hε hε, kernelCov_fc_real_sameCenter hε hε',
    kernelCov_fc_real_sameCenter hε' hε, kernelCov_fc_real_sameCenter hε' hε', max_self,
    max_self, max_eq_right hεε', max_eq_left hεε', log_div hε'.ne' hε.ne']
  ring

theorem radius_sub_eq {j k : ℕ} (hjk : j ≤ k) : radius (k - j) = 2 ^ j * radius k := by
  unfold radius
  rw [show k = (k - j) + j from (Nat.sub_add_cancel hjk).symm]
  rw [Nat.add_sub_cancel, pow_add, ← mul_assoc, mul_comm ((2 : ℝ) ^ j), mul_assoc, ← mul_pow]
  norm_num

/-- A globally measurable version of `t ↦ Re ψ(t)` on `[a, b]`. -/
@[irreducible] def psiRe (ψ : ℂ → ℂ) (a b : ℝ) : ℝ → ℝ :=
  by classical exact (Icc a b).piecewise (fun t => (ψ t).re) (fun _ => 0)

namespace Data

variable {ψ : ℂ → ℂ} {a b δ m C : ℝ}

theorem hasDerivAt_re_psi (h : Data ψ a b δ m C) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivAt (fun x : ℝ => (ψ x).re) (deriv ψ t).re t :=
  (((h.diff t ht) _ (mem_ball_self (by linarith [h.δpos]))).differentiableAt
    (isOpen_ball.mem_nhds (mem_ball_self (by linarith [h.δpos])))).hasDerivAt.real_of_complex

theorem psi_re_sub_ge (h : Data ψ a b δ m C) {t u : ℝ} (ht : t ∈ Icc a b) (hu : u ∈ Icc a b)
    (htu : t ≤ u) : m * (u - t) ≤ (ψ u).re - (ψ t).re :=
  (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv (f := fun x : ℝ => (ψ x).re)
    (fun x hx => (h.hasDerivAt_re_psi hx).continuousAt.continuousWithinAt)
    (fun x hx => (h.hasDerivAt_re_psi (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [(h.hasDerivAt_re_psi (interior_subset hx)).deriv]; exact h.dre x (interior_subset hx))
    t ht u hu htu

theorem abs_psi_re_sub_ge (h : Data ψ a b δ m C) {t u : ℝ} (ht : t ∈ Icc a b)
    (hu : u ∈ Icc a b) : m * |t - u| ≤ |(ψ t).re - (ψ u).re| := by
  have hm := h.mpos
  rcases le_total t u with htu | htu
  · have := h.psi_re_sub_ge ht hu htu
    rw [abs_sub_comm t u, abs_of_nonneg (by linarith), abs_sub_comm,
      abs_of_nonneg (by nlinarith)]
    exact this
  · have := h.psi_re_sub_ge hu ht htu
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by nlinarith)]
    exact this

theorem continuousOn_re_psi (h : Data ψ a b δ m C) :
    ContinuousOn (fun t : ℝ => (ψ t).re) (Icc a b) :=
  fun t ht => (h.hasDerivAt_re_psi ht).continuousAt.continuousWithinAt

theorem measurable_psiRe (h : Data ψ a b δ m C) : Measurable (psiRe ψ a b) := by
  classical
  unfold psiRe
  exact ContinuousOn.measurable_piecewise h.continuousOn_re_psi continuousOn_const
    measurableSet_Icc

theorem psiRe_eq {t : ℝ} (ht : t ∈ Icc a b) : psiRe ψ a b t = (ψ t).re := by
  unfold psiRe Set.piecewise
  simp [ht]

section TRLParts

variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
  (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {R : ℝ}
  (hR : ∀ t ∈ Icc a b, |(ψ t).re| + 1 ≤ R) {j k : ℕ} (hjk : j ≤ k)
  (hj : ∀ t ∈ Icc a b, (deriv ψ t).re ≤ 2 ^ j) (hk : 2 ^ j * radius k ≤ 1 / 4)
include hX h hR hjk hj hk

theorem trl_hUe {t : ℝ} (ht : t ∈ Icc a b) :
    (fun ω => bU X R (k - j) (psiRe ψ a b t) ω) =ᵐ[P]
      fcPairVal X ((((ψ t).re : ℝ) : ℂ), radius (k - j), 0, R) := by
  rw [psiRe_eq ht]; exact avgReg_zField_ae_eq hX R (k - j) (ofReal_mem_Hbar _)

theorem trl_hr21 {t : ℝ} (ht : t ∈ Icc a b) : (deriv ψ t).re * radius k ≤ radius (k - j) := by
  rw [radius_sub_eq hjk]; exact mul_le_mul_of_nonneg_right (hj t ht) (radius_pos k).le

theorem trl_hΔe {t : ℝ} (ht : t ∈ Icc a b) :
    (fun ω => wProc X ψ R (radius k) t ω - bU X R (k - j) (psiRe ψ a b t) ω) =ᵐ[P]
      fcPairVal X ((((ψ t).re : ℝ) : ℂ), (deriv ψ t).re * radius k,
        (((ψ t).re : ℝ) : ℂ), radius (k - j)) := by
  have hW := h.ae_wProc_eq hX ht R (radius_pos k)
    ((trl_hr21 hX h hR hjk hj hk ht).trans (by rw [radius_sub_eq hjk]; exact hk))
  filter_upwards [trl_hUe hX h hR hjk hj hk ht, hW] with ω h1 h2
  rw [h1, h2]
  simp only [fcPairVal]; ring

theorem trl_lawU {t : ℝ} (ht : t ∈ Icc a b) :
    HasLaw (fun ω => bU X R (k - j) (psiRe ψ a b t) ω) (gaussianReal 0 (bV R (k - j))) P := by
  have hr1 : 0 < radius (k - j) := radius_pos _
  have hR0 : 0 < R := by linarith [hR t ht, abs_nonneg (ψ t).re]
  have := (hasLaw_fcPairVal hX (good_Z (ofReal_mem_Hbar (ψ t).re) hr1 hR0)).congr
    (trl_hUe hX h hR hjk hj hk ht)
  rw [fcPairCov_Zself hr1 (by linarith [hR t ht, radius_le_one (k - j)])] at this
  exact this

theorem trl_lawΔ {t : ℝ} (ht : t ∈ Icc a b) :
    HasLaw (fun ω => wProc X ψ R (radius k) t ω - bU X R (k - j) (psiRe ψ a b t) ω)
      (gaussianReal 0 (2 * log (radius (k - j) / ((deriv ψ t).re * radius k))).toNNReal) P := by
  have hr1 : 0 < radius (k - j) := radius_pos _
  have hr2 : 0 < (deriv ψ t).re * radius k := mul_pos (h.deriv_re_pos ht) (radius_pos k)
  have := (hasLaw_fcPairVal hX (good_real (s := (ψ t).re) (t := (ψ t).re) hr2 hr1)).congr
    (trl_hΔe hX h hR hjk hj hk ht)
  rw [fcPairCov_incr_gen hr2 (trl_hr21 hX h hR hjk hj hk ht)] at this
  exact this

theorem trl_indep {t : ℝ} (ht : t ∈ Icc a b) :
    IndepFun (fun ω => wProc X ψ R (radius k) t ω - bU X R (k - j) (psiRe ψ a b t) ω)
      (fun ω => bU X R (k - j) (psiRe ψ a b t) ω) P := by
  have hr1 : 0 < radius (k - j) := radius_pos _
  have hr2 : 0 < (deriv ψ t).re * radius k := mul_pos (h.deriv_re_pos ht) (radius_pos k)
  have hR0 : 0 < R := by linarith [hR t ht, abs_nonneg (ψ t).re]
  have hI := indepFun_fcPair hX
    (fun _ : Unit => (⟨((((ψ t).re : ℝ) : ℂ), (deriv ψ t).re * radius k,
      (((ψ t).re : ℝ) : ℂ), radius (k - j)), good_real hr2 hr1⟩ : {p : FcIdx // p.Good}))
    (fun _ : Unit => (⟨((((ψ t).re : ℝ) : ℂ), radius (k - j), 0, R),
      good_Z (ofReal_mem_Hbar _) hr1 hR0⟩ : {p : FcIdx // p.Good}))
    (fun _ _ => fcPairCov_incr_Zsame hr2 (trl_hr21 hX h hR hjk hj hk ht)
      (by linarith [hR t ht, radius_le_one (k - j)]))
  have hI2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
  exact hI2.congr (trl_hΔe hX h hR hjk hj hk ht).symm (trl_hUe hX h hR hjk hj hk ht).symm

theorem trl_decor {t u : ℝ} (ht : t ∈ Icc a b) (hu : u ∈ Icc a b)
    (htu : 2 * radius (k - j) / m ≤ |t - u|) :
    IndepFun (fun ω => wProc X ψ R (radius k) t ω - bU X R (k - j) (psiRe ψ a b t) ω)
      (fun ω => (bU X R (k - j) (psiRe ψ a b t) ω, bU X R (k - j) (psiRe ψ a b u) ω,
        wProc X ψ R (radius k) u ω - bU X R (k - j) (psiRe ψ a b u) ω)) P := by
  have hm := h.mpos
  have hr1 : 0 < radius (k - j) := radius_pos _
  have hsep : radius (k - j) + max (radius (k - j)) (radius (k - j)) ≤
      |(ψ t).re - (ψ u).re| := by
    rw [max_self]
    have h1 := h.abs_psi_re_sub_ge ht hu
    have h2 : 2 * radius (k - j) ≤ m * |t - u| := by
      rw [div_le_iff₀ hm] at htu; linarith
    linarith
  have hI := indepFun_incr_bullet1 hX (t := (ψ t).re) (u := (ψ u).re)
    (ε := (deriv ψ t).re * radius k) (ε' := radius (k - j)) (r := radius (k - j))
    (δ := (deriv ψ u).re * radius k) (δ' := radius (k - j)) (R := R)
    (mul_pos (h.deriv_re_pos ht) (radius_pos k)) (trl_hr21 hX h hR hjk hj hk ht)
    hr1 (mul_pos (h.deriv_re_pos hu) (radius_pos k)) (trl_hr21 hX h hR hjk hj hk hu)
    (by linarith [hR t ht, radius_le_one (k - j)]) (by linarith [hR u hu, radius_le_one (k - j)])
    hsep
  have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
    (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
  have hI2 := hI.comp (measurable_pi_apply ()) hφ
  refine hI2.congr (trl_hΔe hX h hR hjk hj hk ht).symm ?_
  filter_upwards [trl_hUe hX h hR hjk hj hk ht, trl_hUe hX h hR hjk hj hk hu,
    trl_hΔe hX h hR hjk hj hk hu] with ω h1 h2 h3
  simp only [Function.comp_apply]
  rw [h3, h1, h2]
  rfl

end TRLParts

theorem measurable_trl_w (ψ : ℂ → ℂ) (j k : ℕ) :
    Measurable (fun t : ℝ => (2 * log (radius (k - j) / ((deriv ψ t).re * radius k))).toNNReal) :=
  Measurable.real_toNNReal (measurable_const.mul (Measurable.log
    (measurable_const.div ((Complex.continuous_re.measurable.comp
      ((measurable_deriv ψ).comp Complex.continuous_ofReal.measurable)).mul_const _))))

theorem trl_measU {P : Measure Ω} {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (h : Data ψ a b δ m C) {R : ℝ} {n : ℕ} :
    Measurable (fun p : ℝ × Ω => bU X R n (psiRe ψ a b p.1) p.2) := by
  exact (measurable_avgReg n).comp (((measurable_zField hX R).comp measurable_snd).prodMk
    (Complex.continuous_ofReal.measurable.comp (h.measurable_psiRe.comp measurable_fst)))

theorem trl_measΔ {P : Measure Ω} {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    (h : Data ψ a b δ m C) {R r : ℝ} {n : ℕ} :
    Measurable (fun p : ℝ × Ω => wProc X ψ R r p.1 p.2 - bU X R n (psiRe ψ a b p.1) p.2) :=
  (measurable_wProc hX ψ R r).sub (trl_measU hX h)

/-- The Gaussian hypotheses of the two-radius lemma along `ψ([a, b])`. -/
theorem trlHyp_coordChange {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {R : ℝ}
    (hR : ∀ t ∈ Icc a b, |(ψ t).re| + 1 ≤ R) {j k : ℕ} (hjk : j ≤ k)
    (hj : ∀ t ∈ Icc a b, (deriv ψ t).re ≤ 2 ^ j) (hk : 2 ^ j * radius k ≤ 1 / 4) :
    TRLHyp P (Icc a b) (2 * radius (k - j) / m) (2 * log R) (2 * log (2 ^ j / m))
      (fun _ => log (1 / radius (k - j))) (fun _ => bV R (k - j))
      (fun t => (2 * log (radius (k - j) / ((deriv ψ t).re * radius k))).toNNReal)
      (fun t ω => bU X R (k - j) (psiRe ψ a b t) ω)
      (fun t ω => wProc X ψ R (radius k) t ω - bU X R (k - j) (psiRe ψ a b t) ω) := by
  refine ⟨trl_measU hX h, trl_measΔ hX h, measurable_const, measurable_trl_w ψ j k,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    beta_reduce
    exact trl_lawU hX h hR hjk hj hk ht
  · intro t ht
    beta_reduce
    exact trl_lawΔ hX h hR hjk hj hk ht
  · intro t ht
    beta_reduce
    have hlogR : 0 ≤ log R := log_nonneg (by linarith [hR t ht, abs_nonneg (ψ t).re])
    have hlogr : log (radius (k - j)) ≤ 0 := log_nonpos (radius_pos _).le (radius_le_one _)
    show ((2 * log R - 2 * log (radius (k - j))).toNNReal : ℝ) ≤
      2 * log (1 / radius (k - j)) + 2 * log R
    rw [Real.coe_toNNReal _ (by linarith), one_div, log_inv]
    linarith
  · intro t ht
    beta_reduce
    have hm := h.mpos
    have hd := h.deriv_re_pos ht
    have hq : radius (k - j) / ((deriv ψ t).re * radius k) = 2 ^ j / (deriv ψ t).re := by
      have := radius_pos k
      rw [radius_sub_eq hjk, div_eq_div_iff (by positivity) hd.ne']; ring
    have h1 : 1 ≤ 2 ^ j / (deriv ψ t).re := by rw [le_div_iff₀ hd]; linarith [hj t ht]
    rw [hq, Real.coe_toNNReal _ (by have := log_nonneg h1; linarith)]
    have h2 : 2 ^ j / (deriv ψ t).re ≤ 2 ^ j / m :=
      div_le_div_of_nonneg_left (by positivity) hm (h.dre t ht)
    have := log_le_log (by linarith) h2
    linarith
  · intro t ht
    beta_reduce
    exact trl_indep hX h hR hjk hj hk ht
  · intro t ht u hu htu
    beta_reduce
    exact trl_decor hX h hR hjk hj hk ht hu htu

/-- **Two-radius bound along `ψ([a, b])`** (M4-T4 step 4). -/
theorem trl_coordChange_bound {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample}
    (hX : IsFreeGFFModConstH X P) (h : Data ψ a b δ m C) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {R : ℝ} (hR : ∀ t ∈ Icc a b, |(ψ t).re| + 1 ≤ R) {j k : ℕ} (hjk : j ≤ k)
    (hj : ∀ t ∈ Icc a b, (deriv ψ t).re ≤ 2 ^ j) (hk : 2 ^ j * radius k ≤ 1 / 4)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ t, |f t| ≤ M) :
    ∫ ω, |∫ t in Icc a b, f t * (radius (k - j) ^ (γ ^ 2 / 4) *
        exp (γ / 2 * bU X R (k - j) (psiRe ψ a b t) ω) -
        ((deriv ψ t).re * radius k) ^ (γ ^ 2 / 4) * exp (γ / 2 * wProc X ψ R (radius k) t ω))| ∂P
      ≤ √(M ^ 2 * ((1 + exp (γ ^ 2 / 4 * (2 * log (2 ^ j / m)))) *
            (exp ((γ - max 0 ((3 * γ - 2) / 4)) ^ 2 * (2 * log R) / 2) *
            exp ((γ ^ 2 / 2 - (max 0 ((3 * γ - 2) / 4)) ^ 2) * log (1 / radius (k - j))))) *
            (2 * (2 * radius (k - j) / m) * volume.real (Icc a b)))
        + M * (2 * (exp ((γ / 2 + (2 - γ) / 4) ^ 2 * (2 * log R) / 2) *
            exp (-((2 - γ) ^ 2 / 16) * log (1 / radius (k - j))))) * volume.real (Icc a b) := by
  have hr := radius_pos k
  have hr1 : 0 < radius (k - j) := radius_pos _
  have hrk : radius (k - j) = 2 ^ j * radius k := radius_sub_eq hjk
  have hH := h.trlHyp_coordChange hX hR hjk hj hk
  have hδ : 0 ≤ 2 * radius (k - j) / m := by have := h.mpos; positivity
  have hcore := trl_bound hγ hγ2 hδ measurableSet_Icc measure_Icc_lt_top hf hM hH
    (fun t _ => le_rfl) (fun t _ => le_rfl)
  refine le_trans (le_of_eq ?_) hcore
  congr 1; funext ω; congr 1
  refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  have hd := h.deriv_re_pos ht
  have h2 : 0 < (deriv ψ t).re * radius k := mul_pos hd hr
  have h21 : (deriv ψ t).re * radius k ≤ radius (k - j) := by
    rw [hrk]; exact mul_le_mul_of_nonneg_right (hj t ht) hr.le
  have hw : (((2 * log (radius (k - j) / ((deriv ψ t).re * radius k))).toNNReal : ℝ≥0) : ℝ) =
      2 * log (radius (k - j) / ((deriv ψ t).re * radius k)) := by
    refine Real.coe_toNNReal _ ?_
    have := log_nonneg ((one_le_div h2).2 h21); linarith
  have hXY : ∀ X Y : ℝ, exp X * (1 - exp Y) = exp X - exp (X + Y) := by
    intro X Y; rw [exp_add]; ring
  simp only [trlD, tiltY]
  rw [hXY, hw, rpow_def_of_pos hr1, rpow_def_of_pos h2, one_div, log_inv,
    log_div hr1.ne' h2.ne', ← exp_add, ← exp_add]
  congr 1; congr 1 <;> (congr 1; ring)

end Data

end CoordChange
end QuantumZipper
