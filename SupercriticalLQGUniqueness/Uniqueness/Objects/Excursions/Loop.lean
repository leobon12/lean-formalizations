import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.C3b




 
















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

variable {C : Objects.CorrectedEvent.Constants} {D Db : LSCMetric} {f : C(ℂ, ℝ)} {V : TopologicalSpace.Opens ℂ}
  {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ}

 
theorem sqrt_le_half_of_le_ep {ε : ℝ} (_hε : 0 ≤ ε) (hεep : ε ≤ (2 : ℝ) ^ (-(C.k0 : ℝ))) :
    Real.sqrt ε ≤ 1 / 2 := by
  have hep : (2 : ℝ) ^ (-(C.k0 : ℝ)) ≤ 1 / 4 := by
    have h48 : (48 : ℝ) ≤ C.k0 := by exact_mod_cast C.k0Large
    calc (2 : ℝ) ^ (-(C.k0 : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1 / 4 := by norm_num
  rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (hεep.trans hep)

 
theorem protect_of_mid {z : ℂ} (hz : 3 / 2 * C.r < ‖z‖ ∧ ‖z‖ < 5 / 2 * C.r) {ε : ℝ}
    (hε : Real.sqrt ε ≤ 1 / 2) :
    closedBall z (Real.sqrt ε * C.r) ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := by
  intro x hx
  have hr := C.rPos
  rw [mem_closedBall, dist_eq_norm] at hx
  have hsr : Real.sqrt ε * C.r ≤ C.r / 2 := by nlinarith
  have h1 : ‖z‖ - ‖x - z‖ ≤ ‖x‖ := by
    have := norm_sub_norm_le z (z - x)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  have h2 : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
    have := norm_add_le z (x - z)
    rwa [add_sub_cancel] at this
  change C.r < dist x 0 ∧ dist x 0 < 4 * C.r
  rw [dist_zero_right]
  constructor <;> linarith

 
theorem half_le_dist_of_norms {x y : ℂ} (hx : ‖x‖ = 3 * C.r) (hy : ‖y‖ < 5 / 2 * C.r) :
    C.r / 2 ≤ dist x y := by
  rw [dist_eq_norm]
  have := norm_sub_norm_le x y
  linarith

 
theorem eloop_tau (S : ExcSetting C D Db f V P L τ' τ σ σ') (hS3 : Objects.CorrectedEvent.S3 C D)
    (hline4 : C.c_reg⁻¹ ^ 2 * (1 + C.c_reg) ^ 3 * (2 : ℝ) ^ (2 * theta C) *
      ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ theta C ≤ 1)
    {τ₀ σ₀ : ℝ} (hτ₀ : τ' ≤ τ₀) (hτ₀τ : τ₀ ≤ τ) (hσσ₀ : σ ≤ σ₀) (hσ₀ : σ₀ ≤ σ')
    (hnτ₀ : ‖P τ₀‖ = 3 * C.r) (hnσ₀ : ‖P σ₀‖ = 3 * C.r)
    {ε : ℝ} (hε : 0 < ε) (hεep : ε ≤ (2 : ℝ) ^ (-(C.k0 : ℝ))) :
    Objects.CorrectedEvent.around D (P τ) (ε * C.r) (Real.sqrt ε * C.r) ≤ ENNReal.ofReal (ε ^ theta C * (τ - τ₀)) := by
  have hr := C.rPos
  have hsq := sqrt_le_half_of_le_ep (C := C) hε.le hεep
  have hnτ := S.norm_τ
  have has : τ₀ < τ := lt_of_le_of_ne hτ₀τ (fun h => by rw [h] at hnτ₀; linarith [hnτ.2])
  have hsb : τ < σ₀ := lt_of_le_of_ne (S.τ_le_σ.trans hσσ₀)
    (fun h => by rw [← h] at hnσ₀; linarith [hnτ.2])
  have hfar : ∀ {t : ℝ}, ‖P t‖ = 3 * C.r → Real.sqrt ε * C.r ≤ dist (P t) (P τ) := by
    intro t ht
    have := half_le_dist_of_norms ht hnτ.2
    nlinarith
  refine c3_core C D Db f S.forget S.weyl S.f_bd hS3 hline4 hε hεep (protect_of_mid hnτ hsq)
    has hsb (S.cont_sub hτ₀ hσ₀) ?_ ?_ (hfar hnτ₀) (hfar hnσ₀) (by rw [dist_self]; exact mul_nonneg hε.le hr.le)
  · intro u v hu huv hv
    exact S.dist_eq (hτ₀.trans hu) huv (hv.trans hσ₀)
  · intro u v hu huv hv
    refine ⟨S.isCurve (S.τ'_nonneg.trans (hτ₀.trans hu)) huv
      (hv.trans (S.τ_le_σ.trans (S.σ_le_σ'.trans S.σ'_le_L))), ?_⟩
    exact (S.len_eq_before (hτ₀.trans hu) huv hv).le

 
theorem eloop_sigma (S : ExcSetting C D Db f V P L τ' τ σ σ') (hS3 : Objects.CorrectedEvent.S3 C D)
    (hline4 : C.c_reg⁻¹ ^ 2 * (1 + C.c_reg) ^ 3 * (2 : ℝ) ^ (2 * theta C) *
      ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ theta C ≤ 1)
    {τ₀ σ₀ : ℝ} (hτ₀ : τ' ≤ τ₀) (hτ₀τ : τ₀ ≤ τ) (hσσ₀ : σ ≤ σ₀) (hσ₀ : σ₀ ≤ σ')
    (hnτ₀ : ‖P τ₀‖ = 3 * C.r) (hnσ₀ : ‖P σ₀‖ = 3 * C.r)
    {ε : ℝ} (hε : 0 < ε) (hεep : ε ≤ (2 : ℝ) ^ (-(C.k0 : ℝ))) :
    Objects.CorrectedEvent.around D (P σ) (ε * C.r) (Real.sqrt ε * C.r) ≤ ENNReal.ofReal (ε ^ theta C * (σ₀ - σ)) := by
  have hr := C.rPos
  have hsq := sqrt_le_half_of_le_ep (C := C) hε.le hεep
  have hnσ := S.norm_σ
  set c := τ₀ + σ₀ with hc
  set Q : ℝ → ℂ := fun t => P (c - t) with hQ
  have hσlt : σ < σ₀ := lt_of_le_of_ne hσσ₀ (fun h => by rw [← h] at hnσ₀; linarith [hnσ.2])
  have hτ₀σ : τ₀ < σ := lt_of_le_of_ne (hτ₀τ.trans S.τ_le_σ)
    (fun h => by rw [h] at hnτ₀; linarith [hnσ.2])
  have has : τ₀ < c - σ := by rw [hc]; linarith
  have hsb : c - σ < σ₀ := by rw [hc]; linarith
  have hcont : ContinuousOn Q (Icc τ₀ σ₀) := by
    have h := S.cont_sub hτ₀ hσ₀
    have h' : ContinuousOn P (Icc (c - σ₀) (c - τ₀)) := by
      rw [hc]; simpa only [add_sub_cancel_right, add_sub_cancel_left] using h
    exact continuousOn_reflect h'
  have hfar : ∀ {t : ℝ}, ‖P t‖ = 3 * C.r → Real.sqrt ε * C.r ≤ dist (P t) (P σ) := by
    intro t ht
    have := half_le_dist_of_norms ht hnσ.2
    nlinarith
  have hQa : Q τ₀ = P σ₀ := by simp only [hQ, hc, add_sub_cancel_left]
  have hQb : Q σ₀ = P τ₀ := by simp only [hQ, hc, add_sub_cancel_right]
  have hQs : Q (c - σ) = P σ := by simp only [hQ, sub_sub_cancel]
  have h := c3_core C D Db f S.forget S.weyl S.f_bd hS3 hline4 hε hεep (protect_of_mid hnσ hsq)
    (P := Q) (s := c - σ) has hsb hcont ?_ ?_ (by rw [hQa]; exact hfar hnσ₀)
    (by rw [hQb]; exact hfar hnτ₀) (by rw [hQs, dist_self]; exact mul_nonneg hε.le hr.le)
  · have he : c - σ - τ₀ = σ₀ - σ := by rw [hc]; ring
    rwa [he] at h
  · intro u v hu huv hv
    simp only [hQ]
    rw [Db.isExtMetric.2.2.1 (P (c - u)) (P (c - v)),
      S.dist_eq (by rw [hc]; linarith) (by linarith) (by rw [hc]; linarith)]
    congr 1
    ring
  · intro u v hu huv hv
    have hσv : σ ≤ c - v := by rw [hc]; linarith
    have hu' : c - u ≤ σ' := by rw [hc]; linarith
    have hP : D.IsCurve P (c - v) (c - u) :=
      S.isCurve ((S.τ'_nonneg.trans (S.τ'_le_τ.trans S.τ_le_σ)).trans hσv) (by linarith)
        (hu'.trans S.σ'_le_L)
    refine ⟨isCurve_reflect hP, ?_⟩
    rw [len_reflect, S.len_eq_after hσv (by linarith) hu']
    exact le_of_eq (congrArg ENNReal.ofReal (by ring))

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
