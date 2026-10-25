import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Loop




 














set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

variable {C : Objects.CorrectedEvent.Constants} {D Db : LSCMetric} {f : C(ℂ, ℝ)} {V : TopologicalSpace.Opens ℂ}
  {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ}

 
theorem internal_le_len_of_mem (D : LSCMetric) {Y : Set ℂ} {π : ℝ → ℂ} {a b p q : ℝ}
    (hπ : D.IsCurve π a b) (hY : ∀ t ∈ Icc a b, π t ∈ Y) (hp : p ∈ Icc a b) (hq : q ∈ Icc a b)
    (hpY : π p ∈ Y) (hqY : π q ∈ Y) :
    D.internal Y (⟨π p, hpY⟩, ⟨π q, hqY⟩) ≤ D.len π a b := by
  rcases le_total p q with hpq | hqp
  · have hc : D.IsCurve π p q := ⟨hpq, hπ.2.mono (Icc_subset_Icc hp.1 hq.2)⟩
    have h := BiLipschitz.Barrier.internal_le_len' D hc (fun t ht => hY t ⟨hp.1.trans ht.1, ht.2.trans hq.2⟩)
    exact h.trans (LQGMetric.MetricGeometry.curveLength_mono _ hp.1 hq.2)
  · have hc : D.IsCurve π q p := ⟨hqp, hπ.2.mono (Icc_subset_Icc hq.1 hp.2)⟩
    have h := BiLipschitz.Barrier.internal_le_len' D hc (fun t ht => hY t ⟨hq.1.trans ht.1, ht.2.trans hp.2⟩)
    rw [(LSCMetric.isExtMetric_internal D Y).2.2.1]
    exact h.trans (LQGMetric.MetricGeometry.curveLength_mono _ hq.1 hp.2)

 
theorem x2c_sep (S : ExcSetting C D Db f V P L τ' τ σ σ') (hS3 : Objects.CorrectedEvent.S3 C D)
    (hline4 : C.c_reg⁻¹ ^ 2 * (1 + C.c_reg) ^ 3 * (2 : ℝ) ^ (2 * theta C) *
      ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ theta C ≤ 1)
    (hline5 : 4 * C.A_sp ^ theta C * C.A_around < C.A_across ^ 2 / (16 * C.A_around))
    {N : ℝ} (hN : 0 < N)
    (hS2 : Objects.CorrectedEvent.around D 0 (3 * C.r) (4 * C.r) ≤ ENNReal.ofReal C.A_around * ENNReal.ofReal N)
    {Ctime : ℝ} (hCtime : C.A_across ^ 2 / (4 * C.A_around) ≤ Ctime)
    (hτ4 : P τ ∈ ball (0 : ℂ) (4 * C.r)) (hσ4 : P σ ∈ ball (0 : ℂ) (4 * C.r))
    (hint : ENNReal.ofReal Ctime * ENNReal.ofReal N ≤
      D.internal (ball (0 : ℂ) (4 * C.r)) (⟨P τ, hτ4⟩, ⟨P σ, hσ4⟩)) :
    C.A_sp * C.r ≤ dist (P τ) (P σ) := by
  by_contra hlt
  push Not at hlt
  have hr := C.rPos
  have hAr : 0 < C.A_around := lt_trans one_pos C.aroundGtOne
  have hAc := C.acrossPos
  obtain ⟨τ₀, σ₀, hτ₀, hτ₀τ, hσσ₀, hσ₀, hnτ₀, hnσ₀, htime⟩ := x2a_times S hN hS2
  have hsp := C.spPos
  have hspep : C.A_sp ≤ (2 : ℝ) ^ (-(C.k0 : ℝ)) := C.spLtEp.le
  have hloop := eloop_tau S hS3 hline4 hτ₀ hτ₀τ hσσ₀ hσ₀ hnτ₀ hnσ₀ hsp hspep
  set θ := theta C with hθ
  have hθpos : 0 < C.A_sp ^ θ := Real.rpow_pos_of_pos hsp θ
  set B : ℝ := 2 * C.A_sp ^ θ * C.A_around * N with hB
  have hτlt : τ - τ₀ < 2 * C.A_around * N := by linarith [S.τ_le_σ]
  have hB' : Objects.CorrectedEvent.around D (P τ) (C.A_sp * C.r) (Real.sqrt C.A_sp * C.r) < ENNReal.ofReal B := by
    refine hloop.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
    rw [hB]
    nlinarith
  obtain ⟨π, t₀, t₁, hπ, hπann, hπsep, hπlen⟩ := EndpointAttachment.exists_corrected_loop_lt D (P τ) _ _ hB'
  
  have hsq := sqrt_le_half_of_le_ep (C := C) hsp.le hspep
  have hspsq : C.A_sp ≤ Real.sqrt C.A_sp := by
    have h1 : C.A_sp ≤ 1 := by
      have := Real.sqrt_le_sqrt (le_refl C.A_sp)
      nlinarith [Real.sq_sqrt hsp.le, Real.sqrt_nonneg C.A_sp]
    calc C.A_sp = Real.sqrt C.A_sp * Real.sqrt C.A_sp := (Real.mul_self_sqrt hsp.le).symm
      _ ≤ Real.sqrt C.A_sp * 1 := by
          gcongr
          rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
          exact Real.sqrt_le_sqrt h1
      _ = Real.sqrt C.A_sp := mul_one _
  have hρR : C.A_sp * C.r ≤ Real.sqrt C.A_sp * C.r := mul_le_mul_of_nonneg_right hspsq hr.le
  have hRr : Real.sqrt C.A_sp * C.r ≤ C.r / 2 := by nlinarith
  have hnτ := S.norm_τ
  have hKc : IsClosed (π '' Icc t₀ t₁) := hπ.isClosed_image
  have hKann : π '' Icc t₀ t₁ ⊆ {x | C.A_sp * C.r < dist x (P τ) ∧ dist x (P τ) < Real.sqrt C.A_sp * C.r} :=
    hπann
  
  have hfar' : Real.sqrt C.A_sp * C.r ≤ dist (P τ') (P τ) := by
    rw [dist_eq_norm]
    have := norm_sub_norm_le (P τ') (P τ)
    rw [S.norm_τ'] at this
    linarith [hnτ.2]
  have hfarσ' : Real.sqrt C.A_sp * C.r ≤ dist (P σ') (P τ) := by
    rw [dist_eq_norm]
    have := norm_sub_norm_le (P σ') (P τ)
    rw [S.norm_σ'] at this
    linarith [hnτ.2]
  
  obtain ⟨τA, hτA, hτAτ, hτAK, hτAin⟩ := exists_last_hit S.τ'_le_τ
    (S.cont_sub le_rfl (S.τ_le_σ.trans S.σ_le_σ')) hρR hKc hπsep hKann hfar'
    (by rw [dist_self]; positivity)
  obtain ⟨σA, hσA, hσσA, hσAK, hσAin⟩ := exists_first_hit S.σ_le_σ'
    (S.cont_sub (S.τ'_le_τ.trans S.τ_le_σ) le_rfl) hρR hKc hπsep hKann
    (by rw [dist_comm]; exact hlt.le) hfarσ'
  
  obtain ⟨p, hp, hpe⟩ := hτAK
  obtain ⟨q, hq, hqe⟩ := hσAK
  have hτAσA : τA ≤ σA := hτA.2.trans (S.τ_le_σ.trans hσσA.le)
  have hdAB : Db (P τA, P σA) = ENNReal.ofReal (σA - τA) := S.dist_eq hτA.1 hτAσA hσA.2
  have hπb : Db (P τA, P σA) ≤ D.len π t₀ t₁ := by
    rw [← hpe, ← hqe]
    exact bumped_dist_le_len C D Db f S.forget S.weyl S.f_bd hπ hp hq
  have htAB : σA - τA < B := by
    have := (hdAB ▸ hπb).trans_lt hπlen
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp this
  
  have hin4 : ∀ {x : ℂ}, dist x (P τ) < Real.sqrt C.A_sp * C.r → x ∈ ball (0 : ℂ) (4 * C.r) := by
    intro x hx
    rw [mem_ball, dist_zero_right]
    have h := norm_le_norm_add_norm_sub' x (P τ)
    rw [← dist_eq_norm] at h
    linarith [hnτ.2]
  have hY1 : ∀ t ∈ Icc τA τ, P t ∈ ball (0 : ℂ) (4 * C.r) := fun t ht => hin4 (hτAin t ht)
  have hY3 : ∀ t ∈ Icc σ σA, P t ∈ ball (0 : ℂ) (4 * C.r) := fun t ht => hin4 (hσAin t ht)
  have hYπ : ∀ t ∈ Icc t₀ t₁, π t ∈ ball (0 : ℂ) (4 * C.r) :=
    fun t ht => hin4 (hπann ⟨t, ht, rfl⟩).2
  have hτAY : P τA ∈ ball (0 : ℂ) (4 * C.r) := hY1 τA ⟨le_rfl, hτA.2⟩
  have hσAY : P σA ∈ ball (0 : ℂ) (4 * C.r) := hY3 σA ⟨hσσA.le, le_rfl⟩
  
  set Y := ball (0 : ℂ) (4 * C.r) with hYdef
  have hd1 : D.internal Y (⟨P τ, hτ4⟩, ⟨P τA, hτAY⟩) ≤ ENNReal.ofReal (τ - τA) := by
    have hc : D.IsCurve P τA τ := S.isCurve (S.τ'_nonneg.trans hτA.1) hτA.2
      (S.τ_le_σ.trans (S.σ_le_σ'.trans S.σ'_le_L))
    rw [(LSCMetric.isExtMetric_internal D Y).2.2.1]
    have h := BiLipschitz.Barrier.internal_le_len' D hc hY1
    exact h.trans (S.len_eq_before hτA.1 hτA.2 le_rfl).le
  have hd2 : D.internal Y (⟨P τA, hτAY⟩, ⟨P σA, hσAY⟩) ≤ D.len π t₀ t₁ := by
    have hpY : π p ∈ Y := hYπ p hp
    have hqY : π q ∈ Y := hYπ q hq
    have h := internal_le_len_of_mem D hπ hYπ hp hq hpY hqY
    have hx : (⟨P τA, hτAY⟩ : Y) = ⟨π p, hpY⟩ := Subtype.ext hpe.symm
    have hy : (⟨P σA, hσAY⟩ : Y) = ⟨π q, hqY⟩ := Subtype.ext hqe.symm
    rw [hx, hy]
    exact h
  have hd3 : D.internal Y (⟨P σA, hσAY⟩, ⟨P σ, hσ4⟩) ≤ ENNReal.ofReal (σA - σ) := by
    have hc : D.IsCurve P σ σA :=
      S.isCurve ((S.τ'_nonneg.trans (S.τ'_le_τ.trans S.τ_le_σ))) hσσA.le (hσA.2.trans S.σ'_le_L)
    rw [(LSCMetric.isExtMetric_internal D Y).2.2.1]
    have h := BiLipschitz.Barrier.internal_le_len' D hc hY3
    exact h.trans (S.len_eq_after le_rfl hσσA.le hσA.2).le
  have htri := (LSCMetric.isExtMetric_internal D Y).2.2.2
  have hsum : D.internal Y (⟨P τ, hτ4⟩, ⟨P σ, hσ4⟩) < ENNReal.ofReal (2 * B) := by
    calc D.internal Y (⟨P τ, hτ4⟩, ⟨P σ, hσ4⟩)
        ≤ D.internal Y (⟨P τ, hτ4⟩, ⟨P τA, hτAY⟩) + D.internal Y (⟨P τA, hτAY⟩, ⟨P σ, hσ4⟩) :=
          htri _ _ _
      _ ≤ D.internal Y (⟨P τ, hτ4⟩, ⟨P τA, hτAY⟩) + (D.internal Y (⟨P τA, hτAY⟩, ⟨P σA, hσAY⟩) +
            D.internal Y (⟨P σA, hσAY⟩, ⟨P σ, hσ4⟩)) := by gcongr; exact htri _ _ _
      _ ≤ ENNReal.ofReal (τ - τA) + (D.len π t₀ t₁ + ENNReal.ofReal (σA - σ)) := by
          gcongr
      _ < ENNReal.ofReal (τ - τA) + (ENNReal.ofReal B + ENNReal.ofReal (σA - σ)) :=
          ENNReal.add_lt_add_left ENNReal.ofReal_ne_top
            (ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hπlen)
      _ = ENNReal.ofReal ((τ - τA) + B + (σA - σ)) := by
          rw [ENNReal.ofReal_add (by linarith [hτA.2]) (by positivity),
            ENNReal.ofReal_add (by linarith [hτA.2, hθpos]) (by linarith [hσσA]), add_assoc]
      _ ≤ ENNReal.ofReal (2 * B) := ENNReal.ofReal_le_ofReal (by linarith [S.τ_le_σ])
  
  have h2B : 2 * B < Ctime * N := by
    have h1 : 2 * B = (4 * C.A_sp ^ θ * C.A_around) * N := by rw [hB]; ring
    have h2 : C.A_across ^ 2 / (16 * C.A_around) < C.A_across ^ 2 / (4 * C.A_around) := by
      apply div_lt_div_of_pos_left (by positivity) (by positivity) (by linarith)
    rw [h1]
    have := mul_lt_mul_of_pos_right (hline5.trans (h2.trans_le hCtime)) hN
    linarith
  have hCt0 : 0 ≤ Ctime := le_trans (by positivity) hCtime
  have hfinal : ENNReal.ofReal (2 * B) < ENNReal.ofReal Ctime * ENNReal.ofReal N := by
    rw [← ENNReal.ofReal_mul hCt0]
    exact (ENNReal.ofReal_lt_ofReal_iff (by nlinarith)).mpr h2B
  exact absurd (hint.trans_lt (hsum.trans hfinal)) (lt_irrefl _)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
