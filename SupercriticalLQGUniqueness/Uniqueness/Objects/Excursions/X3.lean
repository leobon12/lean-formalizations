import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.X1




 














set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {D Db : LSCMetric} {f : C(ℂ, ℝ)}
  {V : TopologicalSpace.Opens ℂ} {P : ℝ → ℂ} {L τ' τ σ σ' : ℝ}

 

theorem loop_meets_net {π : ℂ → ℝ → ℂ} {ts us : ℂ → ℝ} {Ne : ℝ≥0∞}
    (net : NetData C T D Ne π ts us) {z : ℂ} (hz : 3 / 2 * C.r < ‖z‖ ∧ ‖z‖ < 5 / 2 * C.r)
    {ε : ℝ} (hε : 0 < ε) (hsq : Real.sqrt ε ≤ 1 / 2) (hεsq : ε ≤ Real.sqrt ε)
    (htube : ∀ x ∈ Objects.CorrectedEvent.tubeSet T, 3 / 2 * C.r < ‖x‖)
    {K : Set ℂ} (hK : LQGMetric.Disconnects K (sphere z (ε * C.r)) (sphere z (Real.sqrt ε * C.r)))
    {p : ℂ} (hp : p ∈ NetData.Γ π ts us T) (hpz : dist p z ≤ ε * C.r) :
    (K ∩ NetData.Γ π ts us T).Nonempty := by
  have hr := C.rPos
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith [hz.1]
  
  set w : ℂ := -((3 * C.r / ‖z‖ : ℝ) : ℂ) * z with hw
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hwn : ‖w‖ = 3 * C.r := by
    rw [hw, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    field_simp
  
  have hseg := net.barrier 0 w (Path.segment 0 w) (by simp; positivity)
    (by simp only [mem_compl_iff, mem_ball, dist_zero_right, hwn, not_lt]; linarith)
  obtain ⟨q, hqseg, hqΓ⟩ := hseg
  
  obtain ⟨t, rfl⟩ := hqseg
  have hqnorm : 3 / 2 * C.r < ‖Path.segment (0 : ℂ) w t‖ := by
    obtain ⟨x, hx, hqx⟩ := mem_iUnion₂.mp hqΓ
    exact htube _ (net.tube x hx hqx)
  have hseg_eq : Path.segment (0 : ℂ) w t = ((t : ℝ) : ℂ) * w := by
    simp [Path.segment, AffineMap.lineMap_apply]
  rw [hseg_eq] at hqnorm hqΓ
  have hqfar : Real.sqrt ε * C.r ≤ dist (((t : ℝ) : ℂ) * w) z := by
    
    have h1 : ((t : ℝ) : ℂ) * w - z = -(((t : ℝ) * (3 * C.r / ‖z‖) + 1 : ℝ) : ℂ) * z := by
      rw [hw]; push_cast; ring
    rw [dist_eq_norm, h1, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have hpos : 0 < (t : ℝ) * (3 * C.r / ‖z‖) + 1 := by positivity
    rw [abs_of_pos hpos]
    have : ‖z‖ ≤ ((t : ℝ) * (3 * C.r / ‖z‖) + 1) * ‖z‖ := by
      nlinarith [mul_nonneg ht0 (by positivity : (0 : ℝ) ≤ 3 * C.r / ‖z‖)]
    nlinarith
  
  obtain ⟨γ, hγ⟩ := (net.joined hp hqΓ)
  have hsep := LQGMetric.Disconnects.closedBall_compl_ball
    (mul_le_mul_of_nonneg_right hεsq hr.le) hK
  obtain ⟨m, hmγ, hmK⟩ := hsep p _ γ (mem_closedBall.mpr hpz)
    (by simpa only [mem_compl_iff, mem_ball, not_lt] using hqfar)
  obtain ⟨s, rfl⟩ := hmγ
  exact ⟨γ s, hmK, hγ s⟩


 

theorem two_set_le_ep (C : Objects.CorrectedEvent.Constants) (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1)
    (hlam : C.lamConst ≤ 1 / 48) : 2 * C.A_set ≤ (2 : ℝ) ^ (-(C.k0 : ℝ)) := by
  have hK1 : C.K_ann < 1 := Objects.Producer.kann_lt_one C
  have h1 : C.A_nar ≤ C.lamConst * C.ρ := by
    have := C.narLe
    have hρ := C.rhoPos
    have hl := C.lamPos
    have he := C.endptPos
    have : C.lamConst * (1 - C.K_ann) * C.A_endpt * C.ρ ≤ C.lamConst * C.ρ := by
      have h2 : (1 - C.K_ann) * C.A_endpt ≤ 1 := by nlinarith
      nlinarith [mul_pos hl hρ]
    linarith
  have h2 : C.lamConst * C.ρ ≤ C.lamConst * (C.lamConst * C.A_sp) :=
    mul_le_mul_of_nonneg_left C.rhoLt.le C.lamPos.le
  have h3 := C.spLtEp
  have hl := C.lamPos
  have hsp := C.spPos
  have h4 : C.lamConst * (C.lamConst * C.A_sp) ≤ C.A_sp / 4 := by
    have h5 : C.lamConst * C.A_sp ≤ C.A_sp / 48 := by nlinarith
    have h6 : C.lamConst * (C.lamConst * C.A_sp) ≤ C.lamConst * (C.A_sp / 48) :=
      mul_le_mul_of_nonneg_left h5 hl.le
    nlinarith
  linarith [C.setLtNar]

 
theorem x3_short (S : ExcSetting C D Db f V P L τ' τ σ σ') (hS3 : Objects.CorrectedEvent.S3 C D)
    (hline4 : C.c_reg⁻¹ ^ 2 * (1 + C.c_reg) ^ 3 * (2 : ℝ) ^ (2 * theta C) *
      ((2 : ℝ) ^ (-(C.k0 : ℝ))) ^ theta C ≤ 1)
    (hline8 : 4 * (2 * C.A_set) ^ theta C * C.A_around ≤
      C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)))
    (hmaxnar : Real.exp (-C.ξ * C.A_max) * C.A_internal ≤ C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)))
    (hsetep : 2 * C.A_set ≤ (2 : ℝ) ^ (-(C.k0 : ℝ)))
    {N : ℝ} (hN : 0 < N)
    (hS2 : Objects.CorrectedEvent.around D 0 (3 * C.r) (4 * C.r) ≤ ENNReal.ofReal C.A_around * ENNReal.ofReal N)
    {π : ℂ → ℝ → ℂ} {ts us : ℂ → ℝ} (net : NetData C T D (ENNReal.ofReal N) π ts us)
    (htube : ∀ x ∈ Objects.CorrectedEvent.tubeSet T, 3 / 2 * C.r < ‖x‖)
    (hfmax : ∀ x ∈ Objects.CorrectedEvent.tubeSet T, f x = C.A_max)
    (hVnear : ∀ y ∈ closure (V : Set ℂ), ∃ x ∈ closure (Objects.CorrectedEvent.tubeSet T), dist y x ≤ C.A_sup * C.r) :
    σ - τ < 3 * C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)) * N := by
  have hr := C.rPos
  have hAr : 0 < C.A_around := lt_trans one_pos C.aroundGtOne
  obtain ⟨τ₀, σ₀, hτ₀, hτ₀τ, hσσ₀, hσ₀, hnτ₀, hnσ₀, htime⟩ := x2a_times S hN hS2
  set ε := 2 * C.A_set with hεdef
  have hε : 0 < ε := by have := C.setPos; positivity
  have hsq := sqrt_le_half_of_le_ep (C := C) hε.le hsetep
  have hεsq : ε ≤ Real.sqrt ε := by
    have h1 : ε ≤ 1 := by
      have : (2 : ℝ) ^ (-(C.k0 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
      linarith
    calc ε = Real.sqrt ε * Real.sqrt ε := (Real.mul_self_sqrt hε.le).symm
      _ ≤ Real.sqrt ε * 1 := by
          gcongr
          rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
          exact Real.sqrt_le_sqrt h1
      _ = Real.sqrt ε := mul_one _
  set θ := theta C with hθ
  have hεθ : 0 < ε ^ θ := Real.rpow_pos_of_pos hε θ
  have hlτ := eloop_tau S hS3 hline4 hτ₀ hτ₀τ hσσ₀ hσ₀ hnτ₀ hnσ₀ hε hsetep
  have hlσ := eloop_sigma S hS3 hline4 hτ₀ hτ₀τ hσσ₀ hσ₀ hnτ₀ hnσ₀ hε hsetep
  set B : ℝ := 2 * ε ^ θ * C.A_around * N with hB
  have hBτ : Objects.CorrectedEvent.around D (P τ) (ε * C.r) (Real.sqrt ε * C.r) < ENNReal.ofReal B := by
    refine hlτ.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
    have : τ - τ₀ < 2 * C.A_around * N := by linarith [S.τ_le_σ]
    rw [hB]; nlinarith
  have hBσ : Objects.CorrectedEvent.around D (P σ) (ε * C.r) (Real.sqrt ε * C.r) < ENNReal.ofReal B := by
    refine hlσ.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_)
    have : σ₀ - σ < 2 * C.A_around * N := by linarith [S.τ_le_σ]
    rw [hB]; nlinarith
  obtain ⟨πτ, aτ, bτ, hπτ, hπτann, hπτsep, hπτlen⟩ := EndpointAttachment.exists_corrected_loop_lt D (P τ) _ _ hBτ
  obtain ⟨πσ, aσ, bσ, hπσ, hπσann, hπσsep, hπσlen⟩ := EndpointAttachment.exists_corrected_loop_lt D (P σ) _ _ hBσ
  
  have hnear : ∀ {z : ℂ}, z ∈ closure (V : Set ℂ) → ∃ p ∈ NetData.Γ π ts us T, dist p z ≤ ε * C.r := by
    intro z hz
    obtain ⟨y, hy, hzy⟩ := hVnear z hz
    obtain ⟨x, hx, p, hp, hyp⟩ := net.dense y hy
    refine ⟨p, NetData.mem_Γ hx hp, ?_⟩
    have htri := dist_triangle p y z
    rw [dist_comm p y, dist_comm y z] at htri
    have := C.supLtSet
    rw [hεdef]
    nlinarith
  obtain ⟨pτ, hpτΓ, hpτ⟩ := hnear S.τ_mem_cl
  obtain ⟨pσ, hpσΓ, hpσ⟩ := hnear S.σ_mem_cl
  obtain ⟨mτ, hmτK, hmτΓ⟩ := loop_meets_net net S.norm_τ hε hsq hεsq htube hπτsep hpτΓ hpτ
  obtain ⟨mσ, hmσK, hmσΓ⟩ := loop_meets_net net S.norm_σ hε hsq hεsq htube hπσsep hpσΓ hpσ
  
  have hfarτ : Real.sqrt ε * C.r ≤ dist (P τ') (P τ) := by
    rw [dist_eq_norm]
    have := norm_sub_norm_le (P τ') (P τ)
    rw [S.norm_τ'] at this
    nlinarith [S.norm_τ.2]
  have hfarσ : Real.sqrt ε * C.r ≤ dist (P σ') (P σ) := by
    rw [dist_eq_norm]
    have := norm_sub_norm_le (P σ') (P σ)
    rw [S.norm_σ'] at this
    nlinarith [S.norm_σ.2]
  have hρR : ε * C.r ≤ Real.sqrt ε * C.r := mul_le_mul_of_nonneg_right hεsq hr.le
  obtain ⟨a, ha, haK⟩ := exists_hit S.τ'_le_τ (S.cont_sub le_rfl (S.τ_le_σ.trans S.σ_le_σ'))
    (LQGMetric.Disconnects.closedBall_compl_ball hρR hπτsep).symm
    (by simpa only [mem_compl_iff, mem_ball, not_lt] using hfarτ)
    (by rw [mem_closedBall, dist_self]; positivity)
  obtain ⟨b, hb, hbK⟩ := exists_hit S.σ_le_σ' (S.cont_sub (S.τ'_le_τ.trans S.τ_le_σ) le_rfl)
    (LQGMetric.Disconnects.closedBall_compl_ball hρR hπσsep)
    (by rw [mem_closedBall, dist_self]; positivity)
    (by simpa only [mem_compl_iff, mem_ball, not_lt] using hfarσ)
  
  have hab : a ≤ b := ha.2.trans (S.τ_le_σ.trans hb.1)
  have hdist := S.dist_eq ha.1 hab hb.2
  obtain ⟨p₁, hp₁, hp₁e⟩ := haK
  obtain ⟨p₂, hp₂, hp₂e⟩ := hmτK
  obtain ⟨q₁, hq₁, hq₁e⟩ := hbK
  obtain ⟨q₂, hq₂, hq₂e⟩ := hmσK
  have h1 : Db (P a, mτ) ≤ D.len πτ aτ bτ := by
    rw [← hp₁e, ← hp₂e]; exact bumped_dist_le_len C D Db f S.forget S.weyl S.f_bd hπτ hp₁ hp₂
  have h3 : Db (mσ, P b) ≤ D.len πσ aσ bσ := by
    rw [← hq₁e, ← hq₂e]; exact bumped_dist_le_len C D Db f S.forget S.weyl S.f_bd hπσ hq₂ hq₁
  have h2 := net.cost_lt Db f S.forget S.weyl hfmax hmτΓ hmσΓ
  rw [← ENNReal.ofReal_mul (div_nonneg C.internalPos.le two_pos.le),
    ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h2
  have htri : Db (P a, P b) ≤ Db (P a, mτ) + Db (mτ, mσ) + Db (mσ, P b) :=
    (Db.isExtMetric.2.2.2 _ mσ _).trans (add_le_add (Db.isExtMetric.2.2.2 _ mτ _) le_rfl)
  set E : ℝ := Real.exp (-C.ξ * C.A_max) * (C.A_internal / 2 * N) with hE
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (div_nonneg C.internalPos.le two_pos.le) hN.le)
  have hsum : Db (P a, P b) < ENNReal.ofReal (B + E + B) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) hE0]
    calc Db (P a, P b) ≤ Db (P a, mτ) + Db (mτ, mσ) + Db (mσ, P b) := htri
      _ < ENNReal.ofReal B + ENNReal.ofReal E + ENNReal.ofReal B := by
          refine ENNReal.add_lt_add (ENNReal.add_lt_add (h1.trans_lt hπτlen) h2) (h3.trans_lt hπσlen)
  rw [hdist] at hsum
  have hlt := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hsum
  have hst : σ - τ ≤ b - a := by linarith [ha.2, hb.1]
  
  have hB4 : 2 * B ≤ C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)) * N := by
    have := mul_le_mul_of_nonneg_right hline8 hN.le
    rw [hB, hεdef]; nlinarith
  have hE2 : E ≤ C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)) * N / 2 := by
    have := mul_le_mul_of_nonneg_right hmaxnar hN.le
    rw [hE]; nlinarith
  have hpos : 0 < C.lamConst * C.A_nar ^ (C.ξ * (C.Q + 3)) * N := by
    have := C.lamPos; have := C.narPos
    have : 0 < C.A_nar ^ (C.ξ * (C.Q + 3)) := Real.rpow_pos_of_pos C.narPos _
    positivity
  linarith

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
