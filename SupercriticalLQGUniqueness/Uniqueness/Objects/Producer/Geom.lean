import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.C8




 

















set_option autoImplicit false

noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem blockBall_subset_ann (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1) (hρ : C.ρ < 1 / 64) (k : Fin T.K) :
    closedBall (Objects.CorrectedEvent.innerCenter T k) T.blockRadius ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) ∧
      closedBall (Objects.CorrectedEvent.outerCenter T k) T.blockRadius ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := by
  obtain ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩ := blockCentre_bounds C T hData hK k
  obtain ⟨-, hR⟩ := blockRadius_bounds C T hData hE
  have hr := C.rPos
  have hρr : C.ρ * C.r < C.r / 64 := by
    have := mul_lt_mul_of_pos_right hρ hr
    linarith only [this]
  have key : ∀ c : ℂ, 2 * C.r - C.ρ * C.r ≤ ‖c‖ → ‖c‖ ≤ 2 * C.r + C.ρ * C.r →
      closedBall c T.blockRadius ⊆ Objects.CorrectedEvent.ann 0 C.r (4 * C.r) := by
    intro c h1 h2 x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have hx1 := norm_sub_norm_le c x
    rw [norm_sub_rev] at hx1
    have hx2 := norm_le_insert' x c
    show C.r < dist x 0 ∧ dist x 0 < 4 * C.r
    rw [dist_zero_right]
    constructor <;> linarith only [h1, h2, hx, hx1, hx2, hR, hρr, hr]
  exact ⟨key _ hu1 hu2, key _ hv1 hv2⟩

 
theorem blockNbhd_subset_midAnn (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (hE : C.A_endpt ≤ 1) (hsmall : 2 * C.ρ + C.A_sup + 3 * C.A_nar ≤ 1 / 2)
    (k : Fin T.K) :
    ball (Objects.CorrectedEvent.innerCenter T k) (T.blockRadius + C.A_sup * C.r + 3 * C.A_nar * C.r) ⊆
        Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) ∧
      ball (Objects.CorrectedEvent.outerCenter T k) (T.blockRadius + C.A_sup * C.r + 3 * C.A_nar * C.r) ⊆
        Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := by
  obtain ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩ := blockCentre_bounds C T hData hK k
  obtain ⟨-, hR⟩ := blockRadius_bounds C T hData hE
  have hr := C.rPos
  have hs : (2 * C.ρ + C.A_sup + 3 * C.A_nar) * C.r ≤ 1 / 2 * C.r :=
    mul_le_mul_of_nonneg_right hsmall hr.le
  have key : ∀ c : ℂ, 2 * C.r - C.ρ * C.r ≤ ‖c‖ → ‖c‖ ≤ 2 * C.r + C.ρ * C.r →
      ball c (T.blockRadius + C.A_sup * C.r + 3 * C.A_nar * C.r) ⊆
        Objects.CorrectedEvent.ann 0 (1.5 * C.r) (3 * C.r) := by
    intro c h1 h2 x hx
    rw [mem_ball, dist_eq_norm] at hx
    have hx1 := norm_sub_norm_le c x
    rw [norm_sub_rev] at hx1
    have hx2 := norm_le_insert' x c
    show 1.5 * C.r < dist x 0 ∧ dist x 0 < 3 * C.r
    rw [dist_zero_right]
    constructor <;> linarith only [h1, h2, hx, hx1, hx2, hR, hs, hr]
  exact ⟨key _ hu1 hu2, key _ hv1 hv2⟩

 
theorem centres_far (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (k : Fin T.K) :
    C.ρ * C.r * (1 - C.K_ann) ≤ dist (Objects.CorrectedEvent.innerCenter T k) (Objects.CorrectedEvent.outerCenter T k) := by
  obtain ⟨hTr, hTrho, -, -, hTalpha, -, horient, -⟩ := hData
  have ho := norm_orientation horient
  have hpos : 0 < C.ρ * C.r := mul_pos C.rhoPos C.rPos
  have hdiff : Objects.CorrectedEvent.innerCenter T k - Objects.CorrectedEvent.outerCenter T k =
      ((T.rho * T.r : ℝ) : ℂ) * T.orientation * (Objects.CorrectedEvent.uNorm T - Objects.CorrectedEvent.vNorm T) := by
    simp only [Objects.CorrectedEvent.innerCenter, Objects.CorrectedEvent.outerCenter, Objects.CorrectedEvent.moduleMap]
    ring
  have hu : ‖Objects.CorrectedEvent.uNorm T‖ = C.K_ann := by
    rw [Objects.CorrectedEvent.uNorm, norm_polar, hTalpha, abs_of_nonneg hK]
  have hv : ‖Objects.CorrectedEvent.vNorm T‖ = 1 := by
    rw [Objects.CorrectedEvent.vNorm, norm_polar, abs_one]
  have h1 : 1 - C.K_ann ≤ ‖Objects.CorrectedEvent.uNorm T - Objects.CorrectedEvent.vNorm T‖ := by
    have := norm_sub_norm_le (Objects.CorrectedEvent.vNorm T) (Objects.CorrectedEvent.uNorm T)
    rw [norm_sub_rev (Objects.CorrectedEvent.vNorm T)] at this
    linarith only [this, hu, hv]
  rw [dist_eq_norm, hdiff, norm_mul, norm_mul, Complex.norm_real, ho, mul_one, Real.norm_eq_abs,
    hTrho, hTr, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left h1 hpos.le

 
theorem blockNbhd_sep (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann)
    (hsmall : 2 * Real.sqrt C.A_endpt * C.ρ + 2 * C.A_sup + 3 * C.A_nar ≤ C.ρ * (1 - C.K_ann))
    (k : Fin T.K) :
    ∀ x ∈ ball (Objects.CorrectedEvent.innerCenter T k) (T.blockRadius + (C.A_sup + C.A_nar) * C.r),
    ∀ y ∈ ball (Objects.CorrectedEvent.outerCenter T k) (T.blockRadius + (C.A_sup + C.A_nar) * C.r),
      C.A_nar * C.r ≤ dist x y := by
  intro x hx y hy
  have hfar := centres_far C T hData hK k
  have hR : T.blockRadius ≤ Real.sqrt C.A_endpt * C.ρ * C.r := hData.2.2.2.2.2.2.2.2.2.2.1
  have hr := C.rPos
  have hs : (2 * Real.sqrt C.A_endpt * C.ρ + 2 * C.A_sup + 3 * C.A_nar) * C.r ≤
      C.ρ * (1 - C.K_ann) * C.r := mul_le_mul_of_nonneg_right hsmall hr.le
  have htri := dist_triangle4 (Objects.CorrectedEvent.innerCenter T k) x y (Objects.CorrectedEvent.outerCenter T k)
  rw [mem_ball] at hx hy
  rw [dist_comm] at hx
  linarith only [hfar, hR, hs, htri, hx, hy]

 
theorem ball_subset_tubeSet (T : Objects.CorrectedEvent.TubeData) (k : Fin T.K) :
    ball (Objects.CorrectedEvent.innerCenter T k) T.blockRadius ⊆ Objects.CorrectedEvent.tubeSet T ∧
      ball (Objects.CorrectedEvent.outerCenter T k) T.blockRadius ⊆ Objects.CorrectedEvent.tubeSet T :=
  ⟨fun _ hx => mem_iUnion.2 ⟨k, Or.inl (Or.inl (Or.inr hx))⟩,
    fun _ hx => mem_iUnion.2 ⟨k, Or.inl (Or.inr hx)⟩⟩

 

 
theorem nar_le_endpt (C : Objects.CorrectedEvent.Constants) (hK : 0 ≤ C.K_ann) (hlam : C.lamConst ≤ 1 / 48) :
    C.A_nar ≤ C.A_endpt * C.ρ / 48 := by
  have hK1 := kann_lt_one C
  have hp : 0 ≤ C.A_endpt * C.ρ := mul_nonneg C.endptPos.le C.rhoPos.le
  have h1 : C.lamConst * (1 - C.K_ann) ≤ 1 / 48 := by
    calc C.lamConst * (1 - C.K_ann) ≤ C.lamConst * 1 :=
          mul_le_mul_of_nonneg_left (by linarith only [hK]) C.lamPos.le
      _ ≤ 1 / 48 := by linarith only [hlam]
  calc C.A_nar ≤ C.lamConst * (1 - C.K_ann) * C.A_endpt * C.ρ := C.narLe
    _ = C.lamConst * (1 - C.K_ann) * (C.A_endpt * C.ρ) := by ring
    _ ≤ 1 / 48 * (C.A_endpt * C.ρ) := mul_le_mul_of_nonneg_right h1 hp
    _ = C.A_endpt * C.ρ / 48 := by ring

 
theorem sup_le_blockRadius (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (hlam : C.lamConst ≤ 1 / 48) : C.A_sup * C.r ≤ T.blockRadius := by
  have h1 := nar_le_endpt C hK hlam
  have hlo : C.A_endpt * C.ρ * C.r ≤ T.blockRadius := hData.2.2.2.2.2.2.2.2.2.1
  have hp : 0 ≤ C.A_endpt * C.ρ := mul_nonneg C.endptPos.le C.rhoPos.le
  have h2 : C.A_sup ≤ C.A_endpt * C.ρ := by
    linarith only [C.supLtSet, C.setLtNar, h1, hp]
  calc C.A_sup * C.r ≤ C.A_endpt * C.ρ * C.r := mul_le_mul_of_nonneg_right h2 C.rPos.le
    _ ≤ T.blockRadius := hlo

 
theorem nar_le_blockRadius (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hData : Objects.CorrectedEvent.DataMatch C T)
    (hK : 0 ≤ C.K_ann) (hlam : C.lamConst ≤ 1 / 48) : 3 * C.A_nar * C.r ≤ T.blockRadius / 2 := by
  have h1 := nar_le_endpt C hK hlam
  have hlo : C.A_endpt * C.ρ * C.r ≤ T.blockRadius := hData.2.2.2.2.2.2.2.2.2.1
  have hp : 0 ≤ C.A_endpt * C.ρ := mul_nonneg C.endptPos.le C.rhoPos.le
  have h2 : 6 * C.A_nar ≤ C.A_endpt * C.ρ := by linarith only [h1, hp]
  have h3 : 6 * C.A_nar * C.r ≤ C.A_endpt * C.ρ * C.r := mul_le_mul_of_nonneg_right h2 C.rPos.le
  linarith only [h3, hlo]

 
theorem mid_small_of_constants (C : Objects.CorrectedEvent.Constants) (hK : 0 ≤ C.K_ann) (hlam : C.lamConst ≤ 1 / 48)
    (hE : C.A_endpt ≤ 1) (hρ : C.ρ < 1 / 64) : 2 * C.ρ + C.A_sup + 3 * C.A_nar ≤ 1 / 2 := by
  have h1 := nar_le_endpt C hK hlam
  have h2 : C.A_endpt * C.ρ ≤ C.ρ := by
    have := mul_le_mul_of_nonneg_right hE C.rhoPos.le
    linarith only [this]
  linarith only [h1, h2, hρ, C.supLe]

 
theorem nar_lt_one (C : Objects.CorrectedEvent.Constants) : C.A_nar < 1 := by
  linarith only [C.narLeQ]

 
theorem rho_lt_of_constants (C : Objects.CorrectedEvent.Constants) (hlam : C.lamConst ≤ 1 / 48) : C.ρ < 1 / 64 := by
  have h2 : (2 : ℝ) ^ (-(C.k0 : ℝ)) ≤ 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
    refine inv_anti₀ (by norm_num) ?_
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ C.k0 := pow_le_pow_right₀ (by norm_num) (le_trans (by norm_num) C.k0Large)
  have hsp : C.A_sp ≤ 1 / 2 := le_trans C.spLtEp.le h2
  have h4 : C.lamConst * C.A_sp ≤ C.lamConst * (1 / 2) := mul_le_mul_of_nonneg_left hsp C.lamPos.le
  linarith only [C.rhoLt, h4, hlam]

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
