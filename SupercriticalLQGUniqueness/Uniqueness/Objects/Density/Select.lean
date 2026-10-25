import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Table
import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Eventually




 





















set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Density

variable {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}

 

 

structure T58Budgets (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ) where
   
  reg : ℝ → Prop
   
  block : T58Stage1 ξ Q cm cp Kann p0 pbar → ℕ → Prop
   
  shield : T58Stage1 ξ Q cm cp Kann p0 pbar → ℕ → ℕ → Prop
   
  across : T58Stage2 ξ Q cm cp Kann p0 pbar → ℝ → Prop
   
  around : T58Stage2 ξ Q cm cp Kann p0 pbar → ℝ → Prop
   
  regCount : T58Stage2 ξ Q cm cp Kann p0 pbar → ℕ → Prop
   

  event : T58Stage5 ξ Q cm cp Kann p0 pbar → ℝ → Prop
   
  narrow : T58Stage6 ξ Q cm cp Kann p0 pbar → ℝ → Prop
   
  network : T58Stage8 ξ Q cm cp Kann p0 pbar → ℝ → Prop
   
  sup : T58Stage10 ξ Q cm cp Kann p0 pbar → ℝ → Prop
   
  energy : T58Stage10 ξ Q cm cp Kann p0 pbar → ℝ → ℝ → Prop

 
structure T58Budgets.Eventually (B : T58Budgets ξ Q cm cp Kann p0 pbar) : Prop where
  reg : ∀ᶠ c in 𝓝[>] (0 : ℝ), B.reg c
  block : ∀ s, ∀ᶠ m in atTop, B.block s m
  shield : ∀ s m, ∀ᶠ k in atTop, B.shield s m k
  across : ∀ s, ∀ᶠ a in 𝓝[>] (0 : ℝ), B.across s a
  around : ∀ s, ∀ᶠ b in atTop, B.around s b
  regCount : ∀ s, ∀ᶠ k in atTop, B.regCount s k
  event : ∀ s, ∀ᶠ x in 𝓝[>] (0 : ℝ), B.event s x
  narrow : ∀ s, ∀ᶠ x in 𝓝[>] (0 : ℝ), B.narrow s x
  network : ∀ s, ∀ᶠ y in atTop, B.network s y
  sup : ∀ s, ∀ᶠ x in 𝓝[>] (0 : ℝ), B.sup s x
  energy : ∀ s x, ∀ᶠ E in atTop, B.energy s x E

 
def T58Table.Satisfies (t : T58Table ξ Q cm cp Kann p0 pbar)
    (B : T58Budgets ξ Q cm cp Kann p0 pbar) : Prop :=
  B.reg t.c_reg ∧ B.block t.toT58Stage1 t.m ∧ B.shield t.toT58Stage1 t.m t.K_sh ∧
    B.across t.toT58Stage2 t.A_across ∧ B.around t.toT58Stage2 t.A_around ∧
    B.regCount t.toT58Stage2 t.k0 ∧ B.event t.toT58Stage5 t.ρ ∧
    B.narrow t.toT58Stage6 t.A_nar ∧ B.network t.toT58Stage8 t.A_internal ∧
    B.sup t.toT58Stage10 t.A_sup ∧ B.energy t.toT58Stage10 t.A_sup t.E_max

 

 

theorem exists_stage1 (hQ : 0 < Q) (hcm : 0 < cm) (hcmp : cm < cp) (hK1 : 3 / 4 < Kann)
    (hK2 : Kann < 1) (hp1 : 0 < p0) (hp2 : p0 < 1) (hb1 : 0 < pbar) (hb2 : pbar < 1)
    {R : ℝ → Prop} (hR : ∀ᶠ c in 𝓝[>] (0 : ℝ), R c) :
    ∃ s : T58Stage1 ξ Q cm cp Kann p0 pbar, R s.c_reg := by
  obtain ⟨c, hRc, hc0, hc1⟩ := (hR.and (ev_pos.and (ev_lt one_pos))).exists
  have hcp : 0 < cp := hcm.trans hcmp
  set M : ℝ := min cm (min cp⁻¹ ((cm / cp) ^ 2)) with hM
  have hMpos : 0 < M := lt_min hcm (lt_min (inv_pos.2 hcp) (pow_pos (div_pos hcm hcp) 2))
  have h10 : 0 < (10 : ℝ) ^ (-(100 : ℤ)) := zpow_pos (by norm_num) _
  set C := Cmid cm cp with hC
  set C0 := Cmid0 cm cp with hC0
  have hC0pos : 0 < C0 := Cmid0_pos hcm hcmp
  have hC0C : C0 < C := Cmid0_lt_Cmid hcmp
  set a₁ : ℝ := (10 : ℝ) ^ (-(100 : ℤ)) * M with ha₁
  set a₂ : ℝ := 1 / (20 * cp) with ha₂
  set a₃ : ℝ := (C - C0) / (10 * cp * (C + C0)) with ha₃
  have ha₁p : 0 < a₁ := mul_pos h10 hMpos
  have ha₂p : 0 < a₂ := by positivity
  have hCC0 : 0 < C + C0 := by linarith
  have ha₃p : 0 < a₃ := div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hcp) hCC0)
  set lam : ℝ := min a₁ (min a₂ a₃) / 2 with hlam
  have hmin : 0 < min a₁ (min a₂ a₃) := lt_min ha₁p (lt_min ha₂p ha₃p)
  have hlam0 : 0 < lam := by positivity
  have hl1 : lam < a₁ := by
    have := min_le_left a₁ (min a₂ a₃); linarith
  have hl2 : lam < a₂ := by
    have := le_trans (min_le_right a₁ (min a₂ a₃)) (min_le_left a₂ a₃); linarith
  have hl3 : lam ≤ a₃ := by
    have := le_trans (min_le_right a₁ (min a₂ a₃)) (min_le_right a₂ a₃); linarith
  have hx : 10 * cp * lam < 1 := by
    have : 10 * cp * lam < 10 * cp * a₂ := mul_lt_mul_of_pos_left hl2 (by positivity)
    have e : 10 * cp * a₂ = 1 / 2 := by rw [ha₂]; field_simp; ring
    linarith
  have hratio : (1 + 10 * cp * lam) / (1 - 10 * cp * lam) * C0 ≤ C := by
    have hpos : 0 < 1 - 10 * cp * lam := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    
    have hx3 : 10 * cp * lam * (C + C0) ≤ C - C0 := by
      have h1 : 10 * cp * lam ≤ 10 * cp * a₃ := mul_le_mul_of_nonneg_left hl3 (by positivity)
      have h2 : 10 * cp * a₃ * (C + C0) = C - C0 := by
        rw [ha₃]
        field_simp [hcp.ne', hCC0.ne']
      have h3 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ C + C0 by linarith)
      linarith
    nlinarith
  exact ⟨{
    Q_pos := hQ, cm_pos := hcm, cm_lt_cp := hcmp, Kann_gt := hK1, Kann_lt := hK2,
    p0_pos := hp1, p0_lt := hp2, pbar_pos := hb1, pbar_lt := hb2, c_reg := c, c_reg_pos := hc0,
    c_reg_lt := hc1, lam := lam, lam_pos := hlam0, lam_small := hl1, lam_ratio_pos := hx,
    lam_ratio := hratio }, hRc⟩

 
theorem exists_stage2 (s : T58Stage1 ξ Q cm cp Kann p0 pbar) {Bm : ℕ → Prop}
    (hBm : ∀ᶠ m in atTop, Bm m) {Bk : ℕ → ℕ → Prop} (hBk : ∀ m, ∀ᶠ k in atTop, Bk m k) :
    ∃ s' : T58Stage2 ξ Q cm cp Kann p0 pbar, s'.toT58Stage1 = s ∧ Bm s'.m ∧ Bk s'.m s'.K_sh := by
  have hK : 0 < 1 - Kann := by linarith [s.Kann_lt]
  have hev : ∀ᶠ m in atTop, Bm m ∧ 1 ≤ m ∧ endptScale m < s.lam * (1 - Kann) ^ 2 ∧
      endptScale m < (1 - Kann) ^ 4 / 4 ∧ endptScale m < ((1 - Kann) / 8) ^ 2 := by
    filter_upwards [hBm, ev_nat_ge 1,
      ev_pow_lt (r := 1 / 16) (by norm_num) (by norm_num) (mul_pos s.lam_pos (pow_pos hK 2)),
      ev_pow_lt (r := 1 / 16) (by norm_num) (by norm_num) (show 0 < (1 - Kann) ^ 4 / 4 by positivity),
      ev_pow_lt (r := 1 / 16) (by norm_num) (by norm_num) (show 0 < ((1 - Kann) / 8) ^ 2 by positivity)]
      with m h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨m, hm, hm1, ha, hb, hc⟩ := hev.exists
  have hc' : 4 * Real.sqrt (endptScale m) ≤ (1 - Kann) / 2 := by
    have h1 : Real.sqrt (endptScale m) ≤ Real.sqrt (((1 - Kann) / 8) ^ 2) :=
      Real.sqrt_le_sqrt hc.le
    rw [Real.sqrt_sq (by positivity)] at h1
    linarith
  obtain ⟨k, hk, hk1⟩ := ((hBk m).and (ev_nat_ge 1)).exists
  exact ⟨{
    toT58Stage1 := s, m := m, m_pos := hm1, endpt_a := ha.le, endpt_b := hb.le,
    endpt_c := hc', K_sh := k, K_sh_pos := hk1 }, rfl, hm, hk⟩

theorem epScale_eq_pow (k : ℕ) : epScale k = (1 / 2 : ℝ) ^ k := by
  rw [epScale, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div, inv_pow]

 

theorem exists_stage4 (s : T58Stage2 ξ Q cm cp Kann p0 pbar) {Ba : ℝ → Prop}
    (hBa : ∀ᶠ a in 𝓝[>] (0 : ℝ), Ba a) {Bb : ℝ → Prop} (hBb : ∀ᶠ b in atTop, Bb b)
    {Bk : ℕ → Prop} (hBk : ∀ᶠ k in atTop, Bk k) :
    ∃ s' : T58Stage4 ξ Q cm cp Kann p0 pbar, s'.toT58Stage2 = s ∧ Ba s'.A_across ∧
      Bb s'.A_around ∧ Bk s'.k0 := by
  obtain ⟨a, ha, ha0, ha1⟩ := (hBa.and (ev_pos.and (ev_lt one_pos))).exists
  obtain ⟨b, hb, hb1, hb2⟩ := (hBb.and ((ev_atTop_gt 1).and (ev_atTop_gt a⁻¹))).exists
  have hb0 : 0 < b := by linarith
  have hθ : 0 < regExp s.c_reg := regExp_pos s.c_reg_pos
  set L : ℝ := (s.c_reg ^ 2)⁻¹ * (1 + s.c_reg) ^ 3 * (2 : ℝ) ^ (2 * regExp s.c_reg) with hL
  have hLpos : 0 < L := by
    have := s.c_reg_pos
    have : 0 < (2 : ℝ) ^ (2 * regExp s.c_reg) := Real.rpow_pos_of_pos two_pos _
    positivity
  have hev : ∀ᶠ k : ℕ in atTop, Bk k ∧ 48 ≤ k ∧ ((1 / 2 : ℝ) ^ k) ^ regExp s.c_reg < L⁻¹ ∧
      (1 / 2 : ℝ) ^ k < b⁻¹ ∧ (1 / 2 : ℝ) ^ k < 1 / 4 := by
    filter_upwards [hBk, ev_nat_ge 48,
      ev_pow_rpow_lt (r := 1 / 2) (by norm_num) (by norm_num) hθ (inv_pos.2 hLpos),
      ev_pow_lt (r := 1 / 2) (by norm_num) (by norm_num) (inv_pos.2 hb0),
      ev_pow_lt (r := 1 / 2) (by norm_num) (by norm_num) (show (0 : ℝ) < 1 / 4 by norm_num)]
      with k h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨k, hk, hk48, hkreg, hkb, hk4⟩ := hev.exists
  have hreg : (s.c_reg ^ 2)⁻¹ * (1 + s.c_reg) ^ 3 * (2 : ℝ) ^ (2 * regExp s.c_reg) *
      epScale k ^ regExp s.c_reg ≤ 1 := by
    rw [epScale_eq_pow, ← hL]
    have := mul_lt_mul_of_pos_left hkreg hLpos
    rw [mul_inv_cancel₀ hLpos.ne'] at this
    exact this.le
  exact ⟨{
    toT58Stage2 := s, A_across := a, across_pos := ha0, across_lt := ha1, A_around := b,
    around_gt := hb1, around_gt_inv := hb2, k0 := k, k0_ge := hk48, reg_ep := hreg,
    ep_lt_around := by rw [epScale_eq_pow]; exact hkb,
    ep_lt_quarter := by rw [epScale_eq_pow]; exact hk4 }, rfl, ha, hb, hk⟩

 
theorem exists_stage5 (s : T58Stage4 ξ Q cm cp Kann p0 pbar) :
    ∃ s' : T58Stage5 ξ Q cm cp Kann p0 pbar, s'.toT58Stage4 = s := by
  have hθ : 0 < regExp s.c_reg := regExp_pos s.c_reg_pos
  have hb0 : 0 < s.A_around := by linarith [s.around_gt]
  have hc : 0 < s.A_across ^ 2 / (16 * s.A_around) := by have := s.across_pos; positivity
  obtain ⟨x, hx0, hx1, hx2⟩ := (ev_pos.and ((ev_lt (epScale_pos s.k0)).and
    (ev_mul_rpow_lt hθ (show 0 < 4 * s.A_around by positivity) hc))).exists
  refine ⟨{
    toT58Stage4 := s, A_sp := x, sp_pos := hx0, sp_lt := hx1, sp_loop := ?_ }, rfl⟩
  calc 4 * x ^ regExp s.c_reg * s.A_around = 4 * s.A_around * x ^ regExp s.c_reg := by ring
    _ < s.A_across ^ 2 / (16 * s.A_around) := hx2

 

theorem exists_stage6 (s : T58Stage5 ξ Q cm cp Kann p0 pbar) {Be : ℝ → Prop}
    (hBe : ∀ᶠ x in 𝓝[>] (0 : ℝ), Be x) :
    ∃ s' : T58Stage6 ξ Q cm cp Kann p0 pbar, s'.toT58Stage5 = s ∧ Be s'.ρ := by
  have hθ : 0 < regExp s.c_reg := regExp_pos s.c_reg_pos
  have hb0 : 0 < s.A_around := by linarith [s.around_gt]
  have hA : 0 < locScale s.K_sh := locScale_pos s.K_sh
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), Be x ∧ 0 < x ∧ x < s.lam * s.A_sp ∧
      s.A_around * x ^ regExp s.c_reg < s.lam * s.A_across ∧ x < 1 / (3 * locScale s.K_sh) ∧
      x ≤ s.lam / locScale s.K_sh ∧ x < 1 / 64 ∧ x < 1 / 204 ∧
      x ≤ 10 * s.lam ^ 2 / (Real.pi ^ 2 * locScale s.K_sh ^ 2) := by
    have := s.lam_pos; have := s.sp_pos; have := s.across_pos
    filter_upwards [hBe, ev_pos, ev_lt (show 0 < s.lam * s.A_sp by positivity),
      ev_mul_rpow_lt hθ hb0 (show 0 < s.lam * s.A_across by positivity),
      ev_lt (show 0 < 1 / (3 * locScale s.K_sh) by positivity),
      ev_le (show 0 < s.lam / locScale s.K_sh by positivity),
      ev_lt (show (0 : ℝ) < 1 / 64 by norm_num), ev_lt (show (0 : ℝ) < 1 / 204 by norm_num),
      ev_le (show 0 < 10 * s.lam ^ 2 / (Real.pi ^ 2 * locScale s.K_sh ^ 2) by positivity)]
      with x h1 h2 h3 h4 h5 h6 h7 h8 h9
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  obtain ⟨x, hx, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7⟩ := hev.exists
  refine ⟨{
    toT58Stage5 := s, ρ := x, ρ_pos := hx0, ρ_lt := hx1, ρ_arho := ?_, ρ_loc := ?_,
    ρ_loc' := hx4, ρ_64 := hx5, ρ_102 := by linarith, ρ_tube := hx7 }, rfl, hx⟩
  · calc x ^ regExp s.c_reg * s.A_around = s.A_around * x ^ regExp s.c_reg := mul_comm _ _
      _ ≤ s.lam * s.A_across := hx2.le
  · rw [lt_div_iff₀ (by positivity)] at hx3; linarith

 


theorem exists_stage7 (s : T58Stage6 ξ Q cm cp Kann p0 pbar) {Bn : ℝ → Prop}
    (hBn : ∀ᶠ x in 𝓝[>] (0 : ℝ), Bn x) :
    ∃ s' : T58Stage7 ξ Q cm cp Kann p0 pbar, s'.toT58Stage6 = s ∧ Bn s'.A_nar := by
  have hK : 0 < 1 - Kann := by linarith [s.Kann_lt]
  have hE := endptScale_pos s.m
  have hc : 0 < Objects.Producer.cSel := by
    unfold Objects.Producer.cSel
    have h2 : (Real.sqrt 2)⁻¹ < 1 := by
      rw [inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))]
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hπ : 0 < 112 * Real.pi := by positivity
    exact div_pos (by linarith) hπ
  have hT : 0 < (2 : ℝ) ^ ((8 * Q + 12) / 3) := Real.rpow_pos_of_pos two_pos _
  have hρ := s.ρ_pos
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), Bn x ∧ 0 < x ∧ x ≤ s.lam * (1 - Kann) * endptScale s.m * s.ρ ∧
      x < 1 / 6 ∧ x < 1 / 2 - 100 * s.ρ ∧
      (∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < x →
        21 * (((k : ℝ) + 3) * ((ξ : ℝ) * (Q + 3)) + (Real.logb 2 (2 * s.A_around) + 2)) ≤
          Objects.Producer.cSel * (endptScale s.m * s.ρ) * (2 : ℝ) ^ ((k : ℝ) / 4)) ∧
      x ≤ s.lam / (2 : ℝ) ^ ((8 * Q + 12) / 3) := by
    have := s.lam_pos
    filter_upwards [hBn, ev_pos,
      ev_le (show 0 < s.lam * (1 - Kann) * endptScale s.m * s.ρ by positivity),
      ev_lt (show (0 : ℝ) < 1 / 6 by norm_num),
      ev_lt (show (0 : ℝ) < 1 / 2 - 100 * s.ρ by linarith [s.ρ_102]),
      ev_count (a := (ξ : ℝ) * (Q + 3)) (c := Real.logb 2 (2 * s.A_around) + 2)
        (show 0 < Objects.Producer.cSel * (endptScale s.m * s.ρ) by positivity),
      ev_le (show 0 < s.lam / (2 : ℝ) ^ ((8 * Q + 12) / 3) by positivity)]
      with x h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨x, hx, hx0, hx1, hx2, hx3, hx4, hx5⟩ := hev.exists
  refine ⟨{
    toT58Stage6 := s, A_nar := x, nar_pos := hx0, nar_le := hx1, nar_sixth := hx2,
    nar_le' := by linarith, nar_rho := by linarith, nar_count := ?_, nar_Q := ?_ }, rfl, hx⟩
  · intro k hk
    have := hx4 k hk
    have e : ((k : ℝ) + 3) * ((ξ : ℝ) * (Q + 3)) + Real.logb 2 (2 * s.A_around) + 2 =
        ((k : ℝ) + 3) * ((ξ : ℝ) * (Q + 3)) + (Real.logb 2 (2 * s.A_around) + 2) := by ring
    rw [e]; exact this
  · rw [le_div_iff₀ hx0]
    rw [le_div_iff₀ hT] at hx5
    linarith

 
theorem exists_stage8 (s : T58Stage7 ξ Q cm cp Kann p0 pbar) :
    ∃ s' : T58Stage8 ξ Q cm cp Kann p0 pbar, s'.toT58Stage7 = s := by
  have hθ : 0 < regExp s.c_reg := regExp_pos s.c_reg_pos
  have hb0 : 0 < s.A_around := by linarith [s.around_gt]
  have hN : 0 < s.A_nar ^ ((ξ : ℝ) * (Q + 3)) := Real.rpow_pos_of_pos s.nar_pos _
  have := s.lam_pos
  obtain ⟨x, hx0, hx1, hx2, hx3⟩ := (ev_pos.and
    ((ev_lt (show 0 < s.lam * epScale s.k0 by have := epScale_pos s.k0; positivity)).and
    ((ev_lt s.nar_pos).and (ev_two_mul_rpow_lt hθ
      (show 0 < s.lam * s.A_nar ^ ((ξ : ℝ) * (Q + 3)) / (4 * s.A_around) by positivity))))).exists
  refine ⟨{
    toT58Stage7 := s, A_set := x, set_pos := hx0, set_lt_ep := hx1, set_lt_nar := hx2,
    set_loop := ?_ }, rfl⟩
  rw [lt_div_iff₀ (by positivity)] at hx3
  linarith

 
theorem exists_stage9 (s : T58Stage8 ξ Q cm cp Kann p0 pbar) {Bw : ℝ → Prop}
    (hBw : ∀ᶠ y in atTop, Bw y) :
    ∃ s' : T58Stage9 ξ Q cm cp Kann p0 pbar, s'.toT58Stage8 = s ∧ Bw s'.A_internal := by
  obtain ⟨y, hy, hy1⟩ := (hBw.and (ev_atTop_gt s.A_set⁻¹)).exists
  exact ⟨{
    toT58Stage8 := s, A_internal := y, internal_gt := hy1 }, rfl, hy⟩

 

theorem amax_spec {ξr A x₁ x₂ : ℝ} (hξ : 0 < ξr) (hA : 0 < A) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    Real.exp (-ξr * (ξr⁻¹ * max (Real.log (A / x₁)) (Real.log (A / x₂)))) * A ≤ x₁ ∧
      Real.exp (-ξr * (ξr⁻¹ * max (Real.log (A / x₁)) (Real.log (A / x₂)))) * A ≤ x₂ := by
  have e : -ξr * (ξr⁻¹ * max (Real.log (A / x₁)) (Real.log (A / x₂))) =
      -max (Real.log (A / x₁)) (Real.log (A / x₂)) := by
    field_simp
  rw [e]
  have key : ∀ x : ℝ, 0 < x → Real.log (A / x) ≤ max (Real.log (A / x₁)) (Real.log (A / x₂)) →
      Real.exp (-max (Real.log (A / x₁)) (Real.log (A / x₂))) * A ≤ x := by
    intro x hx hle
    have h1 : Real.exp (-max (Real.log (A / x₁)) (Real.log (A / x₂))) ≤
        Real.exp (-Real.log (A / x)) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg (Real.log (A / x)), Real.exp_log (div_pos hA hx), inv_div] at h1
    calc Real.exp (-max (Real.log (A / x₁)) (Real.log (A / x₂))) * A ≤ x / A * A :=
          mul_le_mul_of_nonneg_right h1 hA.le
      _ = x := div_mul_cancel₀ x hA.ne'
  exact ⟨key x₁ hx₁ (le_max_left _ _), key x₂ hx₂ (le_max_right _ _)⟩

 
theorem exists_stage10 (s : T58Stage9 ξ Q cm cp Kann p0 pbar) :
    ∃ s' : T58Stage10 ξ Q cm cp Kann p0 pbar, s'.toT58Stage9 = s := by
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hlam := s.lam_pos
  have hac := s.across_pos
  have hN : 0 < s.lam * s.A_nar ^ ((ξ : ℝ) * (Q + 3)) :=
    mul_pos hlam (Real.rpow_pos_of_pos s.nar_pos _)
  have hX : 0 < s.lam * s.A_across := mul_pos hlam hac
  have hint : 0 < s.A_internal := (inv_pos.2 s.set_pos).trans s.internal_gt
  set Amax : ℝ := (ξ : ℝ)⁻¹ * max (Real.log (s.A_internal / (s.lam * s.A_nar ^ ((ξ : ℝ) * (Q + 3)))))
    (Real.log (s.A_internal / (s.lam * s.A_across))) with hAmax
  obtain ⟨h1, h2⟩ := amax_spec (ξr := (ξ : ℝ)) hξ hint hN hX
  
  have hlam1 : s.lam < 1 := by
    have h10 : (10 : ℝ) ^ (-(100 : ℤ)) ≤ 1 := by rw [zpow_neg]; norm_num
    have hM : min cm (min cp⁻¹ ((cm / cp) ^ 2)) < 1 := by
      have hcp : 0 < cp := s.cm_pos.trans s.cm_lt_cp
      have hq : (cm / cp) ^ 2 < 1 := by
        have h1 : cm / cp < 1 := (div_lt_one hcp).2 s.cm_lt_cp
        have h0 : 0 ≤ cm / cp := div_nonneg s.cm_pos.le hcp.le
        nlinarith
      exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) hq
    have := s.lam_small
    have h10p : 0 < (10 : ℝ) ^ (-(100 : ℤ)) := zpow_pos (by norm_num) _
    have : (10 : ℝ) ^ (-(100 : ℤ)) * min cm (min cp⁻¹ ((cm / cp) ^ 2)) < 1 := by
      calc (10 : ℝ) ^ (-(100 : ℤ)) * min cm (min cp⁻¹ ((cm / cp) ^ 2)) ≤
            1 * min cm (min cp⁻¹ ((cm / cp) ^ 2)) := by
            apply mul_le_mul_of_nonneg_right h10
            exact (lt_min s.cm_pos (lt_min (inv_pos.2 (s.cm_pos.trans s.cm_lt_cp))
              (pow_pos (div_pos s.cm_pos (s.cm_pos.trans s.cm_lt_cp)) 2))).le
        _ < 1 := by rw [one_mul]; exact hM
    linarith
  have hset1 : s.A_set < 1 := by
    have h1 : s.A_set < s.lam * epScale s.k0 := s.set_lt_ep
    have h2 : epScale s.k0 < 1 / 4 := s.ep_lt_quarter
    have h3 : s.lam * epScale s.k0 < 1 := by
      have := epScale_pos s.k0
      nlinarith
    linarith
  have hint1 : 1 < s.A_internal := by
    have : 1 < s.A_set⁻¹ := by rw [lt_inv_comm₀ one_pos s.set_pos, inv_one]; exact hset1
    linarith [s.internal_gt]
  have hX1 : s.lam * s.A_across < 1 := by nlinarith [s.across_lt]
  have hpos : 0 < Amax := by
    have hlog : 0 < Real.log (s.A_internal / (s.lam * s.A_across)) := by
      apply Real.log_pos
      rw [lt_div_iff₀ hX, one_mul]; linarith
    have := le_max_right (Real.log (s.A_internal / (s.lam * s.A_nar ^ ((ξ : ℝ) * (Q + 3)))))
      (Real.log (s.A_internal / (s.lam * s.A_across)))
    rw [hAmax]
    exact mul_pos (inv_pos.2 hξ) (by linarith)
  exact ⟨{
    toT58Stage9 := s, A_max := Amax, max_pos := hpos, max_nar := h1, max_across := h2 },
    rfl⟩

 

theorem exists_stage11 (s : T58Stage10 ξ Q cm cp Kann p0 pbar) {Bs : ℝ → Prop}
    (hBs : ∀ᶠ x in 𝓝[>] (0 : ℝ), Bs x) {Be : ℝ → ℝ → Prop} (hBe : ∀ x, ∀ᶠ E in atTop, Be x E) :
    ∃ s' : T58Stage11 ξ Q cm cp Kann p0 pbar, s'.toT58Stage10 = s ∧ Bs s'.A_sup ∧
      Be s'.A_sup s'.E_max := by
  have := s.lam_pos; have := s.max_pos
  obtain ⟨x, hx, hx0, hx1, hx2, hx3⟩ := (hBs.and (ev_pos.and
    ((ev_lt (show 0 < s.lam / s.A_max by positivity)).and ((ev_lt s.set_pos).and
      (ev_le (show (0 : ℝ) < 1 / 64 by norm_num)))))).exists
  obtain ⟨E, hE, hE0⟩ := ((hBe x).and (ev_atTop_gt 0)).exists
  exact ⟨{
    toT58Stage10 := s, A_sup := x, sup_pos := hx0, sup_lt_max := hx1, sup_lt_set := hx2,
    sup_le := hx3, E_max := E, E_max_pos := hE0 }, rfl, hx, hE⟩

 
theorem exists_table (s : T58Stage11 ξ Q cm cp Kann p0 pbar) :
    ∃ t : T58Table ξ Q cm cp Kann p0 pbar, t.toT58Stage11 = s := by
  obtain ⟨y, hy1, hy2⟩ := ((ev_atTop_gt s.A_sup⁻¹).and
    (ev_gauss_le s.E_max_pos (show 0 < (1 - pbar) / 10 by linarith [s.pbar_lt]))).exists
  exact ⟨{
    toT58Stage11 := s, A_RN := y, rn_gt := hy1, rn_budget := hy2 }, rfl⟩

 

 




theorem exists_t58Table (hQ : 0 < Q) (hcm : 0 < cm) (hcmp : cm < cp) (hK1 : 3 / 4 < Kann)
    (hK2 : Kann < 1) (hp1 : 0 < p0) (hp2 : p0 < 1) (hb1 : 0 < pbar) (hb2 : pbar < 1)
    (B : T58Budgets ξ Q cm cp Kann p0 pbar) (hB : B.Eventually) :
    ∃ t : T58Table ξ Q cm cp Kann p0 pbar, t.Satisfies B := by
  obtain ⟨s1, hreg⟩ := exists_stage1 (ξ := ξ) hQ hcm hcmp hK1 hK2 hp1 hp2 hb1 hb2 hB.reg
  obtain ⟨s2, rfl, hblock, hshield⟩ := exists_stage2 s1 (hB.block s1) (hB.shield s1)
  obtain ⟨s4, rfl, hacross, haround, hregc⟩ :=
    exists_stage4 s2 (hB.across s2) (hB.around s2) (hB.regCount s2)
  obtain ⟨s5, rfl⟩ := exists_stage5 s4
  obtain ⟨s6, rfl, hevent⟩ := exists_stage6 s5 (hB.event s5)
  obtain ⟨s7, rfl, hnarrow⟩ := exists_stage7 s6 (hB.narrow s6)
  obtain ⟨s8, rfl⟩ := exists_stage8 s7
  obtain ⟨s9, rfl, hnetwork⟩ := exists_stage9 s8 (hB.network s8)
  obtain ⟨s10, rfl⟩ := exists_stage10 s9
  obtain ⟨s11, rfl, hsup, henergy⟩ := exists_stage11 s10 (hB.sup s10) (hB.energy s10)
  obtain ⟨t, rfl⟩ := exists_table s11
  exact ⟨t, hreg, hblock, hshield, hacross, haround, hregc, hevent, hnarrow, hnetwork, hsup,
    henergy⟩

 
def T58Budgets.trivial : T58Budgets ξ Q cm cp Kann p0 pbar where
  reg _ := True
  block _ _ := True
  shield _ _ _ := True
  across _ _ := True
  around _ _ := True
  regCount _ _ := True
  event _ _ := True
  narrow _ _ := True
  network _ _ := True
  sup _ _ := True
  energy _ _ _ := True

theorem T58Budgets.trivial_eventually :
    (T58Budgets.trivial : T58Budgets ξ Q cm cp Kann p0 pbar).Eventually where
  reg := Filter.Eventually.of_forall fun _ => True.intro
  block _ := Filter.Eventually.of_forall fun _ => True.intro
  shield _ _ := Filter.Eventually.of_forall fun _ => True.intro
  across _ := Filter.Eventually.of_forall fun _ => True.intro
  around _ := Filter.Eventually.of_forall fun _ => True.intro
  regCount _ := Filter.Eventually.of_forall fun _ => True.intro
  event _ := Filter.Eventually.of_forall fun _ => True.intro
  narrow _ := Filter.Eventually.of_forall fun _ => True.intro
  network _ := Filter.Eventually.of_forall fun _ => True.intro
  sup _ := Filter.Eventually.of_forall fun _ => True.intro
  energy _ _ := Filter.Eventually.of_forall fun _ => True.intro

 
theorem exists_t58Table_trivial (hQ : 0 < Q) (hcm : 0 < cm) (hcmp : cm < cp)
    (hK1 : 3 / 4 < Kann) (hK2 : Kann < 1) (hp1 : 0 < p0) (hp2 : p0 < 1) (hb1 : 0 < pbar)
    (hb2 : pbar < 1) : Nonempty (T58Table ξ Q cm cp Kann p0 pbar) := by
  obtain ⟨t, -⟩ := exists_t58Table (ξ := ξ) hQ hcm hcmp hK1 hK2 hp1 hp2 hb1 hb2
    T58Budgets.trivial T58Budgets.trivial_eventually
  exact ⟨t⟩

 

 

theorem eventually_le_threshold {a₀ : ℝ} (ha : 0 < a₀) : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ≤ a₀ :=
  ev_le ha

 

theorem eventually_ge_threshold (A₀ : ℝ) : ∀ᶠ y in atTop, A₀ ≤ y := eventually_ge_atTop A₀

theorem eventually_ge_threshold_nat (k₀ : ℕ) : ∀ᶠ k in atTop, k₀ ≤ k := eventually_ge_atTop k₀

 



theorem T58Table.forall_radius_of_thresholds (t : T58Table ξ Q cm cp Kann p0 pbar) {a A : ℝ}
    {Φ : Objects.CorrectedEvent.Constants → Prop}
    (hΦ : ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → C.A_across ≤ a → A ≤ C.A_around → Φ C)
    (ha : t.A_across ≤ a) (hA : A ≤ t.A_around) (r : Set.Ioi (0 : ℝ)) :
    Φ (t.toConstants r) :=
  hΦ (t.toConstants r) rfl rfl ha hA

end SupercriticalLQGUniqueness.Uniqueness.Objects.Density
