import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Dyadic
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T57w




 
































set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Density

 

 
def Cmid (cm cp : ℝ) : ℝ := (cm + cp) / 2

 
def Cmid0 (cm cp : ℝ) : ℝ := (cm + Cmid cm cp) / 2

 
def regExp (c_reg : ℝ) : ℝ := Real.log (1 + c_reg) / (48 * Real.log 2)

 
def epScale (k0 : ℕ) : ℝ := (2 : ℝ) ^ (-(k0 : ℝ))

 
def endptScale (m : ℕ) : ℝ := (1 / 16 : ℝ) ^ m

 
def locScale (K_sh : ℕ) : ℝ := 3 * (8 : ℝ) ^ K_sh

 
def blockM (lam : ℝ) (m : ℕ) : ℕ := ⌊2 * Real.pi / (lam * endptScale m)⌋₊

 
def blockProb (p0 lam : ℝ) (m : ℕ) : ℝ := p0 / (16 * (((m + 1) * blockM lam m ^ 2 : ℕ) : ℝ))

theorem Cmid_eq_midpoint (cMinus cPlus : ℝ≥0∞) :
    Cmid cMinus.toReal cPlus.toReal = EndSaving.Interfaces.midpoint cMinus cPlus := rfl

theorem cm_lt_Cmid0 {cm cp : ℝ} (h : cm < cp) : cm < Cmid0 cm cp := by
  unfold Cmid0 Cmid; linarith

theorem Cmid0_lt_Cmid {cm cp : ℝ} (h : cm < cp) : Cmid0 cm cp < Cmid cm cp := by
  unfold Cmid0 Cmid; linarith

theorem Cmid0_pos {cm cp : ℝ} (hm : 0 < cm) (h : cm < cp) : 0 < Cmid0 cm cp :=
  hm.trans (cm_lt_Cmid0 h)

theorem regExp_pos {c : ℝ} (hc : 0 < c) : 0 < regExp c := by
  unfold regExp
  have h1 : 0 < Real.log (1 + c) := Real.log_pos (by linarith)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem epScale_pos (k0 : ℕ) : 0 < epScale k0 := Real.rpow_pos_of_pos (by norm_num) _

theorem endptScale_pos (m : ℕ) : 0 < endptScale m := pow_pos (by norm_num) m

theorem endptScale_le_one (m : ℕ) : endptScale m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem locScale_pos (K : ℕ) : 0 < locScale K := by unfold locScale; positivity

 

 
structure T58Stage1 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ) where
   
  Q_pos : 0 < Q
   
  cm_pos : 0 < cm
  cm_lt_cp : cm < cp
   
  Kann_gt : 3 / 4 < Kann
  Kann_lt : Kann < 1
  p0_pos : 0 < p0
  p0_lt : p0 < 1
   
  pbar_pos : 0 < pbar
  pbar_lt : pbar < 1
   
  c_reg : ℝ
  c_reg_pos : 0 < c_reg
  c_reg_lt : c_reg < 1
   
  lam : ℝ
  lam_pos : 0 < lam
  lam_small : lam < (10 : ℝ) ^ (-(100 : ℤ)) * min cm (min cp⁻¹ ((cm / cp) ^ 2))
   
  lam_ratio_pos : 10 * cp * lam < 1
  lam_ratio : (1 + 10 * cp * lam) / (1 - 10 * cp * lam) * Cmid0 cm cp ≤ Cmid cm cp

 
structure T58Stage2 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage1 ξ Q cm cp Kann p0 pbar where
  m : ℕ
  m_pos : 1 ≤ m
   
  endpt_a : endptScale m ≤ lam * (1 - Kann) ^ 2
   
  endpt_b : endptScale m ≤ (1 - Kann) ^ 4 / 4
   
  endpt_c : 4 * Real.sqrt (endptScale m) ≤ (1 - Kann) / 2
  K_sh : ℕ
  K_sh_pos : 1 ≤ K_sh

 
structure T58Stage4 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage2 ξ Q cm cp Kann p0 pbar where
  A_across : ℝ
  across_pos : 0 < A_across
  across_lt : A_across < 1
  A_around : ℝ
  around_gt : 1 < A_around
  around_gt_inv : A_across⁻¹ < A_around
  k0 : ℕ
  k0_ge : 48 ≤ k0
  reg_ep : (c_reg ^ 2)⁻¹ * (1 + c_reg) ^ 3 * (2 : ℝ) ^ (2 * regExp c_reg) *
    epScale k0 ^ regExp c_reg ≤ 1
  ep_lt_around : epScale k0 < A_around⁻¹
  ep_lt_quarter : epScale k0 < 1 / 4

 
structure T58Stage5 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage4 ξ Q cm cp Kann p0 pbar where
  A_sp : ℝ
  sp_pos : 0 < A_sp
  sp_lt : A_sp < epScale k0
  sp_loop : 4 * A_sp ^ regExp c_reg * A_around < A_across ^ 2 / (16 * A_around)

 
structure T58Stage6 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage5 ξ Q cm cp Kann p0 pbar where
  ρ : ℝ
  ρ_pos : 0 < ρ
  ρ_lt : ρ < lam * A_sp
   
  ρ_arho : ρ ^ regExp c_reg * A_around ≤ lam * A_across
  ρ_loc : 3 * locScale K_sh * ρ < 1
  ρ_loc' : ρ ≤ lam / locScale K_sh
  ρ_64 : ρ < 1 / 64
  ρ_102 : 102 * ρ < 1 / 2
   
  ρ_tube : ρ ≤ 10 * lam ^ 2 / (Real.pi ^ 2 * locScale K_sh ^ 2)

 
structure T58Stage7 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage6 ξ Q cm cp Kann p0 pbar where
  A_nar : ℝ
  nar_pos : 0 < A_nar
  nar_le : A_nar ≤ lam * (1 - Kann) * endptScale m * ρ
  nar_sixth : A_nar < 1 / 6
  nar_le' : A_nar ≤ 20 / 21
  nar_rho : 100 * ρ + A_nar < 1 / 2
   

  nar_count : ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < A_nar →
    21 * (((k : ℝ) + 3) * ((ξ : ℝ) * (Q + 3)) + Real.logb 2 (2 * A_around) + 2) ≤
      Objects.Producer.cSel * (endptScale m * ρ) * (2 : ℝ) ^ ((k : ℝ) / 4)
  nar_Q : (2 : ℝ) ^ ((8 * Q + 12) / 3) ≤ lam / A_nar

 
structure T58Stage8 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage7 ξ Q cm cp Kann p0 pbar where
  A_set : ℝ
  set_pos : 0 < A_set
  set_lt_ep : A_set < lam * epScale k0
  set_lt_nar : A_set < A_nar
  set_loop : 4 * (2 * A_set) ^ regExp c_reg * A_around ≤ lam * A_nar ^ ((ξ : ℝ) * (Q + 3))

 
structure T58Stage9 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage8 ξ Q cm cp Kann p0 pbar where
  A_internal : ℝ
  internal_gt : A_set⁻¹ < A_internal

 
structure T58Stage10 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage9 ξ Q cm cp Kann p0 pbar where
  A_max : ℝ
  max_pos : 0 < A_max
  max_nar : Real.exp (-(ξ : ℝ) * A_max) * A_internal ≤ lam * A_nar ^ ((ξ : ℝ) * (Q + 3))
  max_across : Real.exp (-(ξ : ℝ) * A_max) * A_internal ≤ lam * A_across

 
structure T58Stage11 (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage10 ξ Q cm cp Kann p0 pbar where
  A_sup : ℝ
  sup_pos : 0 < A_sup
  sup_lt_max : A_sup < lam / A_max
  sup_lt_set : A_sup < A_set
  sup_le : A_sup ≤ 1 / 64
  E_max : ℝ
  E_max_pos : 0 < E_max

 

structure T58Table (ξ : Set.Ioi (0 : ℝ)) (Q cm cp Kann p0 pbar : ℝ)
    extends T58Stage11 ξ Q cm cp Kann p0 pbar where
  A_RN : ℝ
  rn_gt : A_sup⁻¹ < A_RN
  rn_budget : 2 * Real.exp (-(A_RN ^ 2) / (2 * E_max)) ≤ (1 - pbar) / 10

namespace T58Table

variable {ξ : Set.Ioi (0 : ℝ)} {Q cm cp Kann p0 pbar : ℝ}

 

theorem lam_lt_tiny (t : T58Table ξ Q cm cp Kann p0 pbar) : t.lam < (10 : ℝ) ^ (-(100 : ℤ)) := by
  have hcp : 0 < cp := t.cm_pos.trans t.cm_lt_cp
  have hq : (cm / cp) ^ 2 < 1 := by
    have h1 : cm / cp < 1 := (div_lt_one hcp).2 t.cm_lt_cp
    have h0 : 0 ≤ cm / cp := div_nonneg t.cm_pos.le hcp.le
    nlinarith
  have hmin : min cm (min cp⁻¹ ((cm / cp) ^ 2)) < 1 :=
    lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) hq
  have h10 : 0 < (10 : ℝ) ^ (-(100 : ℤ)) := zpow_pos (by norm_num) _
  calc t.lam < (10 : ℝ) ^ (-(100 : ℤ)) * min cm (min cp⁻¹ ((cm / cp) ^ 2)) := t.lam_small
    _ ≤ (10 : ℝ) ^ (-(100 : ℤ)) * 1 := mul_le_mul_of_nonneg_left hmin.le h10.le
    _ = (10 : ℝ) ^ (-(100 : ℤ)) := mul_one _

theorem tiny_le : (10 : ℝ) ^ (-(100 : ℤ)) ≤ 1 / 100 := by
  rw [zpow_neg]
  norm_num

 
theorem lam_le_hundredth (t : T58Table ξ Q cm cp Kann p0 pbar) : t.lam ≤ 1 / 100 :=
  (t.lam_lt_tiny.trans_le tiny_le).le

 
theorem lam_le (t : T58Table ξ Q cm cp Kann p0 pbar) : t.lam ≤ 1 / 48 := by
  have := t.lam_le_hundredth; linarith

 
theorem lam_le_sixteenth (t : T58Table ξ Q cm cp Kann p0 pbar) : t.lam ≤ 1 / 16 := by
  have := t.lam_le_hundredth; linarith

 
theorem lam_lt_cm (t : T58Table ξ Q cm cp Kann p0 pbar) : t.lam < cm := by
  have h10 : (10 : ℝ) ^ (-(100 : ℤ)) ≤ 1 := tiny_le.trans (by norm_num)
  have h10p : 0 < (10 : ℝ) ^ (-(100 : ℤ)) := zpow_pos (by norm_num) _
  calc t.lam < (10 : ℝ) ^ (-(100 : ℤ)) * min cm (min cp⁻¹ ((cm / cp) ^ 2)) := t.lam_small
    _ ≤ (10 : ℝ) ^ (-(100 : ℤ)) * cm := mul_le_mul_of_nonneg_left (min_le_left _ _) h10p.le
    _ ≤ 1 * cm := mul_le_mul_of_nonneg_right h10 t.cm_pos.le
    _ = cm := one_mul _

 
theorem lam_ratio_lt_one (t : T58Table ξ Q cm cp Kann p0 pbar) : t.lam * cp / cm < 1 := by
  have hcp : 0 < cp := t.cm_pos.trans t.cm_lt_cp
  have h10 : (10 : ℝ) ^ (-(100 : ℤ)) ≤ 1 := tiny_le.trans (by norm_num)
  have h10p : 0 < (10 : ℝ) ^ (-(100 : ℤ)) := zpow_pos (by norm_num) _
  have hq : t.lam < (cm / cp) ^ 2 := by
    calc t.lam < (10 : ℝ) ^ (-(100 : ℤ)) * min cm (min cp⁻¹ ((cm / cp) ^ 2)) := t.lam_small
      _ ≤ (10 : ℝ) ^ (-(100 : ℤ)) * (cm / cp) ^ 2 :=
          mul_le_mul_of_nonneg_left (le_trans (min_le_right _ _) (min_le_right _ _)) h10p.le
      _ ≤ 1 * (cm / cp) ^ 2 := mul_le_mul_of_nonneg_right h10 (sq_nonneg _)
      _ = (cm / cp) ^ 2 := one_mul _
  have hr : cm / cp < 1 := (div_lt_one hcp).2 t.cm_lt_cp
  have hr0 : 0 < cm / cp := div_pos t.cm_pos hcp
  rw [div_lt_one t.cm_pos]
  have h1 : t.lam < cm / cp := by nlinarith
  calc t.lam * cp < cm / cp * cp := mul_lt_mul_of_pos_right h1 hcp
    _ = cm := div_mul_cancel₀ _ hcp.ne'

 

theorem ratio (t : T58Table ξ Q cm cp Kann p0 pbar) :
    (1 + 10 * cp * t.lam) * Cmid0 cm cp ≤ Cmid cm cp * (1 - 10 * cp * t.lam) := by
  have hpos : 0 < 1 - 10 * cp * t.lam := by linarith [t.lam_ratio_pos]
  have h := t.lam_ratio
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos] at h
  exact h

theorem Kann_nonneg (t : T58Table ξ Q cm cp Kann p0 pbar) : 0 ≤ Kann := by
  linarith [t.Kann_gt]

theorem endpt_le_one (t : T58Table ξ Q cm cp Kann p0 pbar) : endptScale t.m ≤ 1 :=
  endptScale_le_one t.m

theorem internal_pos (t : T58Table ξ Q cm cp Kann p0 pbar) : 0 < t.A_internal :=
  (inv_pos.2 t.set_pos).trans t.internal_gt

theorem rn_pos (t : T58Table ξ Q cm cp Kann p0 pbar) : 0 < t.A_RN :=
  (inv_pos.2 t.sup_pos).trans t.rn_gt

 


theorem dg_chain (t : T58Table ξ Q cm cp Kann p0 pbar) :
    t.A_across < 1 ∧ t.A_around⁻¹ < t.A_across ∧ epScale t.k0 < t.A_around⁻¹ ∧
      t.A_sp < epScale t.k0 ∧ t.ρ < t.A_sp ∧ t.A_nar < t.ρ ∧ t.A_set < t.A_nar ∧
      t.A_internal⁻¹ < t.A_set ∧ t.A_RN⁻¹ < t.A_sup ∧ t.A_sup < t.lam / t.A_max := by
  have hlam1 : t.lam < 1 := by have := t.lam_le_hundredth; linarith
  refine ⟨t.across_lt, ?_, t.ep_lt_around, t.sp_lt, ?_, ?_, t.set_lt_nar, ?_, ?_, t.sup_lt_max⟩
  · rw [inv_lt_comm₀ (by linarith [t.around_gt]) t.across_pos]; exact t.around_gt_inv
  · calc t.ρ < t.lam * t.A_sp := t.ρ_lt
      _ < 1 * t.A_sp := mul_lt_mul_of_pos_right hlam1 t.sp_pos
      _ = t.A_sp := one_mul _
  · have hK : 0 < 1 - Kann := by linarith [t.Kann_lt]
    have h1 : t.lam * (1 - Kann) * endptScale t.m < 1 := by
      have hK1 : 1 - Kann ≤ 1 := by linarith [t.Kann_gt]
      have he := t.endpt_le_one
      have hp : 0 < t.lam * (1 - Kann) := mul_pos t.lam_pos hK
      calc t.lam * (1 - Kann) * endptScale t.m ≤ t.lam * (1 - Kann) * 1 :=
            mul_le_mul_of_nonneg_left he hp.le
        _ = t.lam * (1 - Kann) := mul_one _
        _ ≤ t.lam * 1 := mul_le_mul_of_nonneg_left hK1 t.lam_pos.le
        _ < 1 := by linarith
    calc t.A_nar ≤ t.lam * (1 - Kann) * endptScale t.m * t.ρ := t.nar_le
      _ < 1 * t.ρ := mul_lt_mul_of_pos_right h1 t.ρ_pos
      _ = t.ρ := one_mul _
  · rw [inv_lt_comm₀ t.internal_pos t.set_pos]; exact t.internal_gt
  · rw [inv_lt_comm₀ t.rn_pos t.sup_pos]; exact t.rn_gt

 

 
theorem sep_small (t : T58Table ξ Q cm cp Kann p0 pbar) :
    2 * Real.sqrt (endptScale t.m) * t.ρ + 2 * t.A_sup + 3 * t.A_nar ≤ t.ρ * (1 - Kann) := by
  have hK : 0 < 1 - Kann := by linarith [t.Kann_lt]
  have hsq : Real.sqrt (endptScale t.m) ≤ (1 - Kann) / 8 := by
    have := t.endpt_c; linarith
  have h1 : 2 * Real.sqrt (endptScale t.m) * t.ρ ≤ (1 - Kann) / 4 * t.ρ := by
    have := mul_le_mul_of_nonneg_right hsq t.ρ_pos.le; nlinarith
  have hlam := t.lam_le
  have he := t.endpt_le_one
  have hnar : t.A_nar ≤ (1 - Kann) * t.ρ / 48 := by
    have h2 : t.lam * (1 - Kann) * endptScale t.m ≤ (1 - Kann) / 48 := by
      have hp : 0 ≤ t.lam * (1 - Kann) := mul_nonneg t.lam_pos.le hK.le
      calc t.lam * (1 - Kann) * endptScale t.m ≤ t.lam * (1 - Kann) * 1 :=
            mul_le_mul_of_nonneg_left he hp
        _ = (1 - Kann) * t.lam := by ring
        _ ≤ (1 - Kann) * (1 / 48) := mul_le_mul_of_nonneg_left hlam hK.le
        _ = (1 - Kann) / 48 := by ring
    have h3 := mul_le_mul_of_nonneg_right h2 t.ρ_pos.le
    have := t.nar_le
    nlinarith
  have hsup : t.A_sup < t.A_nar := t.sup_lt_set.trans t.set_lt_nar
  have hprod : 0 ≤ (1 - Kann) * t.ρ := mul_nonneg hK.le t.ρ_pos.le
  have e1 : t.ρ * (1 - Kann) = (1 - Kann) * t.ρ := mul_comm _ _
  have e2 : (1 - Kann) / 4 * t.ρ = (1 - Kann) * t.ρ / 4 := by ring
  rw [e2] at h1
  rw [e1]
  linarith

 
theorem nar_le_rho (t : T58Table ξ Q cm cp Kann p0 pbar) : t.A_nar ≤ t.ρ / 48 := by
  have hK : 0 < 1 - Kann := by linarith [t.Kann_lt]
  have hK1 : 1 - Kann ≤ 1 := by linarith [t.Kann_gt]
  have he := t.endpt_le_one
  have hlam := t.lam_le
  have h2 : t.lam * (1 - Kann) * endptScale t.m ≤ 1 / 48 := by
    have hp : 0 ≤ t.lam * (1 - Kann) := mul_nonneg t.lam_pos.le hK.le
    calc t.lam * (1 - Kann) * endptScale t.m ≤ t.lam * (1 - Kann) * 1 :=
          mul_le_mul_of_nonneg_left he hp
      _ = t.lam * (1 - Kann) := mul_one _
      _ ≤ t.lam * 1 := mul_le_mul_of_nonneg_left hK1 t.lam_pos.le
      _ ≤ 1 / 48 := by linarith
  have h3 := mul_le_mul_of_nonneg_right h2 t.ρ_pos.le
  have := t.nar_le
  linarith

 

theorem count_of_le (t : T58Table ξ Q cm cp Kann p0 pbar) {s : ℝ}
    (hs : endptScale t.m * t.ρ ≤ s) :
    ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < t.A_nar →
      21 * (((k : ℝ) + 3) * ((ξ : ℝ) * (Q + 3)) + Real.logb 2 (2 * t.A_around) + 2) ≤
        Objects.Producer.cSel * s * (2 : ℝ) ^ ((k : ℝ) / 4) := by
  intro k hk
  have hc : 0 < Objects.Producer.cSel := by
    unfold Objects.Producer.cSel
    have h2 : (Real.sqrt 2)⁻¹ < 1 := by
      rw [inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))]
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hπ : 0 < 112 * Real.pi := by positivity
    exact div_pos (by linarith) hπ
  have hp : 0 < (2 : ℝ) ^ ((k : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  refine le_trans (t.nar_count k hk) ?_
  have := mul_le_mul_of_nonneg_left hs hc.le
  exact mul_le_mul_of_nonneg_right this hp.le

 

 




def params (t : T58Table ξ Q cm cp Kann p0 pbar) : EndSaving.Interfaces.Parameters ξ where
  Cmax := t.A_max
  Cacross := t.A_across
  Caround := t.A_around
  Crn := Real.exp (t.A_RN + t.E_max / 2)
  Ctime := t.A_across ^ 2 / (4 * t.A_around)
  Cinc := Real.exp (-(ξ : ℝ) * t.A_max) * t.A_nar ^ ((ξ : ℝ) * (Q + 3))
  Ctube := t.A_internal
  max_pos := t.max_pos
  across_pos := t.across_pos
  around_pos := by linarith [t.around_gt]
  rn_pos := Real.exp_pos _
  time_pos := by have := t.around_gt; have := t.across_pos; positivity
  inc_pos := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos t.nar_pos _)
  tube_pos := t.internal_pos
  around_gt_across := by linarith [t.across_lt, t.around_gt]
  strict_slack := by
    have har0 : 0 < t.A_around := by linarith [t.around_gt]
    have e1 : (2 * t.A_around / t.A_across) * (t.A_across ^ 2 / (4 * t.A_around)) =
        t.A_across / 2 := by
      field_simp [t.across_pos.ne', har0.ne']
      ring
    rw [e1]
    have hac := t.across_pos
    have hlamAac : t.lam * t.A_across ≤ t.A_across / 16 := by
      have := mul_le_mul_of_nonneg_right t.lam_le_sixteenth hac.le
      linarith
    have := t.max_across
    have e2 : 4 * Real.exp (-(ξ : ℝ) * t.A_max) * t.A_internal =
        4 * (Real.exp (-(ξ : ℝ) * t.A_max) * t.A_internal) := by ring
    rw [e2]
    linarith

theorem params_Cmax (t : T58Table ξ Q cm cp Kann p0 pbar) : t.params.Cmax = t.A_max := rfl
theorem params_Cacross (t : T58Table ξ Q cm cp Kann p0 pbar) : t.params.Cacross = t.A_across := rfl
theorem params_Caround (t : T58Table ξ Q cm cp Kann p0 pbar) : t.params.Caround = t.A_around := rfl
theorem params_Crn (t : T58Table ξ Q cm cp Kann p0 pbar) :
    t.params.Crn = Real.exp (t.A_RN + t.E_max / 2) := rfl
theorem params_Ctime (t : T58Table ξ Q cm cp Kann p0 pbar) :
    t.params.Ctime = t.A_across ^ 2 / (4 * t.A_around) := rfl
theorem params_Ctube (t : T58Table ξ Q cm cp Kann p0 pbar) : t.params.Ctube = t.A_internal := rfl

 
theorem params_relation0 (t : T58Table ξ Q cm cp Kann p0 pbar) :
    (2 * t.params.Caround / t.params.Cacross) * t.params.Ctime = t.A_across / 2 := by
  have har0 : 0 < t.A_around := by linarith [t.around_gt]
  show (2 * t.A_around / t.A_across) * (t.A_across ^ 2 / (4 * t.A_around)) = t.A_across / 2
  field_simp [t.across_pos.ne', har0.ne']
  ring

 

 
def toConstants (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) : Objects.CorrectedEvent.Constants where
  ξ := ξ
  Q := Q
  r := r
  lamConst := t.lam
  ρ := t.ρ
  A_loc := locScale t.K_sh
  K_ann := Kann
  A_across := t.A_across
  A_around := t.A_around
  c_reg := t.c_reg
  k0 := t.k0
  A_sp := t.A_sp
  A_nar := t.A_nar
  A_set := t.A_set
  A_internal := t.A_internal
  A_max := t.A_max
  A_sup := t.A_sup
  A_endpt := endptScale t.m
  A_RN := t.A_RN
  rPos := r.2
  ξPos := ξ.2
  QPos := t.Q_pos
  lamPos := t.lam_pos
  rhoPos := t.ρ_pos
  supPos := t.sup_pos
  regPos := t.c_reg_pos
  regLtOne := t.c_reg_lt
  k0Large := t.k0_ge
  acrossPos := t.across_pos
  aroundGtOne := t.around_gt
  spPos := t.sp_pos
  spLtEp := t.sp_lt
  rhoLt := t.ρ_lt
  narPos := t.nar_pos
  narLe := t.nar_le
  narLeQ := t.nar_le'
  narrowQScale := t.nar_Q
  setPos := t.set_pos
  setLtNar := t.set_lt_nar
  internalPos := t.internal_pos
  maxPos := t.max_pos
  endptPos := endptScale_pos t.m
  supLtSet := t.sup_lt_set
  supLe := t.sup_le
  rnPos := t.rn_pos

 
theorem toConstants_ξ (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    (t.toConstants r).ξ = ξ := rfl
 
theorem toConstants_Q (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    (t.toConstants r).Q = Q := rfl
 
theorem toConstants_r (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    (t.toConstants r).r = r := rfl
 
theorem toConstants_max (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    (t.toConstants r).A_max = t.params.Cmax := rfl
 
theorem toConstants_inc (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    Objects.Producer.cInc (t.toConstants r) = t.params.Cinc := rfl
 

theorem toConstants_params (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    t.params.Caround = (t.toConstants r).A_around ∧ t.params.Cacross = (t.toConstants r).A_across ∧
      t.params.Ctube = (t.toConstants r).A_internal ∧
      t.params.Crn = Real.exp ((t.toConstants r).A_RN + t.E_max / 2) :=
  ⟨rfl, rfl, rfl, rfl⟩

 

theorem toConstants_relations (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) :
    0 ≤ (t.toConstants r).K_ann ∧ (t.toConstants r).A_endpt ≤ 1 ∧
      (t.toConstants r).lamConst ≤ 1 / 48 ∧
      2 * Real.sqrt (t.toConstants r).A_endpt * (t.toConstants r).ρ + 2 * (t.toConstants r).A_sup +
          3 * (t.toConstants r).A_nar ≤ (t.toConstants r).ρ * (1 - (t.toConstants r).K_ann) ∧
      2 * (t.toConstants r).ρ + (t.toConstants r).A_sup + 3 * (t.toConstants r).A_nar ≤ 1 / 2 ∧
      (t.toConstants r).ρ < 1 / 64 := by
  refine ⟨t.Kann_nonneg, t.endpt_le_one, t.lam_le, t.sep_small, ?_, t.ρ_64⟩
  show 2 * t.ρ + t.A_sup + 3 * t.A_nar ≤ 1 / 2
  have h1 : t.A_sup < t.A_nar := t.sup_lt_set.trans t.set_lt_nar
  have h2 := t.ρ_102
  have h3 := t.ρ_pos
  have h4 := t.nar_le_rho
  linarith

 
theorem toConstants_count (t : T58Table ξ Q cm cp Kann p0 pbar) (r : Set.Ioi (0 : ℝ)) {s : ℝ}
    (hs : (t.toConstants r).A_endpt * (t.toConstants r).ρ * (t.toConstants r).r ≤ s) :
    ∀ k : ℕ, (1 / 2 : ℝ) ^ (k + 1) < (t.toConstants r).A_nar →
      21 * (((k : ℝ) + 3) * ((t.toConstants r).ξ * ((t.toConstants r).Q + 3)) +
          Real.logb 2 (2 * (t.toConstants r).A_around) + 2) ≤
        Objects.Producer.cSel * (s / (t.toConstants r).r) * (2 : ℝ) ^ ((k : ℝ) / 4) := by
  have hr : (0 : ℝ) < r := r.2
  have hs' : endptScale t.m * t.ρ ≤ s / (r : ℝ) := by
    rw [le_div_iff₀ hr]; exact hs
  exact t.count_of_le hs'

end T58Table

end SupercriticalLQGUniqueness.Uniqueness.Objects.Density
