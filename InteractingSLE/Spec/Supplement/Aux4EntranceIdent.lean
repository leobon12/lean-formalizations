/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux4EntranceState
import InteractingSLE.Spec.Sec2.TwoSeedLogClock

/-!
# Aux. lemma 4, VII: the two-seed state in the level variable

Packet PROVE-T14-DS3. The landed clock construction of the two-seed evolution (`Sec2.TwoSeedClock`,
`Sec2.TwoSeedLogClock`: "Integrating the force-point equations back from `−∞` recovers exactly `t, L^−, L^+` and `w`",
spec L546) is written in the logarithmic clock `u`. This file transfers it to the level variable `y = e^u` used by the
restart functional (`Aux4EntranceState`): with `V = vPath U` the entrance path of the angle `U`,

* `integral_level_eq`: `∫₀^y f(U(log z)) dz = ∫_{−∞}^{log y} e^v f(U v) dv` for `[0, 1]`-valued integrands
  (`Sec2.TwoSeed.lintegral_Ioc_exp`);
* `low_vPath`, `upp_vPath`, `drv_vPath`: `low V y = L^−(log y)`, `upp V y = L^+(log y)`, `drv V y = w(log y)` for
  `0 < y ≤ R`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace Aux4

open Sec2 Sec2.TwoSeed

variable {R : ℝ≥0}

/-- **Change of variables `z = e^v`** for a continuous `[0, 1]`-valued path and a continuous transform with values in
`[0, 1]`. -/
theorem integral_level_eq {U : ℝ → ℝ} (hU : Continuous U) {f : ℝ → ℝ} (hf : Continuous f)
    (hf01 : ∀ x ∈ Icc (0 : ℝ) 1, f x ∈ Icc (0 : ℝ) 1) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1) {y : ℝ} (hy : 0 < y) :
    ∫ z in Ioc 0 y, f (U (Real.log z)) = ∫ v in Iic (Real.log y), exp v * f (U v) := by
  have hfU : ∀ z, f (U (Real.log z)) ∈ Icc (0 : ℝ) 1 := fun z => hf01 _ (hU01 _)
  have h1 : IntegrableOn (fun z => f (U (Real.log z))) (Ioc 0 y) := by
    refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne ?_ (ae_of_all _ fun z => ?_)
    · exact (hf.measurable.comp (hU.measurable.comp Real.measurable_log)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hfU z).1, (hfU z).2]
  have h2 : IntegrableOn (fun v => exp v * f (U v)) (Iic (Real.log y)) := by
    refine (integrableOn_exp_Iic (Real.log y)).mono' ?_ (ae_of_all _ fun v => ?_)
    · exact (Real.continuous_exp.mul (hf.comp hU)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos v)]
      exact mul_le_of_le_one_right (exp_pos v).le (abs_le.2 ⟨by linarith [(hf01 _ (hU01 v)).1],
        (hf01 _ (hU01 v)).2⟩)
  rw [← ENNReal.ofReal_eq_ofReal_iff (setIntegral_nonneg measurableSet_Ioc fun z _ => (hfU z).1)
    (setIntegral_nonneg measurableSet_Iic fun v _ => mul_nonneg (exp_pos v).le (hf01 _ (hU01 v)).1),
    ofReal_integral_eq_lintegral_ofReal h1 (ae_of_all _ fun z => (hfU z).1),
    ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ fun v => mul_nonneg (exp_pos v).le (hf01 _ (hU01 v)).1)]
  conv_lhs => rw [← exp_log hy]
  rw [lintegral_Ioc_exp]
  refine setLIntegral_congr_fun measurableSet_Iic fun v _ => ?_
  rw [log_exp, ← ENNReal.ofReal_mul (exp_pos v).le]

variable {U : ℝ → ℝ}

theorem ang_vPath_eq (hU : Continuous U) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) R) :
    ang (vPath (R := R) U hU) y = U (Real.log y) := by
  rw [ang_vPath hU hy]
  have h := hU01 (Real.log y)
  simp only [clamp01, min_eq_right h.2, max_eq_right h.1]

theorem low_vPath (hU : Continuous U) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) R) :
    low (vPath (R := R) U hU) y = lowerL U (Real.log y) := by
  rw [low, lowerL, intervalIntegral.integral_of_le hy.1.le]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun z => 1 - U (Real.log z)) fun z hz =>
    by rw [ang_vPath_eq hU hU01 ⟨hz.1, hz.2.trans hy.2⟩]]
  exact integral_level_eq hU (f := fun x => 1 - x) (by fun_prop)
    (fun x hx => ⟨by linarith [hx.2], by linarith [hx.1]⟩) hU01 hy.1

theorem upp_vPath (hU : Continuous U) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) R) :
    upp (vPath (R := R) U hU) y = upperL U (Real.log y) := by
  rw [upp, upperL, intervalIntegral.integral_of_le hy.1.le]
  rw [setIntegral_congr_fun measurableSet_Ioc (g := fun z => U (Real.log z)) fun z hz =>
    by rw [ang_vPath_eq hU hU01 ⟨hz.1, hz.2.trans hy.2⟩]]
  exact integral_level_eq hU (f := fun x => x) continuous_id (fun x hx => hx) hU01 hy.1

theorem drv_vPath (hU : Continuous U) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) R) :
    drv (vPath (R := R) U hU) y = driver U (Real.log y) := by
  rw [drv, driver, low_vPath hU hU01 hy, ang_vPath_eq hU hU01 hy, exp_log hy.1]

/-! ### Separated marks: from physical time to the level variable -/

section Flow

variable {κ : ℝ} {ρL ρR : Fin 1 → ℝ} {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem coef_nonneg (V : C(Icc (0 : ℝ≥0) R, ℝ)) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ coef V z :=
  mul_nonneg hz (mul_nonneg (ang_mem V z).1 (by linarith [(ang_mem V z).2]))

/-- **The clock density in the level variable**: `ℓ'(s) · coef(ℓ_s) = 2` off the collision set. -/
theorem sepRate_mul_coef (h : IsIntegratedSLEPath κ (fun _ : Fin 1 => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
    (hUc : Continuous U) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1) (hUeq : ∀ u, U u = logAngle w vL vR ζ u)
    {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (hR : sepN vL vR t₀ ≤ R) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) t₀)
    (hX : 0 < gapLR w vL s) (hY : 0 < gapRR w vR s) :
    sepRate w vL vR s * coef (vPath (R := R) U hUc) (sepN vL vR s.toNNReal) = 2 := by
  have hs0 : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
  have hsζ : (s.toNNReal : ℝ≥0∞) < ζ :=
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht₀
  have hℓ := sepN_pos h hsζ hs0
  have hℓR : sepN vL vR s.toNNReal ≤ R :=
    (le_sepN_of_le h ht₀ (Real.toNNReal_le_iff_le_coe.2 hs.2) le_rfl).trans hR
  have hang : ang (vPath (R := R) U hUc) (sepN vL vR s.toNNReal) = gapLR w vL s / sepN vL vR s.toNNReal := by
    rw [ang_vPath_eq hUc hU01 ⟨hℓ, hℓR⟩, hUeq, logAngle_log_sepN h hsζ hs0]
    rfl
  have hsum : sepN vL vR s.toNNReal = gapLR w vL s + gapRR w vR s := by
    simp only [sepN, gapLR, gapRR]; ring
  rw [coef, hang, sepRate, hsum]
  field_simp
  ring

/-- **Change of variables for the separated marks.** For a bounded nonnegative measurable `H`,
`∫₀^{ℓ_t} coef(z) H(z) dz = ∫₀^t 2 H(ℓ_s) ds`. -/
theorem integral_coef_mul_eq (h : IsIntegratedSLEPath κ (fun _ : Fin 1 => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
    (hUc : Continuous U) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1) (hUeq : ∀ u, U u = logAngle w vL vR ζ u)
    {t₀ : ℝ≥0} (ht₀ : (t₀ : ℝ≥0∞) < ζ) (hR : sepN vL vR t₀ ≤ R) {H : ℝ → ℝ} (hHm : Measurable H)
    (hH0 : ∀ z, 0 ≤ H z) {Bd : ℝ} (hHb : ∀ z, H z ≤ Bd) :
    ∫ z in (0 : ℝ)..sepN vL vR t₀, coef (vPath (R := R) U hUc) z * H z =
      ∫ s in (0 : ℝ)..t₀, 2 * H (sepN vL vR s.toNNReal) := by
  set V := vPath (R := R) U hUc with hV
  have hℓ0 : 0 ≤ sepN vL vR t₀ := by
    have := le_sepN_of_le h ht₀ (zero_le (a := t₀)) le_rfl
    rwa [sepN_zero h] at this
  have hBd : 0 ≤ Bd := (hH0 0).trans (hHb 0)
  have hG : Measurable fun z => ENNReal.ofReal (coef V z * H z) :=
    ((measurable_coef V).mul hHm).ennreal_ofReal
  have key := lintegral_comp_sepC h ht₀ (fun z => ENNReal.ofReal (coef V z * H z)) hG.aemeasurable
  -- the left side
  have hint1 : IntegrableOn (fun z => coef V z * H z) (Ioc 0 (sepN vL vR t₀)) := by
    refine Measure.integrableOn_of_bounded (M := sepN vL vR t₀ / 4 * Bd) measure_Ioc_lt_top.ne
      ((measurable_coef V).mul hHm).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hH0 z)]
    refine mul_le_mul ((abs_coef_le V z).trans ?_) (hHb z) (hH0 z) (by positivity)
    rw [abs_of_pos hz.1]; linarith [hz.2]
  have hint2 : IntegrableOn (fun s => 2 * H (sepC vL vR t₀ s)) (Ioc 0 (t₀ : ℝ)) := by
    refine Measure.integrableOn_of_bounded (M := 2 * Bd) measure_Ioc_lt_top.ne
      (measurable_const.mul (hHm.comp (continuous_sepC h ht₀).measurable)).aestronglyMeasurable
      (ae_of_all _ fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hH0 _), abs_two]
    exact mul_le_mul_of_nonneg_left (hHb _) zero_le_two
  have hcongr : ∫ s in Ioc 0 (t₀ : ℝ), 2 * H (sepN vL vR s.toNNReal) =
      ∫ s in Ioc 0 (t₀ : ℝ), 2 * H (sepC vL vR t₀ s) :=
    setIntegral_congr_fun measurableSet_Ioc fun s hs => by rw [sepC_of_le hs.2]
  rw [intervalIntegral.integral_of_le hℓ0, intervalIntegral.integral_of_le (NNReal.coe_nonneg t₀), hcongr,
    ← ENNReal.ofReal_eq_ofReal_iff
      (setIntegral_nonneg measurableSet_Ioc fun z hz => mul_nonneg (coef_nonneg V hz.1.le) (hH0 z))
      (setIntegral_nonneg measurableSet_Ioc fun s _ => mul_nonneg zero_le_two (hH0 _)),
    ofReal_integral_eq_lintegral_ofReal hint1 ((ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun z hz => mul_nonneg (coef_nonneg V hz.1.le) (hH0 z))),
    ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ fun s => mul_nonneg zero_le_two (hH0 _)), ← key]
  refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
  filter_upwards [ae_gaps_pos h ht₀] with s hgap hs
  obtain ⟨hX, hY⟩ := hgap hs
  rw [sepC_of_le hs.2, ← ENNReal.ofReal_mul (sepRate_nonneg h ht₀ hs.2), ← mul_assoc,
    sepRate_mul_coef h hUc hU01 hUeq ht₀ hR hs hX hY]

/-- **A separated mark of the evolution is the level-variable mark** at the level reached. -/
theorem mark_eq_of_flow (h : IsIntegratedSLEPath κ (fun _ : Fin 1 => 0) (fun _ => 0) ρL ρR w vL vR b ζ)
    (hUc : Continuous U) (hU01 : ∀ v, U v ∈ Icc (0 : ℝ) 1) (hUeq : ∀ u, U u = logAngle w vL vR ζ u)
    {t₁ : ℝ≥0} (ht₁ : (t₁ : ℝ≥0∞) < ζ) {R : ℝ≥0} (hR : (R : ℝ) = sepN vL vR t₁) {δ : ℝ} {F : ℝ → ℝ}
    (hF : IsCut δ F) (hk : (R : ℝ) ^ 2 / (4 * δ ^ 2) < 1) (hsign : (∀ x, F x ≤ 0) ∨ ∀ x, 0 ≤ F x)
    {Y : ℝ≥0 → ℝ} {x₀ : ℝ} (hYc : ContinuousOn (fun s : ℝ => Y s.toNNReal) (Icc 0 t₁))
    (hY : ∀ t ≤ t₁, Y t = x₀ + ∫ s in (0 : ℝ)..t, 2 * F (Y s.toNNReal - w s.toNNReal)) :
    Y t₁ = mark F x₀ (vPath (R := R) U hUc) R := by
  set V := vPath (R := R) U hUc with hV
  have hδ := hF.pos
  have hRpos : (0 : ℝ) ≤ R := NNReal.coe_nonneg R
  have hwc : ContinuousOn (fun s : ℝ => w s.toNNReal) (Icc 0 t₁) :=
    (path_continuousOn_w h).comp continuous_real_toNNReal.continuousOn fun s hs =>
      lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht₁
  -- the separation at earlier times
  have hℓle : ∀ t ≤ t₁, sepN vL vR t ≤ R := fun t ht => by
    rw [hR]; exact le_sepN_of_le h ht₁ ht le_rfl
  have hℓ0 : ∀ t ≤ t₁, 0 ≤ sepN vL vR t := fun t ht => by
    have := le_sepN_of_le h ht₁ (zero_le (a := t)) ht
    rwa [sepN_zero h] at this
  have h8 : ∀ t ≤ t₁, 8 * (t : ℝ) ≤ (R : ℝ) ^ 2 := fun t ht =>
    (eight_mul_le_sepN_sq h (lt_of_le_of_lt (by exact_mod_cast ht) ht₁)).trans
      (pow_le_pow_left₀ (hℓ0 t ht) (hℓle t ht) 2)
  -- the driver in the level variable
  have hdrv : ∀ s : ℝ, s ∈ Ioc (0 : ℝ) t₁ → drv V (sepN vL vR s.toNNReal) = w s.toNNReal := by
    intro s hs
    have hs0 : 0 < s.toNNReal := Real.toNNReal_pos.2 hs.1
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ :=
      lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht₁
    have hle := hℓle _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
    rw [drv_vPath hUc hU01 ⟨sepN_pos h hsζ hs0, hle⟩, w_eq_driver_logAngle h hsζ hs0,
      show U = logAngle w vL vR ζ from funext hUeq]
  -- the conversion of the Picard integrals
  have hconv : ∀ (g : ℝ → ℝ), Measurable g → ∀ t ≤ t₁,
      ∫ z in (0 : ℝ)..sepN vL vR t, coef V z * F (g z - drv V z) =
        ∫ s in (0 : ℝ)..t, 2 * F (g (sepN vL vR s.toNNReal) - w s.toNNReal) := by
    intro g hg t ht
    have htζ : (t : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast ht) ht₁
    have hHm : Measurable fun z => F (g z - drv V z) := hF.cont.measurable.comp (hg.sub (measurable_drv V))
    have hcongr : ∫ s in (0 : ℝ)..t, 2 * F (g (sepN vL vR s.toNNReal) - w s.toNNReal) =
        ∫ s in (0 : ℝ)..t, 2 * F (g (sepN vL vR s.toNNReal) - drv V (sepN vL vR s.toNNReal)) := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => ?_)
      rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
      rw [hdrv s ⟨hs.1, hs.2.trans (by exact_mod_cast ht)⟩]
    rw [hcongr]
    rcases hsign with hneg | hpos
    · have e := integral_coef_mul_eq h hUc hU01 hUeq htζ (hℓle t ht) (H := fun z => -F (g z - drv V z))
        hHm.neg (fun z => by linarith [hneg (g z - drv V z)]) (Bd := 1 / δ)
        (fun z => by have := hF.bound (g z - drv V z); rw [abs_le] at this; linarith [this.1])
      simp only [mul_neg, intervalIntegral.integral_neg, neg_inj] at e
      exact e
    · exact integral_coef_mul_eq h hUc hU01 hUeq htζ (hℓle t ht) (H := fun z => F (g z - drv V z))
        hHm (fun z => hpos _) (Bd := 1 / δ)
        (fun z => by have := hF.bound (g z - drv V z); rw [abs_le] at this; linarith [this.2])
  -- the comparison with the Picard iterates
  set c₀ : ℝ := (R : ℝ) ^ 2 / (4 * δ) with hc₀
  set k : ℝ := (R : ℝ) ^ 2 / (4 * δ ^ 2) with hkdef
  have hmeasF : ∀ (G : ℝ → ℝ), ContinuousOn G (Icc 0 t₁) → ∀ t ≤ t₁,
      IntervalIntegrable (fun s => 2 * F (G s - w s.toNNReal)) volume 0 t := by
    intro G hG t ht
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le (NNReal.coe_nonneg t)]
    exact (continuousOn_const.mul (hF.cont.comp_continuousOn ((hG.sub hwc).mono
      (Icc_subset_Icc le_rfl (by exact_mod_cast ht)))))
  have hpicc : ∀ n, ContinuousOn (fun s : ℝ => pic F x₀ V n (sepN vL vR s.toNNReal)) (Icc 0 t₁) := fun n =>
    (continuous_pic hF x₀ V n).comp_continuousOn
      (((continuous_sepC h ht₁).continuousOn).congr fun s hs => (sepC_of_le hs.2).symm)
  have key : ∀ n : ℕ, ∀ t ≤ t₁, |Y t - pic F x₀ V n (sepN vL vR t)| ≤ c₀ * k ^ n := by
    intro n
    induction n with
    | zero =>
      intro t ht
      simp only [pic, pow_zero, mul_one]
      rw [hY t ht, add_sub_cancel_left]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
        (f := fun s => 2 * F (Y s.toNNReal - w s.toNNReal)) (C := 2 / δ) fun s _ => by
          rw [Real.norm_eq_abs, abs_mul, abs_two]
          have := hF.bound (Y s.toNNReal - w s.toNNReal)
          calc 2 * |F (Y s.toNNReal - w s.toNNReal)| ≤ 2 * (1 / δ) := by gcongr
            _ = 2 / δ := by ring
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)] at hb
      refine hb.trans ?_
      rw [hc₀, div_mul_eq_mul_div, div_le_div_iff₀ hδ (by positivity)]
      nlinarith [h8 t ht]
    | succ n ih =>
      intro t ht
      have e1 : pic F x₀ V (n + 1) (sepN vL vR t) = x₀ + ∫ s in (0 : ℝ)..t,
          2 * F (pic F x₀ V n (sepN vL vR s.toNNReal) - w s.toNNReal) := by
        simp only [pic]
        rw [hconv _ (continuous_pic hF x₀ V n).measurable t ht]
      rw [hY t ht, e1, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
        (hmeasF _ hYc t ht) (hmeasF _ (hpicc n) t ht)]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
        (C := 2 / δ ^ 2 * (c₀ * k ^ n))
        (f := fun s => 2 * F (Y s.toNNReal - w s.toNNReal) -
          2 * F (pic F x₀ V n (sepN vL vR s.toNNReal) - w s.toNNReal)) fun s hs => by
          rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
          have hst : s.toNNReal ≤ t₁ := Real.toNNReal_le_iff_le_coe.2 (hs.2.trans (by exact_mod_cast ht))
          rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_two]
          have h1 := hF.lip (Y s.toNNReal - w s.toNNReal)
            (pic F x₀ V n (sepN vL vR s.toNNReal) - w s.toNNReal)
          rw [sub_sub_sub_cancel_right] at h1
          have h2 := ih s.toNNReal hst
          calc 2 * |F (Y s.toNNReal - w s.toNNReal) - F (pic F x₀ V n (sepN vL vR s.toNNReal) - w s.toNNReal)|
              ≤ 2 * (|Y s.toNNReal - pic F x₀ V n (sepN vL vR s.toNNReal)| / δ ^ 2) := by gcongr
            _ ≤ 2 * (c₀ * k ^ n / δ ^ 2) := by gcongr
            _ = 2 / δ ^ 2 * (c₀ * k ^ n) := by ring
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)] at hb
      refine hb.trans ?_
      have hck : 0 ≤ c₀ * k ^ n := by positivity
      calc 2 / δ ^ 2 * (c₀ * k ^ n) * (t : ℝ) ≤ 2 / δ ^ 2 * (c₀ * k ^ n) * ((R : ℝ) ^ 2 / 8) := by
            gcongr; linarith [h8 t ht]
        _ = c₀ * k ^ n * (2 / δ ^ 2 * ((R : ℝ) ^ 2 / 8)) := by ring
        _ = c₀ * k ^ n * k := by
            congr 1; rw [hkdef]; field_simp; ring
        _ = c₀ * k ^ (n + 1) := by ring
  -- the limit
  have hk0 : 0 ≤ k := by positivity
  have hk8 : (R : ℝ) ^ 2 / (8 * δ ^ 2) < 1 :=
    lt_of_le_of_lt (div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)) hk
  have hRmem : (R : ℝ) ∈ Icc (0 : ℝ) R := ⟨hRpos, le_rfl⟩
  have hlim1 : Tendsto (fun n => pic F x₀ V n R) atTop (𝓝 (Y t₁)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (g := fun n => c₀ * k ^ n) (fun n => dist_nonneg) (fun n => ?_) ?_
    · rw [Real.dist_eq, abs_sub_comm, hR]; exact key n t₁ le_rfl
    · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hk0 hk).const_mul c₀
  exact tendsto_nhds_unique hlim1 (tendsto_pic_mark hF hk8 x₀ V hRmem)

end Flow

end Aux4

end Supp12

end InteractingSLE
