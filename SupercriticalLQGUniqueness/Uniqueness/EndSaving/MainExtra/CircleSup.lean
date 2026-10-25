import SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra.CircleUnif
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra.Cover
import LQGMetric.Papers.DZZ.S2ContBox
import LQGMetric.Papers.DFGPS.L3_4Tail




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra

open LQGMetric (DistC)
open LQGMetric.CircleAvg (incCov circCov)
open LQGMetric.SupTail (ferniqueBox ferniqueCF)

 

section Cov

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

theorem hasGaussianLaw_H (hH : LQGDimension.IsGFFCircleAverage H P) {r : ℝ} (hr : 0 < r)
    (z : ℂ) : HasGaussianLaw (H r z) P :=
  hH.isGaussianProcess.hasGaussianLaw_eval (⟨r, hr⟩, z)

 
theorem variance_sub_eq_incCov (hH : LQGDimension.IsGFFCircleAverage H P) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    Var[fun ω => H r z ω - H s w ω; P] = incCov z r w s z r w s := by
  have := hH.isProbabilityMeasure
  have hX := (hasGaussianLaw_H hH hr z).memLp_two
  have hY := (hasGaussianLaw_H hH hs w).memLp_two
  have hmX := (hasGaussianLaw_H hH hr z).aemeasurable
  have hmY := (hasGaussianLaw_H hH hs w).aemeasurable
  rw [variance_fun_sub hX hY, ← covariance_self hmX, ← covariance_self hmY,
    hH.covariance_eq r hr r hr, hH.covariance_eq r hr s hs, hH.covariance_eq s hs s hs,
    LQGMetric.CircleAvg.gffCircleCov_eq_incCov hr hr, LQGMetric.CircleAvg.gffCircleCov_eq_incCov hr hs,
    LQGMetric.CircleAvg.gffCircleCov_eq_incCov hs hs]
  have c1 := LQGMetric.CircleAvg.circCov_comm one_pos hr 0 z
  have c2 := LQGMetric.CircleAvg.circCov_comm one_pos hs 0 w
  have c3 := LQGMetric.CircleAvg.circCov_comm hs hr w z
  simp only [incCov]
  linarith

 
theorem integral_sq_H_sub_le (hH : LQGDimension.IsGFFCircleAverage H P) {r : ℝ} (hr : 0 < r)
    (u v : ℂ) : ∫ ω, (H r v ω - H r u ω) ^ 2 ∂P ≤ 2 / r * ‖u - v‖ := by
  have := hH.isProbabilityMeasure
  have hm : AEMeasurable (fun ω => H r v ω - H r u ω) P :=
    (hasGaussianLaw_H hH hr v).aemeasurable.sub (hasGaussianLaw_H hH hr u).aemeasurable
  have h0 : ∫ ω, (H r v ω - H r u ω) ∂P = 0 := by
    rw [integral_sub (hasGaussianLaw_H hH hr v).integrable (hasGaussianLaw_H hH hr u).integrable,
      hH.integral_eq_zero r hr v, hH.integral_eq_zero r hr u, sub_zero]
  rw [← variance_of_integral_eq_zero hm h0, variance_sub_eq_incCov hH hr hr]
  have := LQGMetric.CircleAvg.incCov_self_le hr hr v u
  rw [sub_self, abs_zero, zero_add, min_self, norm_sub_rev] at this
  calc incCov v r u r v r u r ≤ 2 * (‖u - v‖ / r) := this
    _ = 2 / r * ‖u - v‖ := by ring

end Cov

 

 

theorem quad_exponent_ge {lam K₀ C₆ : ℝ} (hlam : 0 ≤ lam) (hK₀ : 0 ≤ K₀) (hC₆ : 0 < C₆) :
    4 * lam - (3 * K₀ + 4 * C₆) ≤ (3 * lam - K₀) ^ 2 / (2 * (lam + C₆)) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg lam, sq_nonneg K₀, mul_nonneg hC₆.le (by positivity : (0 : ℝ) ≤ 3 * K₀ + 4 * C₆)]

 
theorem sup_tail_circleAvg :
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ t₀ ≤ 1 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (H : ℝ → ℂ → Ω → ℝ),
        LQGDimension.IsGFFCircleAverage H P →
        ∀ b r : ℝ, 0 < r → r ≤ t₀ * b →
          P {ω | ∃ z ∈ Metric.ball (0 : ℂ) (3 * b), 3 * Real.log (b / r) < |H r z ω - H b 0 ω|} ≤
            ENNReal.ofReal (C * (r / b) ^ 2) := by
  set K₀ : ℝ := ferniqueCF * √2 with hK₀
  set C₆ : ℝ := 2 * Real.log 7 with hC₆
  have hK₀0 : 0 < K₀ := mul_pos LQGMetric.SupTail.ferniqueCF_pos (by positivity)
  have hC₆0 : 0 < C₆ := by have := Real.log_pos (by norm_num : (1 : ℝ) < 7); positivity
  set t₀ : ℝ := Real.exp (-(K₀ / 3)) with ht₀
  have ht₀0 : 0 < t₀ := Real.exp_pos _
  have ht₀1 : t₀ ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  refine ⟨98 * Real.exp (3 * K₀ + 4 * C₆), t₀, by positivity, ht₀0, ht₀1, ?_⟩
  intro Ω _ P H hH b r hr hrb
  have := hH.isProbabilityMeasure
  have hb : 0 < b := by
    by_contra hb; push Not at hb; nlinarith
  set t : ℝ := r / b with ht
  have ht0 : 0 < t := div_pos hr hb
  have htt₀ : t ≤ t₀ := (div_le_iff₀ hb).2 (by linarith)
  have ht1 : t ≤ 1 := htt₀.trans ht₀1
  have hrb1 : r ≤ b := by have := (div_le_iff₀ hb).1 ht1; linarith
  set lam : ℝ := Real.log (b / r) with hlam
  have hlam_eq : lam = -Real.log t := by rw [hlam, ht, ← Real.log_inv, inv_div]
  have hlam0 : 0 ≤ lam := Real.log_nonneg ((one_le_div hr).2 hrb1)
  have hlamK : K₀ ≤ 3 * lam := by
    have : Real.log t ≤ -(K₀ / 3) := by
      rw [← Real.log_exp (-(K₀ / 3))]
      exact Real.log_le_log ht0 htt₀
    linarith
  
  set x₀ : ℂ := ⟨-(3 * b), -(3 * b)⟩ with hx₀
  set cl : ℂ → ℂ := LQGMetric.DZZ.boxClamp x₀ (6 * b) with hcl
  set G : ℂ → Ω → ℝ := fun v ω => H r (cl (v + x₀)) ω - H b 0 ω with hG
  have hclmem : ∀ v, ‖cl v‖ ≤ 6 * b := by
    intro v
    have hm := LQGMetric.DZZ.boxClamp_mem (x₀ := x₀) (by positivity : (0 : ℝ) ≤ 6 * b) v
    simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc, hx₀] at hm
    have h1 : |(cl v).re| ≤ 3 * b := abs_le.mpr ⟨by linarith [hm.1.1], by linarith [hm.1.2]⟩
    have h2 : |(cl v).im| ≤ 3 * b := abs_le.mpr ⟨by linarith [hm.2.1], by linarith [hm.2.2]⟩
    linarith [Complex.norm_le_abs_re_add_abs_im (cl v)]
  have hGP : IsGaussianProcess G P := by
    classical
    refine hH.isGaussianProcess.of_isGaussianProcess fun v => ?_
    refine ⟨{(⟨r, hr⟩, cl (v + x₀)), (⟨b, hb⟩, 0)},
      { toFun := fun x => x ⟨(⟨r, hr⟩, cl (v + x₀)), by simp⟩ - x ⟨(⟨b, hb⟩, 0), by simp⟩
        map_add' := fun x y => by simp only [Pi.add_apply]; ring
        map_smul' := fun c x => by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
      fun ω => ?_⟩
    simp [hG, Finset.restrict_def]
  have h0 : ∀ v, ∫ ω, G v ω ∂P = 0 := by
    intro v
    simp only [hG]
    rw [integral_sub (hasGaussianLaw_H hH hr _).integrable (hasGaussianLaw_H hH hb _).integrable,
      hH.integral_eq_zero r hr _, hH.integral_eq_zero b hb _, sub_zero]
  have hc : ∀ ω, Continuous fun v => G v ω := fun ω =>
    ((hH.continuous r hr ω).comp ((LQGMetric.DZZ.continuous_boxClamp x₀ (6 * b)).comp
      (continuous_id.add continuous_const))).sub continuous_const
  have hinc : ∀ u v : ℂ, ∫ ω, (G v ω - G u ω) ^ 2 ∂P ≤ 2 / r * ‖u - v‖ := by
    intro u v
    have e : ∀ ω, G v ω - G u ω = H r (cl (v + x₀)) ω - H r (cl (u + x₀)) ω := fun ω => by
      simp only [hG]; ring
    simp_rw [e]
    refine (integral_sq_H_sub_le hH hr _ _).trans ?_
    gcongr
    calc ‖cl (u + x₀) - cl (v + x₀)‖ ≤ ‖(u + x₀) - (v + x₀)‖ :=
          LQGMetric.DZZ.norm_boxClamp_sub_le _ _ _ _
      _ = ‖u - v‖ := by ring_nf
  have hvar : ∀ v, Var[G v; P] ≤ (√(lam + C₆)) ^ 2 := by
    intro v
    rw [Real.sq_sqrt (by positivity), show G v = fun ω => H r (cl (v + x₀)) ω - H b 0 ω from rfl,
      variance_sub_eq_incCov hH hr hb]
    have := LQGMetric.DFGPS.L34.incCov_far_le (cl (v + x₀)) hr hrb1 (R := 6) (by norm_num)
      (hclmem _)
    rw [hlam, hC₆]
    norm_num at this ⊢
    linarith
  set n : ℕ := ⌈6 * b / r⌉₊ with hn
  have hn6 : 6 * b / r ≤ n := Nat.le_ceil _
  have hnpos : 0 < n := Nat.ceil_pos.2 (by positivity)
  have hside : 6 * b / n ≤ r := by
    rw [div_le_iff₀ (by exact_mod_cast hnpos)]
    have := (div_le_iff₀ hr).1 hn6
    linarith
  set u : ℝ := 3 * lam - K₀ with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have htail := LQGMetric.SupTail.tail_iSup_abs_square hnpos (by positivity : 0 < 6 * b) hGP h0 hc
    (by positivity : (0 : ℝ) < 2 / r) hinc (Real.sqrt_pos.2 (by positivity)) hvar hu0
  
  have hthr : ferniqueCF * √(2 / r * (6 * b / n)) + u ≤ 3 * lam := by
    have hs : √(2 / r * (6 * b / n)) ≤ √2 := by
      apply Real.sqrt_le_sqrt
      calc 2 / r * (6 * b / n) ≤ 2 / r * r := by gcongr
        _ = 2 := by field_simp
    have := mul_le_mul_of_nonneg_left hs LQGMetric.SupTail.ferniqueCF_pos.le
    rw [hu, hK₀]
    linarith
  have hsub : {ω | ∃ z ∈ Metric.ball (0 : ℂ) (3 * b), 3 * Real.log (b / r) < |H r z ω - H b 0 ω|} ⊆
      {ω | ENNReal.ofReal (ferniqueCF * √(2 / r * (6 * b / n)) + u) ≤
        ⨆ x ∈ ferniqueBox 0 (6 * b), ENNReal.ofReal |G x ω|} := by
    intro ω ⟨z, hz, hzω⟩
    have hz3 : ‖z‖ < 3 * b := by simpa [dist_zero_right] using hz
    have hre : |z.re| < 3 * b := (Complex.abs_re_le_norm z).trans_lt hz3
    have him : |z.im| < 3 * b := (Complex.abs_im_le_norm z).trans_lt hz3
    rw [abs_lt] at hre him
    have hzB : z ∈ ferniqueBox x₀ (6 * b) := by
      simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc, hx₀]
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have hvB : z - x₀ ∈ ferniqueBox 0 (6 * b) := by
      simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc, hx₀, Complex.sub_re, Complex.sub_im,
        Complex.zero_re, Complex.zero_im, zero_add]
      refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    have hGz : G (z - x₀) ω = H r z ω - H b 0 ω := by
      simp only [hG, sub_add_cancel, hcl, LQGMetric.DZZ.boxClamp_of_mem hzB]
    show ENNReal.ofReal _ ≤ _
    refine le_trans ?_ (le_iSup₂ (f := fun x (_ : x ∈ ferniqueBox 0 (6 * b)) =>
      ENNReal.ofReal |G x ω|) (z - x₀) hvB)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hGz]
    rw [← hlam] at hzω
    linarith
  refine (measure_mono hsub).trans (htail.trans (ENNReal.ofReal_le_ofReal ?_))
  
  have hn7 : (n : ℝ) ≤ 7 / t := by
    have h1 : (n : ℝ) < 6 * b / r + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 6 * b / r = 6 / t := by rw [ht]; field_simp
    have h3 : (1 : ℝ) ≤ 1 / t := by rw [le_div_iff₀ ht0]; linarith
    rw [h2] at h1
    have : 7 / t = 6 / t + 1 / t := by ring
    linarith
  have hexp : Real.exp (-u ^ 2 / (2 * (√(lam + C₆)) ^ 2)) ≤
      Real.exp (3 * K₀ + 4 * C₆) * t ^ 4 := by
    rw [Real.sq_sqrt (by positivity), neg_div]
    have hq := quad_exponent_ge hlam0 hK₀0.le hC₆0
    have ht4 : t ^ 4 = Real.exp (-(4 * lam)) := by
      rw [hlam_eq, mul_neg, neg_neg, ← Real.rpow_natCast, Real.rpow_def_of_pos ht0]
      congr 1
      push_cast
      ring
    rw [ht4, ← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [hu]
    linarith
  calc 2 * (n : ℝ) ^ 2 * Real.exp (-u ^ 2 / (2 * (√(lam + C₆)) ^ 2))
      ≤ 2 * (7 / t) ^ 2 * (Real.exp (3 * K₀ + 4 * C₆) * t ^ 4) := by
        gcongr
    _ = 98 * Real.exp (3 * K₀ + 4 * C₆) * t ^ 2 := by field_simp; ring
    _ = 98 * Real.exp (3 * K₀ + 4 * C₆) * (r / b) ^ 2 := by rw [ht]

 

 

theorem card_radii_le {S : Set ℝ} {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hsep : ∀ ⦃x y : ℝ⦄, x ∈ S → y ∈ S → x < y → 8 * x ≤ y) (hS : S ⊆ Set.Icc a c) :
    S.Finite ∧ ∀ hfin : S.Finite,
      (hfin.toFinset.card : ℝ) ≤ Real.logb 8 (c / a) + 2 := by
  classical
  set f : ℝ → ℤ := fun x => ⌊Real.logb 8 x⌋ with hf
  have hstep : ∀ ⦃x y : ℝ⦄, x ∈ S → y ∈ S → x < y → f x < f y := by
    intro x y hx hy hlt
    have h8 := hsep hx hy hlt
    have hx0 : 0 < x := ha.trans_le (hS hx).1
    have hl : Real.logb 8 x + 1 ≤ Real.logb 8 y := by
      have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 8) (by positivity) h8
      rwa [Real.logb_mul (by norm_num) hx0.ne', Real.logb_self_eq_one (by norm_num), add_comm]
        at hlog
    have hfl := Int.floor_le_floor hl
    rw [Int.floor_add_one] at hfl
    simp only [hf]
    omega
  have hinj : Set.InjOn f S := by
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (hstep hx hy hlt).ne hxy
    · exact (hstep hy hx hlt).ne hxy.symm
  have himg : f '' S ⊆ Set.Icc ⌊Real.logb 8 a⌋ ⌊Real.logb 8 c⌋ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx0 : 0 < x := ha.trans_le (hS hx).1
    exact ⟨Int.floor_le_floor (Real.logb_le_logb_of_le (by norm_num) ha (hS hx).1),
      Int.floor_le_floor (Real.logb_le_logb_of_le (by norm_num) hx0 (hS hx).2)⟩
  have hfin : S.Finite := Set.Finite.of_finite_image ((Set.finite_Icc _ _).subset himg) hinj
  refine ⟨hfin, fun hfin' => ?_⟩
  have hcard : hfin'.toFinset.card ≤ (Finset.Icc ⌊Real.logb 8 a⌋ ⌊Real.logb 8 c⌋).card := by
    refine Finset.card_le_card_of_injOn f (fun x hx => ?_) (fun x hx y hy hxy => ?_)
    · exact Finset.mem_Icc.mpr (himg ⟨x, hfin'.mem_toFinset.mp hx, rfl⟩)
    · exact hinj (hfin'.mem_toFinset.mp hx) (hfin'.mem_toFinset.mp hy) hxy
  rw [Int.card_Icc] at hcard
  have hc0 : 0 < c := ha.trans_le hac
  have hle : ⌊Real.logb 8 a⌋ ≤ ⌊Real.logb 8 c⌋ :=
    Int.floor_le_floor (Real.logb_le_logb_of_le (by norm_num) ha hac)
  have h1 : ((⌊Real.logb 8 c⌋ + 1 - ⌊Real.logb 8 a⌋).toNat : ℝ) ≤
      Real.logb 8 c - Real.logb 8 a + 2 := by
    have hfc := Int.floor_le (Real.logb 8 c)
    have hfa' := Int.lt_floor_add_one (Real.logb 8 a)
    have hnn : 0 ≤ ⌊Real.logb 8 c⌋ + 1 - ⌊Real.logb 8 a⌋ := by omega
    have e : (((⌊Real.logb 8 c⌋ + 1 - ⌊Real.logb 8 a⌋).toNat : ℤ) : ℝ) =
        ((⌊Real.logb 8 c⌋ + 1 - ⌊Real.logb 8 a⌋ : ℤ) : ℝ) := by
      rw [Int.toNat_of_nonneg hnn]
    have e2 : (((⌊Real.logb 8 c⌋ + 1 - ⌊Real.logb 8 a⌋).toNat : ℕ) : ℝ) =
        (((⌊Real.logb 8 c⌋ + 1 - ⌊Real.logb 8 a⌋).toNat : ℤ) : ℝ) := by norm_cast
    rw [e2, e]
    push_cast
    linarith
  rw [Real.logb_div hc0.ne' ha.ne']
  calc (hfin'.toFinset.card : ℝ) ≤ ((⌊Real.logb 8 c⌋ + 1 - ⌊Real.logb 8 a⌋).toNat : ℝ) := by
        exact_mod_cast hcard
    _ ≤ _ := h1

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra
