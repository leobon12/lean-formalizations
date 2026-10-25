import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Site
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.LowDet
import SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Gauss




 
























set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails

open LQGMetric (DistC)

 
def nrm (ξ Q : ℝ) (g : DistC) (s : ℝ) (w : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (s ^ (ξ * Q) * Real.exp (ξ * LQGMetric.circleAvg g s w))

theorem nrm_eq_normalizer (C : Objects.CorrectedEvent.Constants) (g : DistC) (s : ℝ) (w : ℂ) :
    nrm C.ξ C.Q g s w = Objects.CorrectedEvent.normalizer C g s w := rfl

 
theorem zpow16_neg_eq_exp (j : ℕ) : (16 : ℝ) ^ (-(j : ℤ)) = Real.exp (-(j : ℝ) * Real.log 16) := by
  rw [zpow_neg, zpow_natCast, neg_mul, Real.exp_neg, mul_comm, Real.exp_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 16), Real.rpow_natCast]

 
theorem goodAnn_across_lower {ξ : Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric} {M : ℝ}
    {w : ℂ} {t : Ioi (0 : ℝ)} {g : DistC} (hg : g ∈ goodAnn ξ Q D M w t) :
    ENNReal.ofReal (M⁻¹ * ((t : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * LQGMetric.circleAvg g t w))) ≤
      acrossDist (D g) (ann12 w t) := by
  have ht : (0 : ℝ) < t := t.2
  set c : ℝ := (t : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg g t w))
    with hc
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  have h1 : ENNReal.ofReal M⁻¹ ≤ ENNReal.ofReal c * acrossDist (D g) (ann12 w t) := hg.1
  have h2 := (ENNReal.ofReal_div_of_pos hc0).symm ▸ (ENNReal.div_le_iff_le_mul
    (Or.inl (ENNReal.ofReal_pos.mpr hc0).ne') (Or.inl ENNReal.ofReal_ne_top)).2
    (by rw [mul_comm]; exact h1)
  refine le_of_eq_of_le ?_ h2
  congr 1
  rw [hc, div_eq_mul_inv, mul_inv, Real.rpow_neg ht.le, inv_inv, ← Real.exp_neg, neg_neg]

 
theorem goodAnn_around_upper {ξ : Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric} {M : ℝ}
    {w : ℂ} {t : Ioi (0 : ℝ)} {g : DistC} (hg : g ∈ goodAnn ξ Q D M w t) :
    aroundDist (D g) (ann12 w t) ≤
      ENNReal.ofReal (M * ((t : ℝ) ^ ((ξ : ℝ) * Q) *
        Real.exp ((ξ : ℝ) * LQGMetric.circleAvg g t w))) := by
  have ht : (0 : ℝ) < t := t.2
  set c : ℝ := (t : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg g t w))
    with hc
  have hc0 : 0 < c := mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  have h1 : ENNReal.ofReal c * aroundDist (D g) (ann12 w t) ≤ ENNReal.ofReal M := hg.2
  have h2 : aroundDist (D g) (ann12 w t) ≤ ENNReal.ofReal (M / c) := by
    rw [ENNReal.ofReal_div_of_pos hc0, ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_pos.mpr hc0).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h1
  refine h2.trans_eq ?_
  congr 1
  rw [hc, div_eq_mul_inv, mul_inv, Real.rpow_neg ht.le, inv_inv, ← Real.exp_neg, neg_neg]

 


theorem lower_scale_arith {ξ Q M lam q s : ℝ} {n j : ℕ} (hξ : 0 < ξ) (hQ : 0 < Q)
    (hM : 0 < M) (hMn : Real.log M ≤ n * lam) (hlam : 0 < lam) (hs : 0 < s) (hj : j ≤ 2 * n)
    {ht hs' : ℝ} (hgap : |ht - hs'| < q * n * lam) :
    Real.exp (-(n * lam * (1 + 2 * ξ * Q + ξ * q))) * (s ^ (ξ * Q) * Real.exp (ξ * hs')) ≤
      M⁻¹ * ((Real.exp (-(j : ℝ) * lam) * s) ^ (ξ * Q) * Real.exp (ξ * ht)) := by
  have hpow : (Real.exp (-(j : ℝ) * lam) * s) ^ (ξ * Q) =
      Real.exp (-(j : ℝ) * lam * (ξ * Q)) * s ^ (ξ * Q) := by
    rw [Real.mul_rpow (Real.exp_pos _).le hs.le, ← Real.exp_mul]
  have hj' : (j : ℝ) ≤ 2 * n := by exact_mod_cast hj
  have hgap' : ht - hs' > -(q * n * lam) := by
    have := (abs_lt.1 hgap).1
    linarith
  have hMinv : M⁻¹ = Real.exp (-Real.log M) := by rw [Real.exp_neg, Real.exp_log hM]
  rw [hpow, hMinv]
  have hspos : 0 < s ^ (ξ * Q) := Real.rpow_pos_of_pos hs _
  have key : -(n * lam * (1 + 2 * ξ * Q + ξ * q)) + ξ * hs' ≤
      -Real.log M + (-(j : ℝ) * lam * (ξ * Q) + ξ * ht) := by
    have h1 : -(n * lam) ≤ -Real.log M := by linarith
    have h2 : -(2 * n * lam * (ξ * Q)) ≤ -(j : ℝ) * lam * (ξ * Q) := by
      have : (j : ℝ) * lam * (ξ * Q) ≤ 2 * n * lam * (ξ * Q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hj' hlam.le)
          (mul_pos hξ hQ).le
      linarith
    have h3 : ξ * hs' - ξ * q * n * lam ≤ ξ * ht := by
      have : ξ * (ht - hs') ≥ ξ * (-(q * n * lam)) := by
        exact mul_le_mul_of_nonneg_left hgap'.le hξ.le
      nlinarith
    nlinarith
  calc Real.exp (-(n * lam * (1 + 2 * ξ * Q + ξ * q))) * (s ^ (ξ * Q) * Real.exp (ξ * hs'))
      = s ^ (ξ * Q) * Real.exp (-(n * lam * (1 + 2 * ξ * Q + ξ * q)) + ξ * hs') := by
        rw [Real.exp_add]
        ring
    _ ≤ s ^ (ξ * Q) * Real.exp (-Real.log M + (-(j : ℝ) * lam * (ξ * Q) + ξ * ht)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr key) hspos.le
    _ = Real.exp (-Real.log M) * (Real.exp (-(j : ℝ) * lam * (ξ * Q)) * s ^ (ξ * Q) *
          Real.exp (ξ * ht)) := by
        rw [Real.exp_add, Real.exp_add]
        ring

 
theorem sum_const_ofReal {α : Type*} (S : Finset α) (A : ℝ) :
    ∑ _x ∈ S, ENNReal.ofReal A = ENNReal.ofReal (S.card * A) := by
  rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]

 
theorem succ_le_exp_log16 (n : ℕ) : (n : ℝ) + 1 ≤ Real.exp (n * Real.log 16) := by
  rw [show (n : ℝ) * Real.log 16 = Real.log ((16 : ℝ) ^ n) by
    rw [Real.log_pow], Real.exp_log (by positivity)]
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 15 by norm_num) n
  norm_num at h
  have : (n : ℝ) ≤ 15 * n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  linarith

 
theorem eventually_dyadic_conditions {g L₁ L₂ lam : ℝ} (hg : 0 < g) (hlam : 0 < lam) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ 4 * Real.exp (-(n * lam)) < g ∧ L₁ ≤ n * lam ∧ L₂ ≤ n * lam := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n * lam))) atTop (𝓝 0) := by
    have hpow : (fun n : ℕ => Real.exp (-(n * lam))) = fun n : ℕ => (Real.exp (-lam)) ^ n := by
      funext n
      rw [← Real.exp_nat_mul]
      ring_nf
    rw [hpow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by linarith))
  have hlin : Tendsto (fun n : ℕ => (n : ℝ) * lam) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hlam
  filter_upwards [eventually_ge_atTop 1, hexp.eventually (gt_mem_nhds (by linarith : 0 < g / 4)),
    hlin.eventually_ge_atTop L₁, hlin.eventually_ge_atTop L₂] with n h1 h2 h3 h4
  exact ⟨h1, by linarith, h3, h4⟩

 
theorem scale16_eq_exp (s : Ioi (0 : ℝ)) (j : ℕ) :
    (scale16 s j : ℝ) = Real.exp (-(j : ℝ) * Real.log 16) * s := by
  rw [scale16_val, zpow16_neg_eq_exp]

 
theorem scale16_mem_bounds (s : Ioi (0 : ℝ)) {n j : ℕ} (hnj : n ≤ j) (hj : j ≤ 2 * n) :
    Real.exp (-(2 * n * Real.log 16)) * s ≤ (scale16 s j : ℝ) ∧
      (scale16 s j : ℝ) ≤ Real.exp (-(n * Real.log 16)) * s := by
  have hs : (0 : ℝ) < s := s.2
  have hlam : 0 < Real.log 16 := Real.log_pos (by norm_num)
  have hnj' : (n : ℝ) ≤ j := by exact_mod_cast hnj
  have hj' : (j : ℝ) ≤ 2 * n := by exact_mod_cast hj
  rw [scale16_eq_exp]
  constructor
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hs.le
    have := mul_le_mul_of_nonneg_right hj' hlam.le
    linarith
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hs.le
    have := mul_le_mul_of_nonneg_right hnj' hlam.le
    linarith

 


theorem acr_lower_of_good (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {M q : ℝ} (hM0 : 0 < M) {n : ℕ}
    (hgeo : 4 * Real.exp (-(n * Real.log 16)) < b - a)
    (hMn : Real.log M ≤ n * Real.log 16) (s : Ioi (0 : ℝ)) (y : ℂ) {Nm : ℕ} (hNm0 : 0 < Nm)
    (hNmgt : Real.pi * ((a + b) / 2) * Real.exp (2 * n * Real.log 16) < Nm) (g : DistC)
    (hgood : ∀ w ∈ gridSet y ((a + b) / 2 * s) Nm, ∃ j ∈ Finset.Icc n (2 * n),
      g ∈ goodAnn ξ Q D M w (scale16 s j))
    (hgap : ∀ w ∈ gridSet y ((a + b) / 2 * s) Nm, ∀ j ∈ Finset.Icc n (2 * n),
      |LQGMetric.circleAvg g (scale16 s j) w - LQGMetric.circleAvg g s y| <
        q * n * Real.log 16) :
    ENNReal.ofReal (Real.exp (-(n * Real.log 16 * (1 + 2 * ξ * Q + ξ * q)))) * nrm ξ Q g s y ≤
      Objects.CorrectedEvent.acr (D g) y (a * s) (b * s) := by
  set lam : ℝ := Real.log 16 with hlamdef
  have hlam : 0 < lam := Real.log_pos (by norm_num)
  have hξ : (0 : ℝ) < ξ := ξ.2
  have hs : (0 : ℝ) < s := s.2
  set m : ℝ := (a + b) / 2 with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  set W : Finset ℂ := gridSet y (m * s) Nm with hWdef
  choose! jw hjwJ hjwG using hgood
  let t : ℂ → Ioi (0 : ℝ) := fun w => scale16 s (jw w)
  have hbounds : ∀ w ∈ W, Real.exp (-(2 * n * lam)) * s ≤ (t w : ℝ) ∧
      (t w : ℝ) ≤ Real.exp (-(n * lam)) * s := fun w hw =>
    scale16_mem_bounds s (Finset.mem_Icc.1 (hjwJ w hw)).1 (Finset.mem_Icc.1 (hjwJ w hw)).2
  have hcov : ∀ x ∈ sphere y (m * s), ∃ w ∈ W, dist x w < t w := by
    intro x hx
    obtain ⟨w, hwW, hdw⟩ := exists_gridSet_near y (mul_pos hm0 hs) hNm0 (mem_sphere.1 hx)
    refine ⟨w, hwW, lt_of_le_of_lt hdw (lt_of_lt_of_le ?_ (hbounds w hwW).1)⟩
    rw [div_lt_iff₀ (by exact_mod_cast hNm0)]
    have hE : Real.exp (-(2 * n * lam)) * Real.exp (2 * n * lam) = 1 := by
      rw [← Real.exp_add]; simp
    have hprod : 0 < Real.exp (-(2 * n * lam)) * s := mul_pos (Real.exp_pos _) hs
    calc Real.pi * (m * s) = Real.pi * m * Real.exp (2 * n * lam) *
          (Real.exp (-(2 * n * lam)) * s) := by
          rw [show Real.pi * m * Real.exp (2 * n * lam) * (Real.exp (-(2 * n * lam)) * s) =
            Real.pi * m * s * (Real.exp (-(2 * n * lam)) * Real.exp (2 * n * lam)) by ring, hE]
          ring
      _ < Nm * (Real.exp (-(2 * n * lam)) * s) := mul_lt_mul_of_pos_right hNmgt hprod
      _ = Real.exp (-(2 * n * lam)) * s * Nm := by ring
  have hin : ∀ w ∈ W, closedBall w (2 * t w) ⊆ Objects.CorrectedEvent.ann y (a * s) (b * s) := by
    intro w hw x hx
    have hwy : dist w y = m * s := mem_gridSet_dist y (mul_pos hm0 hs).le Nm hw
    have hxw : dist x w ≤ 2 * t w := mem_closedBall.1 hx
    have ht2 : 2 * (t w : ℝ) < (b - a) / 2 * s := by
      have h1 := (hbounds w hw).2
      have h2 : 2 * (Real.exp (-(n * lam)) * s) < (b - a) / 2 * s := by
        have := mul_lt_mul_of_pos_right hgeo hs
        linarith
      linarith
    have hm : m * s = a * s + (b - a) / 2 * s := by rw [hmdef]; ring
    have hm' : m * s = b * s - (b - a) / 2 * s := by rw [hmdef]; ring
    constructor
    · have := dist_triangle w x y
      rw [dist_comm w x] at this
      linarith
    · have := dist_triangle x w y
      linarith
  have hX : ∀ w ∈ W, ENNReal.ofReal (Real.exp (-(n * lam * (1 + 2 * ξ * Q + ξ * q)))) *
      nrm ξ Q g s y ≤ acrossDist (D g) (ann12 w (t w)) := by
    intro w hw
    refine le_trans ?_ (goodAnn_across_lower (hjwG w hw))
    rw [nrm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hj := (Finset.mem_Icc.1 (hjwJ w hw)).2
    have harith := lower_scale_arith (ξ := (ξ : ℝ)) (Q := Q) (M := M) (lam := lam) (q := q)
      (s := s) (n := n) (j := jw w) hξ hQ hM0 hMn hlam hs hj (hgap w hw (jw w) (hjwJ w hw))
    rw [← scale16_eq_exp s (jw w)] at harith
    exact harith
  have h₁ : a * s < m * s := by rw [hmdef]; nlinarith
  have h₂ : m * s < b * s := by rw [hmdef]; nlinarith
  exact acr_ge_of_cover (D g) h₁ h₂ W t _ hcov hin hX

 


theorem gauss_pair_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : LQGMetric.IsWholePlaneGFF h P) {κ m : ℝ} (hκ : 0 < κ) (hm0 : 0 < m) {n j : ℕ}
    (hn1 : 1 ≤ n) (hnj : n ≤ j) (hj : j ≤ 2 * n)
    (hvarn : 2 * Real.log (m + 1) ≤ n * Real.log 16) (s : Ioi (0 : ℝ)) {w y : ℂ}
    (hwy : dist w y = m * s) :
    P {ω | Real.sqrt (6 * (κ + 3)) * n * Real.log 16 ≤
        |LQGMetric.circleAvg (h ω) (scale16 s j) w - LQGMetric.circleAvg (h ω) s y|} ≤
      ENNReal.ofReal (2 * Real.exp (-((κ + 3) * n * Real.log 16))) := by
  set lam : ℝ := Real.log 16 with hlamdef
  have hlam : 0 < lam := Real.log_pos (by norm_num)
  have hs : (0 : ℝ) < s := s.2
  set q : ℝ := Real.sqrt (6 * (κ + 3)) with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.2 (by linarith)
  have hq2 : q ^ 2 = 6 * (κ + 3) := Real.sq_sqrt (by linarith)
  have hnpos : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hjpos : (1 : ℝ) ≤ j := by exact_mod_cast le_trans hn1 hnj
  have hj' : (j : ℝ) ≤ 2 * n := by exact_mod_cast hj
  have hts : (scale16 s j : ℝ) ≤ s := by
    rw [scale16_eq_exp]
    have : Real.exp (-(j : ℝ) * lam) ≤ 1 := Real.exp_le_one_iff.2 (by
      have := mul_pos (by linarith : (0 : ℝ) < j) hlam
      linarith)
    calc Real.exp (-(j : ℝ) * lam) * s ≤ 1 * s := mul_le_mul_of_nonneg_right this hs.le
      _ = s := one_mul _
  have hlogst : Real.log (s / scale16 s j) = j * lam := by
    rw [scale16_eq_exp, div_mul_eq_div_div_swap, div_self hs.ne', one_div, ← Real.exp_neg,
      Real.log_exp]
    ring
  have hlogm : 0 ≤ Real.log (m + 1) := Real.log_nonneg (by linarith)
  have hjl : 0 < (j : ℝ) * lam := mul_pos (by linarith) hlam
  have hV : 0 < Real.log (s / scale16 s j) + 2 * Real.log (m + 1) := by
    rw [hlogst]
    linarith
  have hpos : (0 : ℝ) < (scale16 s j : ℝ) := (scale16 s j).2
  have hwy' : ‖w - y‖ ≤ m * s := by rw [← dist_eq_norm, hwy]
  have hxn : 0 < q * n * lam := mul_pos (mul_pos hq0 (by linarith)) hlam
  have hT := circleAvg_inc_tail (a := (scale16 s j : ℝ)) (s := (s : ℝ)) (R := m) hh hpos hts
    hm0.le w y hwy' hV hxn
  refine hT.trans (ENNReal.ofReal_le_ofReal ?_)
  have hVle : 2 * (Real.log (s / scale16 s j) + 2 * Real.log (m + 1)) ≤ 6 * n * lam := by
    rw [hlogst]
    have := mul_le_mul_of_nonneg_right hj' hlam.le
    linarith
  have hexp : -(q * n * lam) ^ 2 / (2 * (Real.log (s / scale16 s j) + 2 * Real.log (m + 1))) ≤
      -((κ + 3) * n * lam) := by
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have hxn2 : (q * n * lam) ^ 2 = 6 * (κ + 3) * n * lam * (n * lam) := by
      rw [mul_pow, mul_pow, hq2]
      ring
    rw [hxn2]
    have hk : 0 ≤ (κ + 3) * n * lam := by positivity
    calc (κ + 3) * n * lam * (2 * (Real.log (s / scale16 s j) + 2 * Real.log (m + 1)))
        ≤ (κ + 3) * n * lam * (6 * n * lam) := mul_le_mul_of_nonneg_left hVle hk
      _ = 6 * (κ + 3) * n * lam * (n * lam) := by ring
  have := Real.exp_le_exp.mpr hexp
  linarith

 
theorem dyadic_sum_bound {κ c K Wc : ℝ} (hκ : 0 < κ) (hc : 0 ≤ c) (hK : 0 ≤ K) {n : ℕ}
    (hW : Wc ≤ K * Real.exp (2 * n * Real.log 16)) :
    Wc * (c * Real.exp (-((κ + 2) * Real.log 16) * (n + 1))) +
        Wc * ((n + 1) * (2 * Real.exp (-((κ + 3) * n * Real.log 16)))) ≤
      K * (c + 2) * Real.exp (-(κ * n * Real.log 16)) := by
  set lam : ℝ := Real.log 16 with hlamdef
  have hlam : 0 < lam := Real.log_pos (by norm_num)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE1 : Real.exp (2 * n * lam) * Real.exp (-((κ + 2) * lam) * (n + 1)) ≤
      Real.exp (-(κ * n * lam)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (κ + 2) * lam := by positivity
    nlinarith
  have hE2 : Real.exp (2 * n * lam) * ((n + 1) * Real.exp (-((κ + 3) * n * lam))) ≤
      Real.exp (-(κ * n * lam)) := by
    have hs1 := succ_le_exp_log16 n
    calc Real.exp (2 * n * lam) * ((n + 1) * Real.exp (-((κ + 3) * n * lam)))
        ≤ Real.exp (2 * n * lam) * (Real.exp (n * lam) * Real.exp (-((κ + 3) * n * lam))) := by
          gcongr
      _ = Real.exp (-(κ * n * lam)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
  have hA : Wc * (c * Real.exp (-((κ + 2) * lam) * (n + 1))) ≤
      K * c * Real.exp (-(κ * n * lam)) := by
    calc Wc * (c * Real.exp (-((κ + 2) * lam) * (n + 1)))
        ≤ K * Real.exp (2 * n * lam) * (c * Real.exp (-((κ + 2) * lam) * (n + 1))) := by gcongr
      _ = K * c * (Real.exp (2 * n * lam) * Real.exp (-((κ + 2) * lam) * (n + 1))) := by ring
      _ ≤ K * c * Real.exp (-(κ * n * lam)) := by gcongr
  have hB : Wc * ((n + 1) * (2 * Real.exp (-((κ + 3) * n * lam)))) ≤
      K * 2 * Real.exp (-(κ * n * lam)) := by
    calc Wc * ((n + 1) * (2 * Real.exp (-((κ + 3) * n * lam))))
        ≤ K * Real.exp (2 * n * lam) * ((n + 1) * (2 * Real.exp (-((κ + 3) * n * lam)))) := by
          gcongr
      _ = K * 2 * (Real.exp (2 * n * lam) * ((n + 1) * Real.exp (-((κ + 3) * n * lam)))) := by
          ring
      _ ≤ K * 2 * Real.exp (-(κ * n * lam)) := by gcongr
  calc Wc * (c * Real.exp (-((κ + 2) * lam) * (n + 1))) +
        Wc * ((n + 1) * (2 * Real.exp (-((κ + 3) * n * lam))))
      ≤ K * c * Real.exp (-(κ * n * lam)) + K * 2 * Real.exp (-(κ * n * lam)) := add_le_add hA hB
    _ = K * (c + 2) * Real.exp (-(κ * n * lam)) := by ring

 
theorem mesh_card_bound (m : ℝ) (hm0 : 0 < m) (n : ℕ) (z : ℂ) (r : ℝ) :
    let Nm : ℕ := ⌈Real.pi * m * Real.exp (2 * n * Real.log 16)⌉₊ + 1
    0 < Nm ∧ Real.pi * m * Real.exp (2 * n * Real.log 16) < Nm ∧
      ((gridSet z r Nm).card : ℝ) ≤ (Real.pi * m + 3) * Real.exp (2 * n * Real.log 16) := by
  intro Nm
  have hX : 0 ≤ Real.pi * m * Real.exp (2 * n * Real.log 16) := by positivity
  have hceil := Nat.le_ceil (Real.pi * m * Real.exp (2 * n * Real.log 16))
  have hceil2 := Nat.ceil_lt_add_one hX
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · change Real.pi * m * Real.exp (2 * n * Real.log 16) <
      ((⌈Real.pi * m * Real.exp (2 * n * Real.log 16)⌉₊ + 1 : ℕ) : ℝ)
    push_cast
    linarith
  · have h1 : ((gridSet z r Nm).card : ℝ) ≤ Nm + 1 := by exact_mod_cast card_gridSet_le z r Nm
    have h2 : (Nm : ℝ) ≤ Real.pi * m * Real.exp (2 * n * Real.log 16) + 2 := by
      change ((⌈Real.pi * m * Real.exp (2 * n * Real.log 16)⌉₊ + 1 : ℕ) : ℝ) ≤ _
      push_cast
      linarith
    have h3 : (1 : ℝ) ≤ Real.exp (2 * n * Real.log 16) :=
      Real.one_le_exp (by positivity)
    have h4 : Real.pi * m * Real.exp (2 * n * Real.log 16) + 3 ≤
        (Real.pi * m + 3) * Real.exp (2 * n * Real.log 16) := by
      have : 0 ≤ Real.pi * m := by positivity
      nlinarith
    linarith

 



theorem acr_lower_tail_dyadic (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {a b : ℝ} (ha : 0 < a) (hab : a < b) (κ : ℝ) (hκ : 0 < κ) :
    ∃ (n₀ : ℕ) (C : ℝ), 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ n : ℕ, n₀ ≤ n → ∀ (s : Ioi (0 : ℝ)) (y : ℂ),
          P {ω | Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) <
              ENNReal.ofReal (Real.exp (-(n * Real.log 16 *
                (1 + 2 * ξ * Q + ξ * Real.sqrt (6 * (κ + 3)))))) * nrm ξ Q (h ω) s y} ≤
            ENNReal.ofReal (C * Real.exp (-(κ * n * Real.log 16))) := by
  have hlam : 0 < Real.log 16 := Real.log_pos (by norm_num)
  set m : ℝ := (a + b) / 2 with hmdef
  have hm0 : 0 < m := by rw [hmdef]; linarith
  obtain ⟨M, c, hM1, hc0, hgood⟩ :=
    goodAnn_no_good_scale ξ Q hQ D hD ((κ + 2) * Real.log 16) (by positivity)
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM1
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (eventually_dyadic_conditions (g := b - a) (L₁ := 2 * Real.log (m + 1)) (L₂ := Real.log M)
      (by linarith) hlam)
  refine ⟨n₀, (Real.pi * m + 3) * (c + 2), by positivity, ?_⟩
  intro Ω _ P _ h hh n hn s y
  obtain ⟨hn1, hgeo, hvarn, hMn⟩ := hn₀ n hn
  have hs : (0 : ℝ) < s := s.2
  obtain ⟨hNm0, hNmgt, hcardW⟩ := mesh_card_bound m hm0 n y (m * s)
  set Nm : ℕ := ⌈Real.pi * m * Real.exp (2 * n * Real.log 16)⌉₊ + 1 with hNmdef
  set W : Finset ℂ := gridSet y (m * s) Nm with hWdef
  set J : Finset ℕ := Finset.Icc n (2 * n) with hJdef
  have hJne : J.Nonempty := ⟨n, Finset.mem_Icc.2 ⟨le_rfl, by omega⟩⟩
  have hJ1 : ∀ j ∈ J, 1 ≤ j := fun j hj => le_trans hn1 (Finset.mem_Icc.1 hj).1
  have hJcard : J.card = n + 1 := by rw [hJdef, Nat.card_Icc]; omega
  set q : ℝ := Real.sqrt (6 * (κ + 3)) with hqdef
  let F : ℂ → Set Ω := fun w => {ω | ∀ j ∈ J, h ω ∉ goodAnn ξ Q D M w (scale16 s j)}
  let G : ℂ → ℕ → Set Ω := fun w j => {ω | q * n * Real.log 16 ≤
    |LQGMetric.circleAvg (h ω) (scale16 s j) w - LQGMetric.circleAvg (h ω) s y|}
  have hsub : {ω | Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) <
      ENNReal.ofReal (Real.exp (-(n * Real.log 16 * (1 + 2 * ξ * Q + ξ * q)))) *
        nrm ξ Q (h ω) s y} ⊆ (⋃ w ∈ W, F w) ∪ ⋃ w ∈ W, ⋃ j ∈ J, G w j := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_iUnion₂, not_or, not_exists] at hno
    obtain ⟨hnoF, hnoG⟩ := hno
    have hch : ∀ w ∈ W, ∃ j ∈ J, h ω ∈ goodAnn ξ Q D M w (scale16 s j) := by
      intro w hw
      by_contra hc
      push Not at hc
      exact hnoF w hw hc
    have hgap : ∀ w ∈ W, ∀ j ∈ J, |LQGMetric.circleAvg (h ω) (scale16 s j) w -
        LQGMetric.circleAvg (h ω) s y| < q * n * Real.log 16 := by
      intro w hw j hj
      have := hnoG w hw j hj
      simp only [G, mem_ofPred_eq, not_le] at this
      exact this
    exact absurd hω (not_lt.2 (acr_lower_of_good ξ Q hQ D ha hab hM0 hgeo hMn s y hNm0
      (by rw [← hmdef]; exact hNmgt) (h ω) hch hgap))
  have hF : ∀ w, P (F w) ≤ ENNReal.ofReal (c * Real.exp (-((κ + 2) * Real.log 16) * (n + 1))) := by
    intro w
    have := hgood P h hh w s J hJne hJ1
    rw [hJcard] at this
    push_cast at this
    exact this
  have hGb : ∀ w ∈ W, ∀ j ∈ J, P (G w j) ≤
      ENNReal.ofReal (2 * Real.exp (-((κ + 3) * n * Real.log 16))) := by
    intro w hw j hj
    have hjn := Finset.mem_Icc.1 hj
    exact gauss_pair_bound hh.1 hκ hm0 hn1 hjn.1 hjn.2 hvarn s
      (mem_gridSet_dist y (mul_pos hm0 hs).le Nm hw)
  have hsum := dyadic_sum_bound hκ hc0.le (by positivity : (0 : ℝ) ≤ Real.pi * m + 3)
    (n := n) hcardW
  calc P {ω | Objects.CorrectedEvent.acr (D (h ω)) y (a * s) (b * s) <
        ENNReal.ofReal (Real.exp (-(n * Real.log 16 * (1 + 2 * ξ * Q + ξ * q)))) *
          nrm ξ Q (h ω) s y}
      ≤ P ((⋃ w ∈ W, F w) ∪ ⋃ w ∈ W, ⋃ j ∈ J, G w j) := measure_mono hsub
    _ ≤ P (⋃ w ∈ W, F w) + P (⋃ w ∈ W, ⋃ j ∈ J, G w j) := measure_union_le _ _
    _ ≤ ∑ w ∈ W, P (F w) + ∑ w ∈ W, ∑ j ∈ J, P (G w j) := by
        gcongr
        · exact measure_biUnion_finset_le _ _
        · refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
          exact measure_biUnion_finset_le _ _
    _ ≤ ∑ _w ∈ W, ENNReal.ofReal (c * Real.exp (-((κ + 2) * Real.log 16) * (n + 1))) +
          ∑ w ∈ W, ∑ _j ∈ J, ENNReal.ofReal (2 * Real.exp (-((κ + 3) * n * Real.log 16))) :=
        add_le_add (Finset.sum_le_sum fun w _ => hF w)
          (Finset.sum_le_sum fun w hw => Finset.sum_le_sum fun j hj => hGb w hw j hj)
    _ = ENNReal.ofReal (W.card * (c * Real.exp (-((κ + 2) * Real.log 16) * (n + 1))) +
          W.card * ((n + 1) * (2 * Real.exp (-((κ + 3) * n * Real.log 16))))) := by
        rw [sum_const_ofReal, Finset.sum_congr rfl (fun w _ => sum_const_ofReal J _),
          sum_const_ofReal, hJcard, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        push_cast
        rfl
    _ ≤ ENNReal.ofReal ((Real.pi * m + 3) * (c + 2) * Real.exp (-(κ * n * Real.log 16))) :=
        ENNReal.ofReal_le_ofReal hsum

end SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails
