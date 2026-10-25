import BR1Bridges
import LQGMetric.Papers.DDDF.PsiSupTail
import LQGMetric.Field.CircleAvgGauss
import LQGMetric.Field.CircleAvgRate
import LQGMetric.Field.CircleAvgVar
import LQGMetric.Field.CircleAvgKolm
import LQGMetric.Field.MeasurableAvg




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra

open LQGMetric (DistC TestC TestC0 IsWholePlaneGFF logCov bumpTest)
open LQGMetric.CircleAvg (mollAvg circBump circDiff logPot circLog)
open LQGMetric.SupTail (ferniqueBox ferniqueCF)

 

 
theorem continuous_circleAverage_center {g : ℂ → ℝ} (hg : Continuous g) (r : ℝ) :
    Continuous fun z : ℂ => Real.circleAverage g z r := by
  have hc : Continuous fun p : ℂ × ℝ => circleMap p.1 r p.2 := by
    unfold circleMap
    fun_prop
  have hI : Continuous fun z : ℂ => ∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap z r θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun z θ => g (circleMap z r θ)) (hg.comp hc) _ _
  have e : (fun z : ℂ => Real.circleAverage g z r) =
      fun z => (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap z r θ) := by
    funext z
    exact Real.circleAverage_def
  rw [e]
  exact hI.const_smul ((2 * Real.pi)⁻¹)

 
theorem continuous_mollAvg_center (T : DistC) (n : ℕ) (r : ℝ) :
    Continuous fun z => mollAvg T n z r :=
  continuous_circleAverage_center (T.continuous.comp (LQGMetric.continuous_bumpTest n)) r

 

theorem integrable_bump_mul_circLog {r : ℝ} (hr : 0 < r) (k : ℕ) (z x : ℂ) :
    Integrable fun t => bumpTest k 0 t * circLog z r (x - t) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (bumpTest k 0).continuous.mul
      ((LQGMetric.CircleAvg.continuous_circLog hr.ne' z).comp (continuous_const.sub continuous_id))
  · exact (bumpTest k 0).hasCompactSupport.mul_right

 
theorem abs_logPot_circBump_sub_le {r : ℝ} (hr : 0 < r) (k : ℕ) (u v x : ℂ) :
    |logPot (circBump k v r) x - logPot (circBump k u r) x| ≤ ‖u - v‖ / r := by
  rw [LQGMetric.CircleAvg.logPot_circBump, LQGMetric.CircleAvg.logPot_circBump]
  have h1 := integrable_bump_mul_circLog hr k v x
  have h2 := integrable_bump_mul_circLog hr k u x
  have e : (-∫ t, bumpTest k 0 t * circLog v r (x - t)) -
      (-∫ t, bumpTest k 0 t * circLog u r (x - t)) =
      ∫ t, bumpTest k 0 t * (circLog u r (x - t) - circLog v r (x - t)) := by
    rw [neg_sub_neg, ← integral_sub h2 h1]
    congr 1
    funext t
    ring
  rw [e]
  have hb : ∀ t, ‖bumpTest k 0 t * (circLog u r (x - t) - circLog v r (x - t))‖ ≤
      bumpTest k 0 t * (‖u - v‖ / r) := by
    intro t
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (LQGMetric.CircleAvg.bumpTest_nonneg k 0 t)]
    refine mul_le_mul_of_nonneg_left ?_ (LQGMetric.CircleAvg.bumpTest_nonneg k 0 t)
    have := LQGMetric.CircleAvg.abs_circLog_sub_circLog_le hr hr v u (x - t)
    simpa only [sub_self, abs_zero, zero_add, min_self, norm_sub_rev] using this
  have hint : Integrable fun t => bumpTest k 0 t * (‖u - v‖ / r) :=
    (LQGMetric.CircleAvg.integrable_testC _).mul_const _
  calc |∫ t, bumpTest k 0 t * (circLog u r (x - t) - circLog v r (x - t))|
      = ‖∫ t, bumpTest k 0 t * (circLog u r (x - t) - circLog v r (x - t))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, bumpTest k 0 t * (‖u - v‖ / r) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hb)
    _ = ‖u - v‖ / r := by
        rw [integral_mul_const, LQGMetric.CircleAvg.integral_bumpTest', one_mul]

 
theorem logCov_mollIncr_sub_le {r : ℝ} (hr : 0 < r) (n : ℕ) (u v : ℂ) :
    logCov (⇑((circBump (n + 1) v r - circBump n v r) - (circBump (n + 1) u r - circBump n u r)))
      (⇑((circBump (n + 1) v r - circBump n v r) - (circBump (n + 1) u r - circBump n u r))) ≤
      8 / r * ‖u - v‖ := by
  set ψ : TestC := (circBump (n + 1) v r - circBump n v r) - (circBump (n + 1) u r - circBump n u r)
    with hψ
  rw [LQGMetric.CircleAvg.logCov_eq_integral_logPot]
  set c : ℝ := 2 * (‖u - v‖ / r) with hc
  have hc0 : 0 ≤ c := by positivity
  have hpot : ∀ x, |logPot ψ x| ≤ c := by
    intro x
    rw [hψ, LQGMetric.CircleAvg.logPot_sub, LQGMetric.CircleAvg.logPot_sub,
      LQGMetric.CircleAvg.logPot_sub]
    have h1 := abs_logPot_circBump_sub_le hr (n + 1) u v x
    have h2 := abs_logPot_circBump_sub_le hr n u v x
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  set S : ℂ → ℝ := fun x => circBump (n + 1) v r x + circBump n v r x +
    circBump (n + 1) u r x + circBump n u r x with hS
  have hψS : ∀ x, |ψ x| ≤ S x := by
    intro x
    have e : ψ x = (circBump (n + 1) v r x - circBump n v r x) -
        (circBump (n + 1) u r x - circBump n u r x) := rfl
    rw [e, hS]
    have := LQGMetric.CircleAvg.circBump_nonneg (n + 1) v r x
    have := LQGMetric.CircleAvg.circBump_nonneg n v r x
    have := LQGMetric.CircleAvg.circBump_nonneg (n + 1) u r x
    have := LQGMetric.CircleAvg.circBump_nonneg n u r x
    rw [abs_le]
    constructor <;> linarith
  have hb : ∀ x, ‖ψ x * logPot ψ x‖ ≤ S x * c := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (hψS x) (hpot x) (abs_nonneg _) ((abs_nonneg _).trans (hψS x))
  have hSi : Integrable S := by
    have i := LQGMetric.CircleAvg.integrable_testC
    exact (((i _).add (i _)).add (i _)).add (i _)
  have hint : Integrable fun x => S x * c := hSi.mul_const c
  have hSint : ∫ x, S x = 4 := by
    have i := LQGMetric.CircleAvg.integrable_testC
    have h4 := integral_add (μ := volume)
      (((i (circBump (n + 1) v r)).add (i (circBump n v r))).add (i (circBump (n + 1) u r)))
      (i (circBump n u r))
    have h3 := integral_add (μ := volume) ((i (circBump (n + 1) v r)).add (i (circBump n v r)))
      (i (circBump (n + 1) u r))
    have h2 := integral_add (μ := volume) (i (circBump (n + 1) v r)) (i (circBump n v r))
    simp only [Pi.add_apply] at h4 h3 h2
    rw [hS, h4, h3, h2]
    simp only [LQGMetric.CircleAvg.integral_circBump]
    norm_num
  calc ∫ x, ψ x * logPot ψ x ≤ ‖∫ x, ψ x * logPot ψ x‖ := Real.le_norm_self _
    _ ≤ ∫ x, S x * c := norm_integral_le_of_norm_le hint (Eventually.of_forall hb)
    _ = 8 / r * ‖u - v‖ := by
        rw [integral_mul_const, hSint, hc]
        ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

 
theorem integral_sq_mollIncr_sub_le (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (n : ℕ)
    (u v : ℂ) :
    ∫ ω, ((mollAvg (h ω) (n + 1) v r - mollAvg (h ω) n v r) -
      (mollAvg (h ω) (n + 1) u r - mollAvg (h ω) n u r)) ^ 2 ∂P ≤ 8 / r * ‖u - v‖ := by
  set ψ : TestC := (circBump (n + 1) v r - circBump n v r) - (circBump (n + 1) u r - circBump n u r)
    with hψ
  have hψ0 : ∫ x, ψ x = 0 := by
    have i := LQGMetric.CircleAvg.integrable_testC
    have h3 := integral_sub (μ := volume) ((i (circBump (n + 1) v r)).sub (i (circBump n v r)))
      ((i (circBump (n + 1) u r)).sub (i (circBump n u r)))
    have h2 := integral_sub (μ := volume) (i (circBump (n + 1) v r)) (i (circBump n v r))
    have h1 := integral_sub (μ := volume) (i (circBump (n + 1) u r)) (i (circBump n u r))
    simp only [Pi.sub_apply] at h3 h2 h1
    have e : (fun x => ψ x) = fun x => (circBump (n + 1) v r x - circBump n v r x) -
        (circBump (n + 1) u r x - circBump n u r x) := rfl
    rw [e, h3, h2, h1]
    simp only [LQGMetric.CircleAvg.integral_circBump]
    norm_num
  set ψ0 : TestC0 := ⟨ψ, hψ0⟩
  have he : ∀ ω, ((mollAvg (h ω) (n + 1) v r - mollAvg (h ω) n v r) -
      (mollAvg (h ω) (n + 1) u r - mollAvg (h ω) n u r)) = h ω ψ0.1 := by
    intro ω
    simp only [LQGMetric.CircleAvg.mollAvg_eq, ψ0, hψ, map_sub]
  have hmeas : AEMeasurable (fun ω => h ω ψ0.1) P :=
    ((LQGMetric.GFFInv.measurable_pair _).comp hh.measurable).aemeasurable
  simp_rw [he]
  rw [← variance_of_integral_eq_zero hmeas (hh.centered ψ0), ← covariance_self hmeas,
    hh.covariance_eq ψ0 ψ0]
  exact logCov_mollIncr_sub_le hr n u v

 
theorem variance_mollIncr_le (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) (n : ℕ) (z : ℂ) :
    Var[fun ω => mollAvg (h ω) (n + 1) z r - mollAvg (h ω) n z r; P] ≤ 4 / r * 2⁻¹ ^ n := by
  have e : (fun ω => mollAvg (h ω) (n + 1) z r - mollAvg (h ω) n z r) =
      fun ω => h ω (circDiff (n + 1) z r n z r).1 := by
    funext ω
    exact LQGMetric.CircleAvg.mollAvg_sub_eq _ _ _ _ _ _ _
  have hmeas : AEMeasurable (fun ω => h ω (circDiff (n + 1) z r n z r).1) P :=
    ((LQGMetric.GFFInv.measurable_pair _).comp hh.measurable).aemeasurable
  rw [e, ← covariance_self hmeas, hh.covariance_eq]
  exact LQGMetric.CircleAvg.logCov_circDiff_succ_le hr z n

 

 
theorem exp_neg_le_factorial_div {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ (Nat.factorial 10 : ℝ) / y ^ 10 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 10
  have hf : (0 : ℝ) < Nat.factorial 10 := by exact_mod_cast Nat.factorial_pos 10
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
  exact h

 
theorem step_tail_le {r : ℝ} (hr : 0 < r) (n : ℕ) :
    2 * ((4 ^ n : ℕ) : ℝ) ^ 2 * Real.exp (-((7 / 8 : ℝ) ^ n) ^ 2 / (2 * (√(4 / r * 2⁻¹ ^ n)) ^ 2)) ≤
      2 * (Nat.factorial 10 : ℝ) * (8 / r) ^ 10 * 2⁻¹ ^ n := by
  have hσ : (√(4 / r * 2⁻¹ ^ n)) ^ 2 = 4 / r * 2⁻¹ ^ n := Real.sq_sqrt (by positivity)
  set y : ℝ := r / 8 * (49 / 32) ^ n with hy
  have hy0 : 0 < y := by positivity
  have hyeq : ((7 / 8 : ℝ) ^ n) ^ 2 / (2 * (√(4 / r * 2⁻¹ ^ n)) ^ 2) = y := by
    rw [hσ, hy, ← pow_mul, mul_comm n 2, pow_mul]
    have h2 : (2 : ℝ)⁻¹ ^ n ≠ 0 := by positivity
    have e1 : ((7 / 8 : ℝ) ^ 2) ^ n = (49 / 64 : ℝ) ^ n := by norm_num
    have e2 : (49 / 32 : ℝ) ^ n = (49 / 64 : ℝ) ^ n / (2 : ℝ)⁻¹ ^ n := by
      rw [← div_pow]; norm_num
    rw [e1, e2]
    field_simp
    ring
  rw [neg_div, hyeq]
  have hexp := exp_neg_le_factorial_div hy0
  have hf : (0 : ℝ) ≤ Nat.factorial 10 := by positivity
  have hkey : ((4 ^ n : ℕ) : ℝ) ^ 2 / y ^ 10 ≤ (8 / r) ^ 10 * 2⁻¹ ^ n := by
    rw [div_le_iff₀ (by positivity), hy, mul_pow, ← pow_mul]
    push_cast
    have hb : (16 : ℝ) * ((32 / 49 : ℝ) ^ 10) ≤ 2⁻¹ := by norm_num
    have hpow : ((16 : ℝ) * ((32 / 49 : ℝ) ^ 10)) ^ n ≤ (2⁻¹ : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) hb n
    have e1 : ((4 : ℝ) ^ n) ^ 2 = (16 : ℝ) ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have e2 : ((49 / 32 : ℝ) ^ (n * 10)) = ((49 / 32 : ℝ) ^ 10) ^ n := by
      rw [← pow_mul, mul_comm]
    have e3 : (8 / r) ^ 10 * (r / 8) ^ 10 = 1 := by
      rw [← mul_pow, div_mul_div_comm, mul_comm 8 r, div_self (by positivity), one_pow]
    rw [e1, e2]
    have hq : (0 : ℝ) < ((49 / 32 : ℝ) ^ 10) ^ n := by positivity
    calc (16 : ℝ) ^ n = ((16 : ℝ) * ((32 / 49 : ℝ) ^ 10)) ^ n * ((49 / 32 : ℝ) ^ 10) ^ n := by
          rw [← mul_pow, mul_assoc, ← mul_pow]; norm_num
      _ ≤ 2⁻¹ ^ n * ((49 / 32 : ℝ) ^ 10) ^ n := by gcongr
      _ = (8 / r) ^ 10 * 2⁻¹ ^ n * ((r / 8) ^ 10 * ((49 / 32 : ℝ) ^ 10) ^ n) := by
          rw [show (8 / r) ^ 10 * 2⁻¹ ^ n * ((r / 8) ^ 10 * ((49 / 32 : ℝ) ^ 10) ^ n) =
            ((8 / r) ^ 10 * (r / 8) ^ 10) * (2⁻¹ ^ n * ((49 / 32 : ℝ) ^ 10) ^ n) by ring, e3,
            one_mul]
  calc 2 * ((4 ^ n : ℕ) : ℝ) ^ 2 * Real.exp (-y)
      ≤ 2 * ((4 ^ n : ℕ) : ℝ) ^ 2 * ((Nat.factorial 10 : ℝ) / y ^ 10) := by gcongr
    _ = 2 * (Nat.factorial 10 : ℝ) * (((4 ^ n : ℕ) : ℝ) ^ 2 / y ^ 10) := by ring
    _ ≤ 2 * (Nat.factorial 10 : ℝ) * ((8 / r) ^ 10 * 2⁻¹ ^ n) := by gcongr
    _ = 2 * (Nat.factorial 10 : ℝ) * (8 / r) ^ 10 * 2⁻¹ ^ n := by ring

 
theorem sqrt_step_eq {r L : ℝ} (hr : 0 < r) (hL : 0 < L) (n : ℕ) :
    √(8 / r * (L / ((4 ^ n : ℕ) : ℝ))) = √(8 * L / r) * 2⁻¹ ^ n := by
  have h4 : ((2 : ℝ)⁻¹ ^ n) ^ 2 = 1 / (4 : ℝ) ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, one_div, ← inv_pow]
    norm_num
  have e : 8 / r * (L / ((4 ^ n : ℕ) : ℝ)) = 8 * L / r * ((2 : ℝ)⁻¹ ^ n) ^ 2 := by
    rw [h4]
    push_cast
    ring
  rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

 

theorem ae_eventually_mollIncr_lt [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P) {r : ℝ}
    (hr : 0 < r) (x₀ : ℂ) {L : ℝ} (hL : 0 < L) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ x ∈ ferniqueBox 0 L,
      |mollAvg (h ω) (n + 1) (x + x₀) r - mollAvg (h ω) n (x + x₀) r| <
        ferniqueCF * √(8 * L / r) * 2⁻¹ ^ n + (7 / 8) ^ n := by
  set G : ℕ → ℂ → Ω → ℝ := fun n x ω =>
    mollAvg (h ω) (n + 1) (x + x₀) r - mollAvg (h ω) n (x + x₀) r with hG
  set s : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (ferniqueCF *
    √(8 / r * (L / ((4 ^ n : ℕ) : ℝ))) + (7 / 8) ^ n) ≤
      ⨆ x ∈ ferniqueBox 0 L, ENNReal.ofReal |G n x ω|} with hs
  have hstep : ∀ n, P (s n) ≤ ENNReal.ofReal (2 * (Nat.factorial 10 : ℝ) * (8 / r) ^ 10 * 2⁻¹ ^ n) := by
    intro n
    have hGP : IsGaussianProcess (G n) P := by
      have := (LQGMetric.CircleAvg.isGaussianProcess_mollAvg_sub hh).comp_right
        (fun x : ℂ => (((n + 1 : ℕ), x + x₀, r), (n, x + x₀, r)))
      exact this.congr fun x => Eventually.of_forall fun ω => rfl
    have h0 : ∀ x, ∫ ω, G n x ω ∂P = 0 := fun x =>
      LQGMetric.CircleAvg.integral_mollAvg_sub hh _ _ _ _ _ _
    have hc : ∀ ω, Continuous fun x => G n x ω := fun ω =>
      ((continuous_mollAvg_center (h ω) (n + 1) r).comp (continuous_id.add continuous_const)).sub
        ((continuous_mollAvg_center (h ω) n r).comp (continuous_id.add continuous_const))
    have hinc : ∀ u v : ℂ, ∫ ω, (G n v ω - G n u ω) ^ 2 ∂P ≤ 8 / r * ‖u - v‖ := by
      intro u v
      have := integral_sq_mollIncr_sub_le hh hr n (u + x₀) (v + x₀)
      rwa [show u + x₀ - (v + x₀) = u - v by ring] at this
    have hvar : ∀ v, Var[G n v; P] ≤ (√(4 / r * 2⁻¹ ^ n)) ^ 2 := by
      intro v
      rw [Real.sq_sqrt (by positivity)]
      exact variance_mollIncr_le hh hr n (v + x₀)
    have hnpos : 0 < 4 ^ n := by positivity
    refine (LQGMetric.SupTail.tail_iSup_abs_square hnpos hL hGP h0 hc (by positivity) hinc
      (Real.sqrt_pos.2 (by positivity)) hvar (by positivity)).trans ?_
    exact ENNReal.ofReal_le_ofReal (step_tail_le hr n)
  have hsum : ∑' n, P (s n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' n, ENNReal.ofReal
      (2 * (Nat.factorial 10 : ℝ) * (8 / r) ^ 10 * 2⁻¹ ^ n)) ?_ (ENNReal.tsum_le_tsum hstep)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_left _)]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn x hx
  have hlt : ⨆ x ∈ ferniqueBox 0 L, ENNReal.ofReal |G n x ω| <
      ENNReal.ofReal (ferniqueCF * √(8 / r * (L / ((4 ^ n : ℕ) : ℝ))) + (7 / 8) ^ n) := by
    simpa only [hs, Set.mem_ofPred_eq, not_le] using hn
  have hle : ENNReal.ofReal |G n x ω| ≤ ⨆ x ∈ ferniqueBox 0 L, ENNReal.ofReal |G n x ω| :=
    le_iSup₂ (f := fun x (_ : x ∈ ferniqueBox 0 L) => ENNReal.ofReal |G n x ω|) x hx
  have h3 := (ENNReal.ofReal_lt_ofReal_iff'.mp (hle.trans_lt hlt)).1
  rw [sqrt_step_eq hr hL n] at h3
  simpa only [hG, mul_assoc] using h3

 

 
theorem exists_limit_of_eventually_incr_le {m : ℕ → ℂ → ℝ} {S : Set ℂ}
    (hm : ∀ n, ContinuousOn (m n) S) {δ : ℕ → ℝ} (hδ : Summable δ)
    (hev : ∀ᶠ n in atTop, ∀ x ∈ S, |m (n + 1) x - m n x| ≤ δ n) :
    ∃ g : ℂ → ℝ, ContinuousOn g S ∧ ∀ x ∈ S, Tendsto (fun n => m n x) atTop (𝓝 (g x)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set d : ℕ → ℂ → ℝ := fun k x => m (N + k + 1) x - m (N + k) x with hd
  have hδ' : Summable fun k => δ (N + k) := by
    have := (summable_nat_add_iff N).mpr hδ
    simpa only [add_comm] using this
  have hdb : ∀ k x, x ∈ S → ‖d k x‖ ≤ δ (N + k) := fun k x hx => by
    rw [Real.norm_eq_abs]
    exact hN (N + k) (Nat.le_add_right N k) x hx
  refine ⟨fun x => m N x + ∑' k, d k x, (hm N).add (continuousOn_tsum
    (fun k => (hm _).sub (hm _)) hδ' hdb), fun x hx => ?_⟩
  have hsx : Summable fun k => d k x := Summable.of_norm_bounded hδ' fun k => hdb k x hx
  have htel : ∀ n, m (N + n) x = m N x + ∑ k ∈ Finset.range n, d k x := by
    intro n
    have := Finset.sum_range_sub (fun i => m (N + i) x) n
    simp only [hd]
    rw [show (∑ k ∈ Finset.range n, (m (N + k + 1) x - m (N + k) x)) =
      ∑ i ∈ Finset.range n, (m (N + (i + 1)) x - m (N + i) x) from rfl, this, add_zero]
    ring
  have ht : Tendsto (fun n => m (N + n) x) atTop (𝓝 (m N x + ∑' k, d k x)) := by
    simp_rw [htel]
    exact tendsto_const_nhds.add hsx.hasSum.tendsto_sum_nat
  rw [← tendsto_add_atTop_iff_nat N]
  simpa only [add_comm] using ht

 

theorem ae_exists_continuous_limit_mollAvg [IsProbabilityMeasure P] (hh : IsWholePlaneGFF h P)
    {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∃ Lf : ℂ → ℝ, Continuous Lf ∧
      ∀ z, Tendsto (fun n => mollAvg (h ω) n z r) atTop (𝓝 (Lf z)) := by
  set x₀ : ℕ → ℂ := fun j => ⟨-((j : ℝ) + 1), -((j : ℝ) + 1)⟩ with hx₀
  set L : ℕ → ℝ := fun j => 2 * ((j : ℝ) + 1) with hL
  have hLpos : ∀ j, 0 < L j := fun j => by simp only [hL]; positivity
  have hall := ae_all_iff.2 fun j => ae_eventually_mollIncr_lt hh hr (x₀ j) (hLpos j)
  filter_upwards [hall] with ω hω
  
  have hmem : ∀ (j : ℕ) (w : ℂ), ‖w‖ < (j : ℝ) + 1 → w - x₀ j ∈ ferniqueBox 0 (L j) := by
    intro j w hw
    have hre : |w.re| < (j : ℝ) + 1 := (Complex.abs_re_le_norm w).trans_lt hw
    have him : |w.im| < (j : ℝ) + 1 := (Complex.abs_im_le_norm w).trans_lt hw
    rw [abs_lt] at hre him
    simp only [ferniqueBox, Complex.zero_re, Complex.zero_im, zero_add, hx₀, hL]
    refine Complex.mem_reProdIm.mpr ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
  
  have hbox : ∀ j, ∃ g : ℂ → ℝ, ContinuousOn g (ferniqueBox 0 (L j)) ∧
      ∀ x ∈ ferniqueBox 0 (L j),
        Tendsto (fun n => mollAvg (h ω) n (x + x₀ j) r) atTop (𝓝 (g x)) := by
    intro j
    refine exists_limit_of_eventually_incr_le
      (m := fun n x => mollAvg (h ω) n (x + x₀ j) r)
      (fun n => ((continuous_mollAvg_center (h ω) n r).comp
        (continuous_id.add continuous_const)).continuousOn)
      (δ := fun n => ferniqueCF * √(8 * L j / r) * 2⁻¹ ^ n + (7 / 8) ^ n) ?_ ?_
    · exact ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_left _).add
        (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    · filter_upwards [hω j] with n hn x hx using (hn x hx).le
  choose g hgc hgt using hbox
  set Lf : ℂ → ℝ := fun z => limUnder atTop fun n => mollAvg (h ω) n z r with hLf
  have hLfeq : ∀ (j : ℕ) (w : ℂ), ‖w‖ < (j : ℝ) + 1 → Lf w = g j (w - x₀ j) := by
    intro j w hw
    have ht := hgt j _ (hmem j w hw)
    rw [sub_add_cancel] at ht
    exact ht.limUnder_eq
  refine ⟨Lf, continuous_iff_continuousAt.2 fun z => ?_, fun z => ?_⟩
  · obtain ⟨j, hj⟩ := exists_nat_gt ‖z‖
    set U : Set ℂ := Metric.ball 0 ((j : ℝ) + 1) with hU
    have hzU : z ∈ U := by
      rw [hU, Metric.mem_ball, dist_zero_right]; linarith
    have hcont : ContinuousOn (fun w => g j (w - x₀ j)) U :=
      (hgc j).comp (continuous_id.sub continuous_const).continuousOn fun w hw => by
        refine hmem j w ?_
        simpa [hU, Metric.mem_ball, dist_zero_right] using hw
    have hcont' : ContinuousOn Lf U := hcont.congr fun w hw => by
      refine hLfeq j w ?_
      simpa [hU, Metric.mem_ball, dist_zero_right] using hw
    exact hcont'.continuousAt (Metric.isOpen_ball.mem_nhds hzU)
  · obtain ⟨j, hj⟩ := exists_nat_gt ‖z‖
    have hz : ‖z‖ < (j : ℝ) + 1 := by linarith
    have ht := hgt j _ (hmem j z hz)
    rw [sub_add_cancel] at ht
    rw [hLfeq j z hz]
    exact ht

 

 


theorem ae_isCircleAverage_all {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGDimension.IsGFFCircleAverage H P ∧
      ∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P, ∀ z : ℂ, IsCircleAverage (h ω) r z (H r z ω) := by
  obtain ⟨H, hH, -, hbridge⟩ := exists_normalized_circleAverage_process_bridge hh
  refine ⟨H, hH, fun r => ?_⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  have hD : ∀ᵐ ω ∂P, ∀ z ∈ D, H r z ω = LQGMetric.circleAvg (h ω) r z := by
    refine (ae_ball_iff hDc).2 fun z _ => ?_
    exact hbridge r z _ (ae_isCircleAverage_old hh.1 r z)
  filter_upwards [hD, ae_exists_continuous_limit_mollAvg hh.1 r.2] with ω hω ⟨Lf, hLfc, hLft⟩
  have hcirc : ∀ z, LQGMetric.circleAvg (h ω) r z = Lf z := fun z => by
    rw [LQGMetric.CircleAvg.circleAvg_eq_limUnder]
    exact (hLft z).limUnder_eq
  have hext : (fun z => H r z ω) = Lf :=
    Continuous.ext_on hDd (hH.continuous r r.2 ω) hLfc fun z hz => by
      rw [hω z hz, hcirc z]
  intro z
  have := hLft z
  rw [← congrFun hext z] at this
  exact this

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.MainExtra
