import QuantumZipper.Proofs.ItoLite.Oscillation
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-WINSPLIT-ii: Doob's maximal inequality for the exponential Brownian martingale

For a pre-Brownian motion `B`, `γ : ℝ`, `s ≥ 0` and a countable set `D ⊆ [0, s]`,

`E sup_{t ∈ D} |exp (γ B_t - γ² t / 2) - 1| ≤ 2 √(exp (γ² s) - 1)`

(`lintegral_iSup_expMart_sub_one_le`). This is the estimate behind `C(N) → 1` in
Sheffield–Wang, arXiv:1605.06171, p. 9.

**Source.** Doob's weak-type maximal inequality (J. L. Doob, *Stochastic Processes*, Wiley 1953,
Ch. VII, Thm. 3.2; mathlib `MeasureTheory.maximal_ineq`) applied to the nonnegative submartingale
`(M_k)²`, `M_k = exp (γ B_{t_k} - γ² t_k / 2) - 1`, along a finite grid, followed by the layer-cake
formula `E Y = ∫_0^∞ P(Y > x) dx ≤ ∫_0^∞ min (1, σ²/x²) dx = 2σ`. The submartingale property
is checked directly (`(a + b)² ≥ a² + 2ab` and the independent increment with mean one), in the
style of `BMOsc.expGrid_submartingale`; countable `D` follows by monotone convergence over finite
subsets, and a measurable modification removes the measurability hypothesis.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal NNReal

namespace QuantumZipper
namespace E6

set_option linter.unusedSectionVars false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

/-- The exponential Brownian martingale `exp (γ B_t - γ² t / 2)`. -/
def swExpMart (B : ℝ≥0 → Ω → ℝ) (γ : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  rexp (γ * B t ω - γ ^ 2 / 2 * t)

theorem swDoob_gauss_integrable (v : ℝ≥0) (a b : ℝ) :
    Integrable (fun x => rexp (a * x + b)) (gaussianReal 0 v) := by
  have h : (fun x => rexp (a * x + b)) = fun x => rexp (a * x) * rexp b :=
    funext fun x => by rw [exp_add]
  rw [h]
  exact (integrable_exp_mul_gaussianReal a).mul_const _

theorem swDoob_gauss_integral (v : ℝ≥0) (a b : ℝ) :
    ∫ x, rexp (a * x + b) ∂gaussianReal 0 v = rexp (v * a ^ 2 / 2 + b) := by
  have h : (fun x => rexp (a * x + b)) = fun x => rexp (a * x) * rexp b :=
    funext fun x => by rw [exp_add]
  rw [h, integral_mul_const, BMOsc.integral_exp_gaussianReal, ← exp_add]

theorem swDoob_integrable_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) (a b : ℝ) :
    Integrable (fun ω => rexp (a * B t ω + b)) P :=
  (hB.hasLaw_eval t).integrable_comp (f := fun x => rexp (a * x + b))
    (swDoob_gauss_integrable t a b)

theorem swDoob_integral_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) (a b : ℝ) :
    ∫ ω, rexp (a * B t ω + b) ∂P = rexp (t * a ^ 2 / 2 + b) := by
  have h := (hB.hasLaw_eval t).integral_comp (f := fun x => rexp (a * x + b)) (by fun_prop)
  rw [swDoob_gauss_integral] at h
  rw [← h]
  rfl

theorem swExpMart_eq (γ : ℝ) (t : ℝ≥0) (ω : Ω) :
    swExpMart B γ t ω = rexp (γ * B t ω + (-(γ ^ 2 / 2 * t))) := by
  unfold swExpMart; rw [sub_eq_add_neg]

theorem swExpMart_sq_eq (γ : ℝ) (t : ℝ≥0) (ω : Ω) :
    swExpMart B γ t ω ^ 2 = rexp ((2 * γ) * B t ω + (-(γ ^ 2 * t))) := by
  unfold swExpMart; rw [sq, ← exp_add]; congr 1; ring

theorem swExpMart_integrable (hB : IsPreBrownianReal B P) (γ : ℝ) (t : ℝ≥0) :
    Integrable (swExpMart B γ t) P := by
  have h : swExpMart B γ t = fun ω => rexp (γ * B t ω + (-(γ ^ 2 / 2 * t))) :=
    funext fun ω => swExpMart_eq γ t ω
  rw [h]; exact swDoob_integrable_eval hB t _ _

theorem swExpMart_sq_integrable (hB : IsPreBrownianReal B P) (γ : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => swExpMart B γ t ω ^ 2) P := by
  have h : (fun ω => swExpMart B γ t ω ^ 2) =
      fun ω => rexp ((2 * γ) * B t ω + (-(γ ^ 2 * t))) := funext fun ω => swExpMart_sq_eq γ t ω
  rw [h]; exact swDoob_integrable_eval hB t _ _

theorem swExpMart_integral (hB : IsPreBrownianReal B P) (γ : ℝ) (t : ℝ≥0) :
    ∫ ω, swExpMart B γ t ω ∂P = 1 := by
  have h : swExpMart B γ t = fun ω => rexp (γ * B t ω + (-(γ ^ 2 / 2 * t))) :=
    funext fun ω => swExpMart_eq γ t ω
  rw [h, swDoob_integral_eval hB]
  have : (t : ℝ) * γ ^ 2 / 2 + -(γ ^ 2 / 2 * t) = 0 := by ring
  rw [this, exp_zero]

theorem swExpMart_sq_integral (hB : IsPreBrownianReal B P) (γ : ℝ) (t : ℝ≥0) :
    ∫ ω, swExpMart B γ t ω ^ 2 ∂P = rexp (γ ^ 2 * t) := by
  have h : (fun ω => swExpMart B γ t ω ^ 2) =
      fun ω => rexp ((2 * γ) * B t ω + (-(γ ^ 2 * t))) := funext fun ω => swExpMart_sq_eq γ t ω
  rw [h, swDoob_integral_eval hB]
  congr 1; ring

theorem swExpMart_memLp (hB : IsPreBrownianReal B P) (γ : ℝ) (t : ℝ≥0) :
    MemLp (swExpMart B γ t) 2 P :=
  (memLp_two_iff_integrable_sq (swExpMart_integrable hB γ t).aestronglyMeasurable).2
    (swExpMart_sq_integrable hB γ t)

theorem swExpMart_sub_one_sq_integrable (hB : IsPreBrownianReal B P) (γ : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => (swExpMart B γ t ω - 1) ^ 2) P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h : (fun ω => (swExpMart B γ t ω - 1) ^ 2) =
      fun ω => swExpMart B γ t ω ^ 2 - 2 * swExpMart B γ t ω + 1 := funext fun ω => by ring
  rw [h]
  exact ((swExpMart_sq_integrable hB γ t).sub ((swExpMart_integrable hB γ t).const_mul 2)).add
    (integrable_const 1)

theorem swExpMart_sub_one_sq_integral (hB : IsPreBrownianReal B P) (γ : ℝ) (t : ℝ≥0) :
    ∫ ω, (swExpMart B γ t ω - 1) ^ 2 ∂P = rexp (γ ^ 2 * t) - 1 := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have h : (fun ω => (swExpMart B γ t ω - 1) ^ 2) =
      fun ω => swExpMart B γ t ω ^ 2 - 2 * swExpMart B γ t ω + 1 := funext fun ω => by ring
  have i1 : Integrable (fun ω => swExpMart B γ t ω ^ 2 - 2 * swExpMart B γ t ω) P :=
    (swExpMart_sq_integrable hB γ t).sub ((swExpMart_integrable hB γ t).const_mul 2)
  rw [h, integral_add i1 (integrable_const 1),
    integral_sub (swExpMart_sq_integrable hB γ t) ((swExpMart_integrable hB γ t).const_mul 2),
    integral_const_mul, swExpMart_sq_integral hB, swExpMart_integral hB]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

/-- Along a monotone grid, `k ↦ (swExpMart B γ (u k) - 1)²` is a submartingale for the natural
filtration. -/
theorem swExpMart_sq_submartingale (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    {u : ℕ → ℝ≥0} (hu : Monotone u) (γ : ℝ) :
    Submartingale (fun k ω => (swExpMart B γ (u k) ω - 1) ^ 2)
      (BMOsc.gridFiltration hBm u hu) P := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmeas : ∀ k, Measurable[bmFiltration B (u k)] (swExpMart B γ (u k)) := fun k =>
    (((BMOsc.measurable_bmFiltration le_rfl).const_mul γ).sub_const _).exp
  refine submartingale_of_setIntegral_le
    (fun k => (((hmeas k).sub_const 1).pow_const 2).stronglyMeasurable)
    (fun k => swExpMart_sub_one_sq_integrable hB γ (u k)) ?_
  intro i j hij A hA
  have hAm : MeasurableSet A := (BMOsc.gridFiltration hBm u hu).le i A hA
  set X : ℝ≥0 → Ω → ℝ := swExpMart B γ with hXdef
  set c : ℝ := γ ^ 2 / 2 * ((u j - u i : ℝ≥0) : ℝ) with hc
  have hX : ∀ ω, X (u j) ω = X (u i) ω * rexp (γ * (B (u j) ω - B (u i) ω) - c) := by
    intro ω
    simp only [hXdef, swExpMart, hc, ← exp_add]
    congr 1
    rw [NNReal.coe_sub (hu hij)]
    ring
  -- the cross term has mean zero
  have hξ : Measurable[bmFiltration B (u i)]
      (A.indicator fun ω => 2 * (X (u i) ω - 1) * X (u i) ω) :=
    (((hmeas i).sub_const 1).const_mul 2 |>.mul (hmeas i)).indicator hA
  have key := BMOsc.integral_mul_comp_incr hB hBm (s := u j - u i) hξ
    (g := fun x => rexp (γ * x - c) - 1) (by fun_prop)
  rw [add_tsub_cancel_of_le (hu hij)] at key
  have hg : ∫ x, (rexp (γ * x - c) - 1) ∂gaussianReal 0 (u j - u i) = 0 := by
    have h1 : (fun x => rexp (γ * x - c) - 1) = fun x => rexp (γ * x + (-c)) - 1 :=
      funext fun x => by rw [← sub_eq_add_neg]
    rw [h1, integral_sub (swDoob_gauss_integrable _ _ _) (integrable_const 1),
      swDoob_gauss_integral]
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, hc]
    have : ((u j - u i : ℝ≥0) : ℝ) * γ ^ 2 / 2 + -(γ ^ 2 / 2 * ((u j - u i : ℝ≥0) : ℝ)) = 0 := by
      ring
    rw [this, exp_zero]; simp
  rw [hg, mul_zero] at key
  have hpt : (fun ω => (A.indicator fun ω => 2 * (X (u i) ω - 1) * X (u i) ω) ω *
      (rexp (γ * (B (u j) ω - B (u i) ω) - c) - 1)) =
      A.indicator fun ω => 2 * ((X (u i) ω - 1) * (X (u j) ω - X (u i) ω)) := by
    funext ω
    by_cases hω : ω ∈ A
    · simp only [indicator_of_mem hω, hX ω]; ring
    · simp [indicator_of_notMem hω]
  rw [hpt] at key
  have hcross : Integrable (A.indicator fun ω => 2 * ((X (u i) ω - 1) * (X (u j) ω - X (u i) ω)))
      P := by
    have h1 : MemLp (fun ω => X (u i) ω - 1) 2 P :=
      (swExpMart_memLp hB γ (u i)).sub (memLp_const 1)
    have h2 : MemLp (fun ω => X (u j) ω - X (u i) ω) 2 P :=
      (swExpMart_memLp hB γ (u j)).sub (swExpMart_memLp hB γ (u i))
    exact ((h1.integrable_mul h2).const_mul 2).indicator hAm
  have hi := (swExpMart_sub_one_sq_integrable hB γ (u i)).indicator hAm
  have hj := (swExpMart_sub_one_sq_integrable hB γ (u j)).indicator hAm
  rw [← integral_indicator hAm, ← integral_indicator hAm]
  calc ∫ ω, A.indicator (fun ω => (X (u i) ω - 1) ^ 2) ω ∂P
      = ∫ ω, A.indicator (fun ω => (X (u i) ω - 1) ^ 2) ω ∂P +
          ∫ ω, A.indicator (fun ω => 2 * ((X (u i) ω - 1) * (X (u j) ω - X (u i) ω))) ω ∂P := by
        rw [key, add_zero]
    _ = ∫ ω, (A.indicator (fun ω => (X (u i) ω - 1) ^ 2) ω +
          A.indicator (fun ω => 2 * ((X (u i) ω - 1) * (X (u j) ω - X (u i) ω))) ω) ∂P :=
        (integral_add hi hcross).symm
    _ ≤ ∫ ω, A.indicator (fun ω => (X (u j) ω - 1) ^ 2) ω ∂P := by
        refine integral_mono (hi.add hcross) hj fun ω => ?_
        by_cases hω : ω ∈ A
        · simp only [indicator_of_mem hω]
          nlinarith [sq_nonneg (X (u j) ω - X (u i) ω)]
        · simp [indicator_of_notMem hω]

/-- Doob's weak `L²` maximal inequality on a finite grid: `P(max_k |M_k| > x) ≤ σ² / x²`. -/
theorem swExpMart_grid_tail (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    {u : ℕ → ℝ≥0} (hu : Monotone u) (γ : ℝ) (n : ℕ) {s : ℝ≥0} (hs : u n ≤ s) {x : ℝ}
    (hx : 0 < x) :
    P {ω | x < (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |swExpMart B γ (u k) ω - 1|} ≤ ENNReal.ofReal ((rexp (γ ^ 2 * s) - 1) / x ^ 2) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hsub := swExpMart_sq_submartingale hB hBm hu γ
  have hmax := maximal_ineq hsub (fun k ω => sq_nonneg _) (ε := (x ^ 2).toNNReal) n
  rw [Real.coe_toNNReal _ (sq_nonneg x)] at hmax
  set S := {ω | x ^ 2 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
    fun k => (swExpMart B γ (u k) ω - 1) ^ 2}
  have hsubset : {ω | x < (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |swExpMart B γ (u k) ω - 1|} ⊆ S := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    obtain ⟨k, hk, hlt⟩ := (Finset.lt_sup'_iff _).1 hω
    have h2 : x ^ 2 < (swExpMart B γ (u k) ω - 1) ^ 2 := by
      have := sq_lt_sq' (by linarith [abs_nonneg (swExpMart B γ (u k) ω - 1)]) hlt
      rwa [sq_abs] at this
    exact h2.le.trans (Finset.le_sup' (fun k => (swExpMart B γ (u k) ω - 1) ^ 2) hk)
  have hle : ∫ ω in S, (swExpMart B γ (u n) ω - 1) ^ 2 ∂P ≤ rexp (γ ^ 2 * s) - 1 := by
    refine (setIntegral_le_integral (swExpMart_sub_one_sq_integrable hB γ (u n))
      (Eventually.of_forall fun ω => sq_nonneg _)).trans ?_
    rw [swExpMart_sub_one_sq_integral hB]
    have : γ ^ 2 * (u n : ℝ) ≤ γ ^ 2 * s :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (sq_nonneg γ)
    linarith [exp_le_exp.2 this]
  have h2 : ENNReal.ofReal (x ^ 2) * P S ≤ ENNReal.ofReal (rexp (γ ^ 2 * s) - 1) :=
    hmax.trans (ENNReal.ofReal_le_ofReal hle)
  have hS : P S ≤ ENNReal.ofReal (rexp (γ ^ 2 * s) - 1) / ENNReal.ofReal (x ^ 2) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hx.ne'])) (Or.inl ENNReal.ofReal_ne_top),
      mul_comm]
    exact h2
  rw [← ENNReal.ofReal_div_of_pos (by positivity)] at hS
  exact (measure_mono hsubset).trans hS

/-- `∫_σ^∞ σ² t^{-2} dt = σ`. -/
theorem swDoob_lintegral_Ioi {σ : ℝ} (hσ0 : 0 ≤ σ) :
    ∫⁻ t in Ioi σ, ENNReal.ofReal (σ ^ 2 * t ^ (-2 : ℝ)) = ENNReal.ofReal σ := by
  rcases hσ0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hpos]
    norm_num
    rw [Real.rpow_neg_one]
    field_simp
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hpos).const_mul _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hσ0.trans (le_of_lt ht)) _)

/-- Layer cake on a finite grid: `E max_k |M_k| ≤ 2σ`. -/
theorem swExpMart_grid_lintegral (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    {u : ℕ → ℝ≥0} (hu : Monotone u) (γ : ℝ) (n : ℕ) {s : ℝ≥0} (hs : u n ≤ s) :
    ∫⁻ ω, ENNReal.ofReal ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |swExpMart B γ (u k) ω - 1|) ∂P ≤
      2 * ENNReal.ofReal (√(rexp (γ ^ 2 * s) - 1)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set σ := √(rexp (γ ^ 2 * s) - 1) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσsq : σ ^ 2 = rexp (γ ^ 2 * s) - 1 :=
    Real.sq_sqrt (by linarith [one_le_exp (by positivity : 0 ≤ γ ^ 2 * (s : ℝ))])
  have hYnn : ∀ ω, 0 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |swExpMart B γ (u k) ω - 1| := fun ω =>
    (abs_nonneg _).trans (Finset.le_sup' (fun k => |swExpMart B γ (u k) ω - 1|)
      (Finset.mem_range.2 (Nat.zero_lt_succ n)))
  have hYm : Measurable fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
      fun k => |swExpMart B γ (u k) ω - 1| :=
    Finset.measurable_range_sup'' fun k _ =>
      continuous_abs.measurable.comp ((((hBm (u k)).const_mul γ).sub_const _).exp.sub_const 1)
  rw [lintegral_eq_lintegral_meas_lt P (Eventually.of_forall hYnn) hYm.aemeasurable,
    ← Ioc_union_Ioi_eq_Ioi hσ0, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same, two_mul]
  refine add_le_add ?_ ?_
  · calc _ ≤ ∫⁻ t in Ioc 0 σ, (1 : ℝ≥0∞) := lintegral_mono fun t => prob_le_one
      _ = ENNReal.ofReal σ := by simp [Real.volume_Ioc]
  · calc _ ≤ ∫⁻ t in Ioi σ, ENNReal.ofReal (σ ^ 2 * t ^ (-2 : ℝ)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht0 : 0 < t := hσ0.trans_lt ht
          refine (swExpMart_grid_tail hB hBm hu γ n hs ht0).trans (le_of_eq ?_)
          rw [← hσsq, Real.rpow_neg ht0.le, Real.rpow_two, div_eq_mul_inv]
      _ = ENNReal.ofReal σ := swDoob_lintegral_Ioi hσ0

/-- Finite sets of times: sort them into a monotone grid ending at `s`. -/
theorem swExpMart_lintegral_finite (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (γ : ℝ) (s : ℝ≥0) {D : Set ℝ≥0} (hD : D.Finite) (hDs : ∀ t ∈ D, t ≤ s) :
    ∫⁻ ω, ⨆ t ∈ D, ‖swExpMart B γ t ω - 1‖ₑ ∂P ≤
      2 * ENNReal.ofReal (√(rexp (γ ^ 2 * s) - 1)) := by
  set F := hD.toFinset with hF
  set e := F.orderEmbOfFin rfl
  set u : ℕ → ℝ≥0 := fun k => if h : k < F.card then e ⟨k, h⟩ else s with hu_def
  have hu : Monotone u := by
    intro i j hij
    simp only [hu_def]
    split_ifs with hi hj hj
    · exact e.monotone (Fin.mk_le_mk.2 hij)
    · exact hDs _ (hD.mem_toFinset.1 (F.orderEmbOfFin_mem rfl _))
    · omega
    · exact le_rfl
  have hun : u F.card ≤ s := by simp [hu_def]
  refine le_trans (lintegral_mono fun ω => ?_) (swExpMart_grid_lintegral hB hBm hu γ F.card hun)
  refine iSup₂_le fun t ht => ?_
  have htF : t ∈ Set.range e := by
    rw [Finset.range_orderEmbOfFin]; exact hD.mem_toFinset.2 ht
  obtain ⟨i, rfl⟩ := htF
  have hui : u i.1 = e i := by simp [hu_def, i.2]
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have := Finset.le_sup' (fun k => |swExpMart B γ (u k) ω - 1|)
    (Finset.mem_range.2 (Nat.lt_succ_of_lt i.2))
  rwa [hui] at this

theorem swExpMart_measurable (hBm : ∀ r, Measurable (B r)) (γ : ℝ) (t : ℝ≥0) :
    Measurable fun ω => ‖swExpMart B γ t ω - 1‖ₑ :=
  ((((hBm t).const_mul γ).sub_const _).exp.sub_const 1).enorm

/-- Countable sets of times, measurable `B`: monotone convergence over finite subsets. -/
theorem swExpMart_lintegral_countable (hB : IsPreBrownianReal B P)
    (hBm : ∀ r, Measurable (B r)) (γ : ℝ) (s : ℝ≥0) {D : Set ℝ≥0} (hD : D.Countable)
    (hDs : ∀ t ∈ D, t ≤ s) :
    ∫⁻ ω, ⨆ t ∈ D, ‖swExpMart B γ t ω - 1‖ₑ ∂P ≤
      2 * ENNReal.ofReal (√(rexp (γ ^ 2 * s) - 1)) := by
  rcases D.eq_empty_or_nonempty with hDe | hDne
  · subst hDe; simp
  obtain ⟨f, rfl⟩ := hD.exists_eq_range hDne
  set S : ℕ → Set ℝ≥0 := fun m => f '' Set.Iio m
  have hSfin : ∀ m, (S m).Finite := fun m => (Set.finite_Iio m).image f
  have heq : (fun ω => ⨆ t ∈ Set.range f, ‖swExpMart B γ t ω - 1‖ₑ) =
      fun ω => ⨆ m, ⨆ t ∈ S m, ‖swExpMart B γ t ω - 1‖ₑ := by
    funext ω
    refine le_antisymm (iSup₂_le fun t ht => ?_) (iSup_le fun m => iSup₂_le fun t ht => ?_)
    · obtain ⟨k, rfl⟩ := ht
      exact le_iSup_of_le (k + 1)
        (le_iSup₂_of_le (f := fun t (_ : t ∈ S (k + 1)) => ‖swExpMart B γ t ω - 1‖ₑ) (f k)
          ⟨k, Nat.lt_succ_self k, rfl⟩ le_rfl)
    · obtain ⟨k, _, rfl⟩ := ht
      exact le_iSup₂_of_le (f := fun t (_ : t ∈ Set.range f) => ‖swExpMart B γ t ω - 1‖ₑ) (f k)
        ⟨k, rfl⟩ le_rfl
  rw [heq, lintegral_iSup]
  · exact iSup_le fun m => swExpMart_lintegral_finite hB hBm γ s (hSfin m)
      fun t ht => hDs t (Set.image_subset_range _ _ ht)
  · exact fun m => Measurable.biSup _ (hSfin m).countable
      fun t _ => swExpMart_measurable hBm γ t
  · intro m m' hmm' ω
    exact biSup_mono fun t ht => Set.image_mono (Set.Iio_subset_Iio hmm') ht

/-- **SW-WINSPLIT-ii.** Doob's maximal inequality for the exponential Brownian martingale:
`E sup_{t ∈ D} |exp (γ B_t - γ² t / 2) - 1| ≤ 2 √(exp (γ² s) - 1)` for countable `D ⊆ [0, s]`. -/
theorem lintegral_iSup_expMart_sub_one_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (γ : ℝ) (s : ℝ≥0)
    {D : Set ℝ≥0} (hD : D.Countable) (hDs : ∀ t ∈ D, t ≤ s) :
    ∫⁻ ω, ⨆ t ∈ D, ‖Real.exp (γ * B t ω - γ ^ 2 / 2 * t) - 1‖ₑ ∂P ≤
      2 * ENNReal.ofReal (Real.sqrt (Real.exp (γ ^ 2 * s) - 1)) := by
  set B' : ℝ≥0 → Ω → ℝ := fun t => (hB.aemeasurable t).mk (B t)
  have hB' : IsPreBrownianReal B' P := hB.congr fun t => (hB.aemeasurable t).ae_eq_mk
  have hBm' : ∀ t, Measurable (B' t) := fun t => (hB.aemeasurable t).measurable_mk
  have hae : ∀ᵐ ω ∂P, ∀ t ∈ D, B t ω = B' t ω :=
    (ae_ball_iff hD).2 fun t _ => (hB.aemeasurable t).ae_eq_mk
  refine le_trans (le_of_eq (lintegral_congr_ae ?_))
    (swExpMart_lintegral_countable hB' hBm' γ s hD hDs)
  filter_upwards [hae] with ω hω
  exact iSup_congr fun t => iSup_congr fun ht => by rw [hω t ht]; rfl

/-- Corollary: `E sup_{t ∈ D} exp (γ B_t - γ² t / 2) ≤ 1 + 2 √(exp (γ² s) - 1)`. -/
theorem lintegral_iSup_expMart_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (γ : ℝ) (s : ℝ≥0)
    {D : Set ℝ≥0} (hD : D.Countable) (hDs : ∀ t ∈ D, t ≤ s) :
    ∫⁻ ω, ⨆ t ∈ D, ENNReal.ofReal (Real.exp (γ * B t ω - γ ^ 2 / 2 * t)) ∂P ≤
      1 + 2 * ENNReal.ofReal (Real.sqrt (Real.exp (γ ^ 2 * s) - 1)) := by
  have hpt : ∀ ω, (⨆ t ∈ D, ENNReal.ofReal (Real.exp (γ * B t ω - γ ^ 2 / 2 * t))) ≤
      1 + ⨆ t ∈ D, ‖Real.exp (γ * B t ω - γ ^ 2 / 2 * t) - 1‖ₑ := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    refine le_trans ?_ (add_le_add (le_refl 1) (le_iSup₂_of_le (f := fun t (_ : t ∈ D) =>
      ‖Real.exp (γ * B t ω - γ ^ 2 / 2 * t) - 1‖ₑ) t ht le_rfl))
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (abs_nonneg _)]
    have h1 := le_abs_self (Real.exp (γ * B t ω - γ ^ 2 / 2 * t) - 1)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  exact add_le_add (le_refl 1) (lintegral_iSup_expMart_sub_one_le hB γ s hD hDs)

theorem swExpMart_iSup_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (γ : ℝ) {D : Set ℝ≥0} (hD : D.Countable) :
    AEMeasurable (fun ω => ⨆ t ∈ D, ‖Real.exp (γ * B t ω - γ ^ 2 / 2 * t) - 1‖ₑ) P := by
  set B' : ℝ≥0 → Ω → ℝ := fun t => (hB.aemeasurable t).mk (B t)
  have hBm' : ∀ t, Measurable (B' t) := fun t => (hB.aemeasurable t).measurable_mk
  have hae : ∀ᵐ ω ∂P, ∀ t ∈ D, B t ω = B' t ω :=
    (ae_ball_iff hD).2 fun t _ => (hB.aemeasurable t).ae_eq_mk
  refine ⟨fun ω => ⨆ t ∈ D, ‖swExpMart B' γ t ω - 1‖ₑ,
    Measurable.biSup _ hD fun t _ => swExpMart_measurable hBm' γ t, ?_⟩
  filter_upwards [hae] with ω hω
  exact iSup_congr fun t => iSup_congr fun ht => by rw [hω t ht]; rfl

/-- Corollary: `E inf_{t ∈ D} exp (γ B_t - γ² t / 2) ≥ 1 - 2 √(exp (γ² s) - 1)`. -/
theorem lintegral_iInf_expMart_ge {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (γ : ℝ) (s : ℝ≥0)
    {D : Set ℝ≥0} (hD : D.Countable) (hDs : ∀ t ∈ D, t ≤ s) :
    1 - 2 * ENNReal.ofReal (Real.sqrt (Real.exp (γ ^ 2 * s) - 1)) ≤
      ∫⁻ ω, ⨅ t ∈ D, ENNReal.ofReal (Real.exp (γ * B t ω - γ ^ 2 / 2 * t)) ∂P := by
  set Y : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ D, ‖Real.exp (γ * B t ω - γ ^ 2 / 2 * t) - 1‖ₑ
  have hpt : ∀ ω, 1 - Y ω ≤ ⨅ t ∈ D, ENNReal.ofReal (Real.exp (γ * B t ω - γ ^ 2 / 2 * t)) := by
    intro ω
    refine le_iInf₂ fun t ht => ?_
    refine le_trans (tsub_le_tsub_left (le_iSup₂_of_le (f := fun t (_ : t ∈ D) =>
      ‖Real.exp (γ * B t ω - γ ^ 2 / 2 * t) - 1‖ₑ) t ht le_rfl) 1) ?_
    rw [tsub_le_iff_right, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (exp_pos _).le
      (abs_nonneg _), ← ENNReal.ofReal_one]
    have h1 := neg_abs_le (Real.exp (γ * B t ω - γ ^ 2 / 2 * t) - 1)
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsub := lintegral_sub_le' (μ := P) Y (fun _ => (1 : ℝ≥0∞))
    (swExpMart_iSup_aemeasurable hB γ hD)
  simp only [lintegral_const, measure_univ, mul_one] at hsub
  calc 1 - 2 * ENNReal.ofReal (Real.sqrt (Real.exp (γ ^ 2 * s) - 1))
      ≤ 1 - ∫⁻ ω, Y ω ∂P :=
        tsub_le_tsub_left (lintegral_iSup_expMart_sub_one_le hB γ s hD hDs) 1
    _ ≤ ∫⁻ ω, 1 - Y ω ∂P := hsub
    _ ≤ _ := lintegral_mono hpt

end E6
end QuantumZipper
