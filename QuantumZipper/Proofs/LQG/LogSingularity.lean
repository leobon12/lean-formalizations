import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.LQG.Atomless
import QuantumZipper.Proofs.LQG.FractionalMoments

/-!
# M4-P4: boundary log singularities of strength `α < Q`

Blueprint `M4_BLUEPRINT.md`, node M4-P4 (boundary part).

For `s ∈ ℝ` and `α ∈ ℝ` let `ψ(v) = α (−log ‖v − s‖)` and `Y = Z + ofFun ψ`.

* (i) `bdryApprox_add_log`: for regular `x`, exactly
  `bdryApprox γ (x + ofFun ψ) k = max(2^{-k}, |t−s|)^{−αγ/2} · bdryApprox γ x k`.
* (ii) `isVagueLimitOnR_add_log`: away from `s`, if `bdryApprox γ x → ν` then
  `bdryApprox γ (x + ofFun ψ) → |t−s|^{−αγ/2} ν` vaguely on `ℝ \ {s}` (LocalRule).
* (iii) `isVagueLimitR_of_local_of_tight`: local convergence on `ℝ \ {s}` plus uniform smallness
  of the approximations near `s` give global vague convergence, with no atom at `s`;
  `tight_of_annuli` derives the uniform smallness from summable dyadic annulus bounds; and
  `ae_logSingularity` assembles the a.s. statement, taking the M4-P3(b) fractional-moment bound
  (not yet built) as the explicit hypothesis `P3bBound`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace LogSing

open GoodSample Positivity GaussTK

/-- The log potential `ψ(v) = α (−log ‖v − s‖)`. -/
def logPot (α s : ℝ) (v : ℂ) : ℝ := α * -Real.log ‖v - s‖

/-! ### (i) The exact mean-value identity -/

theorem circPot_real_div_two {r : ℝ} (t s : ℝ) :
    CircleCont.circPot r (t : ℂ) (s : ℂ) / 2 = -Real.log (max r |t - s|) := by
  unfold CircleCont.circPot
  rw [Complex.conj_ofReal, KernelId.norm_ofReal_sub]
  ring

theorem avgReg_add_log {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (α s : ℝ) (k : ℕ) (t : ℝ) :
    avgReg (x + ofFun (logPot α s)) k t =
      avgReg x k t + α * -Real.log (max (radius k) |t - s|) := by
  have h := hF.add_ofFun_log' α s
  rw [show ofFun (logPot α s) = ofFun fun v => α * -Real.log ‖v - s‖ from rfl,
    h.avgReg_eq k (ofReal_mem_Hbar t), hF.avgReg_eq k (ofReal_mem_Hbar t)]
  simp only
  rw [circPot_real_div_two]

/-- The density factor `max(2^{-k}, |t−s|)^{−αγ/2}`. -/
def logFactor (γ α s : ℝ) (k : ℕ) (t : ℝ) : ℝ := max (radius k) |t - s| ^ (-(α * γ / 2))

theorem measurable_logFactor (γ α s : ℝ) (k : ℕ) : Measurable (logFactor γ α s k) := by
  unfold logFactor
  exact (continuous_const.max (continuous_id.sub continuous_const).abs).measurable.pow_const _

/-- **(i) Mean-value identity**: `bdryApprox γ (x + ofFun ψ) k = max(2^{-k},|t−s|)^{−αγ/2} ν_k`. -/
theorem bdryApprox_add_log {x : FieldSample} (hx : IsRegularSample x) (γ α s : ℝ) (k : ℕ) :
    bdryApprox γ (x + ofFun (logPot α s)) k =
      (bdryApprox γ x k).withDensity fun t => ENNReal.ofReal (logFactor γ α s k t) := by
  obtain ⟨F, hF⟩ := hx
  have hm : Measurable fun t : ℝ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg x k t)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (((RegClosure.measurable_avgReg_slice x k).comp
        Complex.continuous_ofReal.measurable).const_mul _).exp)
  unfold bdryApprox
  rw [← withDensity_mul _ hm (measurable_logFactor γ α s k).ennreal_ofReal]
  congr 1
  funext t
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (radius_pos k).le _)
    (Real.exp_pos _).le), avgReg_add_log hF α s k t]
  congr 1
  have hm0 : 0 < max (radius k) |t - s| := lt_max_of_lt_left (radius_pos k)
  unfold logFactor
  rw [Real.rpow_def_of_pos hm0, mul_add, Real.exp_add]
  ring_nf

/-! ### (ii) Away from the singularity -/

theorem isVagueLimitR_restrict {νs : ℕ → Measure ℝ} {ν : Measure ℝ} (h : IsVagueLimitR νs ν)
    {U : Set ℝ} (hU : IsOpen U) : IsVagueLimitOnR U νs (ν.restrict U) := by
  obtain ⟨hloc, ht⟩ := h
  refine ⟨by rw [Measure.restrict_apply' hU.measurableSet]; simp, fun K hK _ => ?_,
    fun f hf hfc hfU => ?_⟩
  · exact (Measure.restrict_apply_le _ _).trans_lt hK.measure_lt_top
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h => ht (hfU h)]
    exact ht f hf hfc

theorem continuousOn_logPot (α s : ℝ) :
    ContinuousOn (logPot α s) ({u : ℂ | u ≠ s} ∩ Hbar) := by
  unfold logPot
  refine continuousOn_const.mul (ContinuousOn.neg ?_)
  refine ((continuous_id.sub continuous_const).norm.continuousOn).log fun u hu => ?_
  exact norm_ne_zero_iff.2 (sub_ne_zero.2 hu.1)

theorem isOpen_ne_real (s : ℝ) : IsOpen {u : ℂ | u ≠ s} := isOpen_ne

/-- **(ii)** Away from `s`, the measure of `x + ofFun ψ` is `|t−s|^{−αγ/2} ν`. -/
theorem isVagueLimitOnR_add_log {x : FieldSample} (hx : IsRegularSample x) {γ : ℝ}
    {ν : Measure ℝ} (hν : IsVagueLimitR (bdryApprox γ x) ν) (α s : ℝ) :
    IsVagueLimitOnR {s}ᶜ (bdryApprox γ (x + ofFun (logPot α s)))
      ((ν.restrict {s}ᶜ).withDensity fun t => ENNReal.ofReal (|t - s| ^ (-(α * γ / 2)))) := by
  have hU : IsOpen ({s}ᶜ : Set ℝ) := isOpen_compl_singleton
  have h := LocalRule.isVagueLimitOnR_add_ofFun hx hU (isVagueLimitR_restrict hν hU)
    (isOpen_ne_real s) (fun t ht => by
      simp only [mem_setOf_eq, ne_eq, Complex.ofReal_inj]; exact ht)
    (continuousOn_logPot α s)
  convert h using 1
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hU.measurableSet] with t ht
  have hts : 0 < |t - s| := abs_pos.2 (sub_ne_zero.2 ht)
  unfold logPot
  rw [KernelId.norm_ofReal_sub, Real.rpow_def_of_pos hts]
  congr 2
  ring

/-! ### (iii-a) Global vague convergence from local convergence and tightness at `s` -/

/-- Cut-off vanishing on `|t − s| ≤ 1/(j+1)` and equal to `1` on `|t − s| ≥ 2/(j+1)`. -/
def cutS (s : ℝ) (j : ℕ) (t : ℝ) : ℝ := max 0 (min 1 (((j : ℝ) + 1) * |t - s| - 1))

/-- Trapezoid equal to `1` on `|t − s| ≤ δ/2` and vanishing on `|t − s| ≥ δ`. -/
def trapS (s δ : ℝ) (t : ℝ) : ℝ := max 0 (min 1 (2 * (δ - |t - s|) / δ))

section Cut

variable {s : ℝ} {j : ℕ} {t : ℝ}

theorem continuous_cutS : Continuous (cutS s j) := by unfold cutS; fun_prop

theorem cutS_nonneg : 0 ≤ cutS s j t := le_max_left _ _

theorem cutS_le_one : cutS s j t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem cutS_eq_zero (h : |t - s| ≤ 1 / ((j : ℝ) + 1)) : cutS s j t = 0 := by
  unfold cutS
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have := mul_le_mul_of_nonneg_left h hj.le
  rw [mul_one_div_cancel hj.ne'] at this
  exact max_eq_left (min_le_of_right_le (by linarith))

theorem cutS_eq_one (h : 2 / ((j : ℝ) + 1) ≤ |t - s|) : cutS s j t = 1 := by
  unfold cutS
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have : 2 ≤ ((j : ℝ) + 1) * |t - s| := by rw [div_le_iff₀ hj] at h; linarith
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem cutS_mono (s t : ℝ) : Monotone fun j => cutS s j t := by
  intro i j hij
  have h1 : (i : ℝ) ≤ j := Nat.cast_le.2 hij
  have : ((i : ℝ) + 1) * |t - s| ≤ ((j : ℝ) + 1) * |t - s| :=
    mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

theorem tsupport_cutS_subset (s : ℝ) (j : ℕ) :
    tsupport (cutS s j) ⊆ {t | 1 / ((j : ℝ) + 1) ≤ |t - s|} :=
  closure_minimal (fun t ht => by
    by_contra h
    exact ht (cutS_eq_zero (not_le.1 h).le))
    (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)

theorem tsupport_mul_cutS_subset (f : ℝ → ℝ) (s : ℝ) (j : ℕ) :
    tsupport (fun t => f t * cutS s j t) ⊆ {s}ᶜ := by
  refine (tsupport_mul_subset_right).trans ((tsupport_cutS_subset s j).trans fun t ht h => ?_)
  rw [mem_singleton_iff] at h
  simp only [mem_setOf_eq, h, sub_self, abs_zero] at ht
  have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  linarith

theorem exists_cutS_lt {δ : ℝ} (hδ : 0 < δ) : ∃ j : ℕ, 2 / ((j : ℝ) + 1) < δ := by
  obtain ⟨j, hj⟩ := exists_nat_gt (2 / δ)
  refine ⟨j, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hj
  nlinarith

theorem continuous_trapS (s δ : ℝ) : Continuous (trapS s δ) := by unfold trapS; fun_prop

theorem trapS_nonneg {δ : ℝ} : 0 ≤ trapS s δ t := le_max_left _ _

theorem trapS_eq_one {δ : ℝ} (hδ : 0 < δ) (h : |t - s| ≤ δ / 2) : trapS s δ t = 1 := by
  unfold trapS
  have : 1 ≤ 2 * (δ - |t - s|) / δ := by rw [le_div_iff₀ hδ]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem trapS_eq_zero {δ : ℝ} (hδ : 0 < δ) (h : δ ≤ |t - s|) : trapS s δ t = 0 := by
  unfold trapS
  have : 2 * (δ - |t - s|) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  exact max_eq_left (min_le_of_right_le this)

theorem hasCompactSupport_trapS {δ : ℝ} (hδ : 0 < δ) : HasCompactSupport (trapS s δ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := s - δ) (b := s + δ)) fun t ht => ?_
  apply trapS_eq_zero hδ
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

end Cut

/-- The limit has mass at most `ε` near `s` if the approximations do. -/
theorem measure_Icc_le_of_tight {νs : ℕ → Measure ℝ} {ν : Measure ℝ} {s : ℝ}
    (hloc : IsVagueLimitOnR {s}ᶜ νs ν) (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k))
    {δ : ℝ} (hδ : 0 < δ) {ε : ℝ≥0∞} (hε : ∀ k, νs k (Ioo (s - δ) (s + δ)) ≤ ε) :
    ν (Icc (s - δ / 2) (s + δ / 2)) ≤ ε := by
  have hs0 : ν {s} = 0 := by simpa using hloc.1
  set h : ℕ → ℝ → ℝ := fun j t => trapS s δ t * cutS s j t with hhdef
  have hhc : ∀ j, Continuous (h j) := fun j => (continuous_trapS s δ).mul continuous_cutS
  have hhcs : ∀ j, HasCompactSupport (h j) := fun j => (hasCompactSupport_trapS hδ).mul_right
  have hhU : ∀ j, tsupport (h j) ⊆ {s}ᶜ := fun j => tsupport_mul_cutS_subset _ s j
  have hh0 : ∀ j t, 0 ≤ h j t := fun j t => mul_nonneg trapS_nonneg cutS_nonneg
  have hIoo : ∀ j t, ENNReal.ofReal (h j t) ≤ (Ioo (s - δ) (s + δ)).indicator 1 t := by
    intro j t
    by_cases ht : |t - s| < δ
    · have hm : t ∈ Ioo (s - δ) (s + δ) := by
        rw [abs_lt] at ht; constructor <;> linarith
      rw [indicator_of_mem hm, Pi.one_apply, ENNReal.ofReal_le_one]
      exact mul_le_one₀ (max_le zero_le_one (min_le_left _ _)) cutS_nonneg cutS_le_one
    · simp only [hhdef, trapS_eq_zero hδ (not_lt.1 ht), zero_mul, ENNReal.ofReal_zero]
      exact zero_le
  -- each cut-off test function
  have hj : ∀ j, ∫⁻ t, ENNReal.ofReal (h j t) ∂ν ≤ ε := by
    intro j
    have hint : Integrable (h j) ν :=
      integrable_of_tsupport hloc.2.1 (hhc j) (hhcs j) (hhU j)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (hh0 j))]
    have hlim := (ENNReal.continuous_ofReal.tendsto _).comp (hloc.2.2 _ (hhc j) (hhcs j) (hhU j))
    refine le_of_tendsto' hlim fun k => ?_
    have := hfin k
    simp only [Function.comp]
    rw [ofReal_integral_eq_lintegral_ofReal ((hhc j).integrable_of_hasCompactSupport (hhcs j))
      (ae_of_all _ (hh0 j))]
    calc ∫⁻ t, ENNReal.ofReal (h j t) ∂νs k
        ≤ ∫⁻ t, (Ioo (s - δ) (s + δ)).indicator 1 t ∂νs k := lintegral_mono (hIoo j)
      _ = νs k (Ioo (s - δ) (s + δ)) := lintegral_indicator_one measurableSet_Ioo
      _ ≤ ε := hε k
  -- monotone convergence
  have hmono : Monotone fun j t => ENNReal.ofReal (h j t) := by
    intro i j hij t
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (cutS_mono s t hij) trapS_nonneg)
  have htrap : ∫⁻ t, ENNReal.ofReal (trapS s δ t) ∂ν ≤ ε := by
    calc ∫⁻ t, ENNReal.ofReal (trapS s δ t) ∂ν
        ≤ ∫⁻ t, ⨆ j, ENNReal.ofReal (h j t) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hs0] with t ht
          have hts : 0 < |t - s| := abs_pos.2 (sub_ne_zero.2 ht)
          obtain ⟨j, hj⟩ := exists_cutS_lt hts
          refine le_iSup_of_le j (le_of_eq ?_)
          simp only [hhdef, cutS_eq_one hj.le, mul_one]
      _ = ⨆ j, ∫⁻ t, ENNReal.ofReal (h j t) ∂ν :=
          lintegral_iSup (fun j => ((hhc j).measurable).ennreal_ofReal) hmono
      _ ≤ ε := iSup_le hj
  calc ν (Icc (s - δ / 2) (s + δ / 2))
      = ∫⁻ t, (Icc (s - δ / 2) (s + δ / 2)).indicator 1 t ∂ν :=
        (lintegral_indicator_one measurableSet_Icc).symm
    _ ≤ ∫⁻ t, ENNReal.ofReal (trapS s δ t) ∂ν := by
        refine lintegral_mono fun t => ?_
        by_cases ht : t ∈ Icc (s - δ / 2) (s + δ / 2)
        · rw [indicator_of_mem ht, Pi.one_apply, trapS_eq_one hδ (abs_le.2
            ⟨by linarith [ht.1], by linarith [ht.2]⟩), ENNReal.ofReal_one]
        · rw [indicator_of_notMem ht]; exact zero_le
    _ ≤ ε := htrap

theorem abs_integral_sub_mul_cutS_le {μ : Measure ℝ} [IsFiniteMeasureOnCompacts μ]
    {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) {M : ℝ}
    (hM : ∀ t, ‖f t‖ ≤ M) {s δ : ℝ} {j : ℕ} (hj : 2 / ((j : ℝ) + 1) < δ / 2) {ε' : ℝ}
    (hε' : 0 ≤ ε') (hμ : μ (Icc (s - δ / 2) (s + δ / 2)) ≤ ENNReal.ofReal ε') :
    |∫ t, f t ∂μ - ∫ t, f t * cutS s j t ∂μ| ≤ |M| * ε' := by
  rw [← integral_sub (f := f) (g := fun t => f t * cutS s j t) (hf.integrable_of_hasCompactSupport hfc)
    ((hf.mul continuous_cutS).integrable_of_hasCompactSupport hfc.mul_right)]
  have hδ2 : 0 < δ / 2 := lt_trans (by positivity) hj
  set A := Icc (s - δ / 2) (s + δ / 2) with hA
  have hpt : ∀ t, ‖f t - f t * cutS s j t‖ ≤ A.indicator (fun _ => |M|) t := by
    intro t
    have hfM : |f t| ≤ |M| := (by simpa using hM t : |f t| ≤ M).trans (le_abs_self M)
    by_cases ht : t ∈ A
    · rw [indicator_of_mem ht, Real.norm_eq_abs,
        show f t - f t * cutS s j t = f t * (1 - cutS s j t) by ring, abs_mul,
        abs_of_nonneg (sub_nonneg.2 cutS_le_one)]
      calc |f t| * (1 - cutS s j t) ≤ |f t| * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [(cutS_nonneg : 0 ≤ cutS s j t)])
              (abs_nonneg _)
        _ ≤ |M| := by rw [mul_one]; exact hfM
    · rw [indicator_of_notMem ht]
      have h2 : 2 / ((j : ℝ) + 1) ≤ |t - s| := by
        simp only [hA, mem_Icc, not_and_or, not_le] at ht
        rcases ht with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [cutS_eq_one h2]; simp
  have hint : Integrable (A.indicator fun _ => |M|) μ :=
    (continuous_const.integrableOn_Icc (μ := μ)).integrable_indicator measurableSet_Icc
  calc |∫ t, (f t - f t * cutS s j t) ∂μ| = ‖∫ t, (f t - f t * cutS s j t) ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, A.indicator (fun _ => |M|) t ∂μ := norm_integral_le_of_norm_le hint (ae_of_all _ hpt)
    _ = μ.real A * |M| := by rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    _ ≤ ε' * |M| := mul_le_mul_of_nonneg_right
        (by rw [measureReal_def]; exact ENNReal.toReal_le_of_le_ofReal hε' hμ) (abs_nonneg _)
    _ = |M| * ε' := mul_comm _ _

/-- **Global vague convergence** from vague convergence on `ℝ \ {s}` and uniform smallness of the
approximations near `s`. The limit has no atom at `s`. -/
theorem isVagueLimitR_of_local_of_tight {νs : ℕ → Measure ℝ} {ν : Measure ℝ} {s : ℝ}
    (hloc : IsVagueLimitOnR {s}ᶜ νs ν) (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k))
    (htight : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ k, νs k (Ioo (s - δ) (s + δ)) ≤ ENNReal.ofReal ε) :
    IsVagueLimitR νs ν := by
  have hsm : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, (∀ k, νs k (Ioo (s - δ) (s + δ)) ≤ ENNReal.ofReal ε) ∧
      ν (Icc (s - δ / 2) (s + δ / 2)) ≤ ENNReal.ofReal ε := fun ε hε => by
    obtain ⟨δ, hδ, h⟩ := htight ε hε
    exact ⟨δ, hδ, h, measure_Icc_le_of_tight hloc hfin hδ h⟩
  have hK : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    obtain ⟨δ, hδ, -, hν⟩ := hsm 1 one_pos
    have h1 : K ⊆ (K \ Ioo (s - δ / 2) (s + δ / 2)) ∪ Icc (s - δ / 2) (s + δ / 2) :=
      fun t ht => by
        by_cases h : t ∈ Ioo (s - δ / 2) (s + δ / 2)
        · exact Or.inr (Ioo_subset_Icc_self h)
        · exact Or.inl ⟨ht, h⟩
    refine (measure_mono h1).trans_lt ((measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.2 ⟨?_, hν.trans_lt ENNReal.ofReal_lt_top⟩))
    refine hloc.2.1 _ (hK.diff isOpen_Ioo) fun t ht h => ht.2 ?_
    rw [mem_singleton_iff.1 h]
    constructor <;> linarith⟩
  refine ⟨inferInstance, fun f hf hfc => ?_⟩
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε' := ε / (4 * (|M| + 1)) with hε'def
  have hε' : 0 < ε' := by positivity
  have hMε : |M| * ε' ≤ ε / 4 := by
    rw [hε'def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg M]
  obtain ⟨δ, hδ, hk, hν⟩ := hsm ε' hε'
  obtain ⟨j, hj⟩ := exists_cutS_lt (by linarith : 0 < δ / 2)
  have hgU := tsupport_mul_cutS_subset f s j
  have hconv := hloc.2.2 (fun t => f t * cutS s j t) (hf.mul continuous_cutS) hfc.mul_right hgU
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hconv (ε / 2) (by positivity)
  refine ⟨N, fun k hkN => ?_⟩
  have := hfin k
  have e1 := abs_integral_sub_mul_cutS_le (μ := νs k) hf hfc hM hj hε'.le
    ((measure_mono (Icc_subset_Ioo (a₂ := s - δ) (b₂ := s + δ) (a₁ := s - δ / 2) (b₁ := s + δ / 2) (by linarith)
      (by linarith))).trans (hk k))
  have e2 := abs_integral_sub_mul_cutS_le (μ := ν) hf hfc hM hj hε'.le hν
  have e3 := hN k hkN
  rw [Real.dist_eq] at e3 ⊢
  calc |∫ t, f t ∂νs k - ∫ t, f t ∂ν|
      ≤ |∫ t, f t ∂νs k - ∫ t, f t * cutS s j t ∂νs k| +
        |∫ t, f t * cutS s j t ∂νs k - ∫ t, f t * cutS s j t ∂ν| +
        |∫ t, f t * cutS s j t ∂ν - ∫ t, f t ∂ν| := by
        have := abs_sub_le (∫ t, f t ∂νs k) (∫ t, f t * cutS s j t ∂νs k) (∫ t, f t ∂ν)
        have := abs_sub_le (∫ t, f t * cutS s j t ∂νs k) (∫ t, f t * cutS s j t ∂ν)
          (∫ t, f t ∂ν)
        linarith
    _ < ε / 4 + ε / 2 + ε / 4 := by
        rw [abs_sub_comm (∫ t, f t * cutS s j t ∂ν)]
        linarith
    _ = ε := by ring

/-! ### (iii-b) Uniform smallness near `s` from dyadic interval bounds -/

/-- The dyadic interval `I_n = [s − 2^{-n}, s + 2^{-n}]`. -/
def annI (s : ℝ) (n : ℕ) : Set ℝ := Icc (s - radius n) (s + radius n)

/-- The exponent `b = α⁺ γ / 2`. -/
def expB (γ α : ℝ) : ℝ := max α 0 * γ / 2

/-- The weight `w_n = 2^{(n+1) b}`. -/
def annW (γ α : ℝ) (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (radius (n + 1) ^ (-expB γ α))

/-- `T_n = sup_{k ≥ n} ν_k(I_n)`. -/
def annT (νZ : ℕ → Measure ℝ) (s : ℝ) (n : ℕ) : ℝ≥0∞ := ⨆ j, νZ (j + n) (annI s n)

theorem radius_zero' : radius 0 = 1 := by simp [radius]

theorem expB_nonneg {γ : ℝ} (hγ : 0 < γ) (α : ℝ) : 0 ≤ expB γ α :=
  div_nonneg (mul_nonneg (le_max_right _ _) hγ.le) zero_le_two

theorem rpow_neg_le_of_le {γ α r x : ℝ} (hγ : 0 < γ) (hr : 0 < r) (hrx : r ≤ x) (hx1 : x ≤ 1) :
    x ^ (-(α * γ / 2)) ≤ r ^ (-expB γ α) := by
  unfold expB
  rcases le_or_gt 0 α with hα | hα
  · rw [max_eq_left hα]
    exact Real.rpow_le_rpow_of_nonpos hr hrx (by nlinarith)
  · rw [max_eq_right hα.le, zero_mul, zero_div, neg_zero, Real.rpow_zero]
    exact Real.rpow_le_one (hr.le.trans hrx) hx1 (by nlinarith)

theorem radius_rpow_mono {γ : ℝ} (hγ : 0 < γ) (α : ℝ) {j k : ℕ} (h : j ≤ k) :
    radius j ^ (-expB γ α) ≤ radius k ^ (-expB γ α) :=
  Real.rpow_le_rpow_of_nonpos (radius_pos k) (AreaExist.aradius_anti h)
    (neg_nonpos.2 (expB_nonneg hγ α))

theorem le_annT (νZ : ℕ → Measure ℝ) (s : ℝ) {n k : ℕ} (h : n ≤ k) :
    νZ k (annI s n) ≤ annT νZ s n :=
  le_iSup_of_le (k - n) (by rw [Nat.sub_add_cancel h])

theorem mem_annI {s t : ℝ} {n : ℕ} (h : |t - s| ≤ radius n) : t ∈ annI s n := by
  obtain ⟨h1, h2⟩ := abs_sub_le_iff.1 h
  exact ⟨by linarith, by linarith⟩

theorem logFactor_le_of_near {γ α s : ℝ} (hγ : 0 < γ) {k : ℕ} {t : ℝ}
    (h : |t - s| ≤ radius k) : logFactor γ α s k t ≤ radius k ^ (-expB γ α) := by
  unfold logFactor
  rw [max_eq_left h]
  exact rpow_neg_le_of_le hγ (radius_pos k) le_rfl (BdryExist.radius_le_one k)

theorem withDensity_logFactor_le_near {γ α s : ℝ} (hγ : 0 < γ) (μ : Measure ℝ) {k m : ℕ}
    (hkm : k ≤ m) :
    μ.withDensity (fun t => ENNReal.ofReal (logFactor γ α s k t))
        (Ioo (s - radius m) (s + radius m)) ≤
      ENNReal.ofReal (radius k ^ (-expB γ α)) * μ (Ioo (s - radius m) (s + radius m)) := by
  rw [withDensity_apply _ measurableSet_Ioo, ← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun t ht =>
    ENNReal.ofReal_le_ofReal (logFactor_le_of_near hγ ?_)
  have : |t - s| < radius m := abs_lt.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact this.le.trans (AreaExist.aradius_anti hkm)

theorem logFactor_le_sum {γ α s : ℝ} (hγ : 0 < γ) {k m : ℕ} (hmk : m < k) {t : ℝ}
    (ht : |t - s| < radius m) :
    ENNReal.ofReal (logFactor γ α s k t) ≤
      (∑ n ∈ Finset.Ico m k, annW γ α n * (annI s n).indicator 1 t) +
        ENNReal.ofReal (radius k ^ (-expB γ α)) * (annI s k).indicator 1 t := by
  classical
  by_cases hd : |t - s| ≤ radius k
  · rw [indicator_of_mem (mem_annI hd), Pi.one_apply, mul_one]
    exact le_add_left (ENNReal.ofReal_le_ofReal (logFactor_le_of_near hγ hd))
  · push_neg at hd
    have hk1 : radius (k - 1 + 1) ≤ |t - s| := by rw [Nat.sub_add_cancel (by omega)]; exact hd.le
    have hex : ∃ n, radius (n + 1) ≤ |t - s| := ⟨k - 1, hk1⟩
    set n := Nat.find hex with hn
    have hn1 : radius (n + 1) ≤ |t - s| := Nat.find_spec hex
    have hnk : n < k := by
      have := Nat.find_min' hex hk1
      omega
    have hmn : m ≤ n := by
      by_contra h
      push_neg at h
      have := AreaExist.aradius_anti (show n + 1 ≤ m by omega)
      linarith
    have hdn : |t - s| ≤ radius n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, radius_zero']; linarith [BdryExist.radius_le_one m]
      · have := Nat.find_min hex (show n - 1 < n by omega)
        rw [Nat.sub_add_cancel hpos] at this
        exact (not_le.1 this).le
    refine le_add_right (le_trans ?_ (Finset.single_le_sum (f := fun i =>
      annW γ α i * (annI s i).indicator 1 t) (fun i _ => zero_le)
      (Finset.mem_Ico.2 ⟨hmn, hnk⟩)))
    rw [indicator_of_mem (mem_annI hdn), Pi.one_apply, mul_one]
    unfold annW logFactor
    rw [max_eq_right hd.le]
    exact ENNReal.ofReal_le_ofReal (rpow_neg_le_of_le hγ (radius_pos _) hn1
      (by linarith [BdryExist.radius_le_one m]))

theorem withDensity_logFactor_le_far {γ α s : ℝ} (hγ : 0 < γ) (μ : Measure ℝ) {k m : ℕ}
    (hmk : m < k) :
    μ.withDensity (fun t => ENNReal.ofReal (logFactor γ α s k t))
        (Ioo (s - radius m) (s + radius m)) ≤
      (∑ n ∈ Finset.Ico m k, annW γ α n * μ (annI s n)) +
        ENNReal.ofReal (radius k ^ (-expB γ α)) * μ (annI s k) := by
  have hmeas : ∀ n, MeasurableSet (annI s n) := fun n => measurableSet_Icc
  have hg : Measurable fun t => (∑ n ∈ Finset.Ico m k, annW γ α n * (annI s n).indicator 1 t) +
      ENNReal.ofReal (radius k ^ (-expB γ α)) * (annI s k).indicator 1 t :=
    (Finset.measurable_sum _ fun n _ => (measurable_one.indicator (hmeas n)).const_mul _).add
      ((measurable_one.indicator (hmeas k)).const_mul _)
  rw [withDensity_apply _ measurableSet_Ioo]
  calc ∫⁻ t in Ioo (s - radius m) (s + radius m), ENNReal.ofReal (logFactor γ α s k t) ∂μ
      ≤ ∫⁻ t in Ioo (s - radius m) (s + radius m),
          ((∑ n ∈ Finset.Ico m k, annW γ α n * (annI s n).indicator 1 t) +
            ENNReal.ofReal (radius k ^ (-expB γ α)) * (annI s k).indicator 1 t) ∂μ :=
        setLIntegral_mono hg fun t ht => logFactor_le_sum hγ hmk
          (abs_lt.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    _ ≤ ∫⁻ t, ((∑ n ∈ Finset.Ico m k, annW γ α n * (annI s n).indicator 1 t) +
            ENNReal.ofReal (radius k ^ (-expB γ α)) * (annI s k).indicator 1 t) ∂μ :=
        setLIntegral_le_lintegral _ _
    _ = _ := by
        rw [lintegral_add_left (Finset.measurable_sum _ fun n _ =>
            (measurable_one.indicator (hmeas n)).const_mul _),
          lintegral_finset_sum _ fun n _ => (measurable_one.indicator (hmeas n)).const_mul _,
          lintegral_const_mul _ (measurable_one.indicator (hmeas k)),
          lintegral_indicator_one (hmeas k)]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [lintegral_const_mul _ (measurable_one.indicator (hmeas n)),
          lintegral_indicator_one (hmeas n)]

/-- **Uniform smallness near `s`** of `ν^Y_k = max(2^{-k},|t−s|)^{−αγ/2} ν^Z_k`, from a
summable tail of `w_n T_n`. -/
theorem tight_of_annuli {γ α s : ℝ} (hγ : 0 < γ) {νZ : ℕ → Measure ℝ}
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (νZ k)) (hnull : ∀ k, νZ k {s} = 0) {N : ℕ}
    (hsum : ∑' n, annW γ α (n + N) * annT νZ s (n + N) ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ k,
      (νZ k).withDensity (fun t => ENNReal.ofReal (logFactor γ α s k t))
        (Ioo (s - δ) (s + δ)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  set a : ℕ → ℝ≥0∞ := fun n => annW γ α n * annT νZ s n with ha
  set tail : ℕ → ℝ≥0∞ := fun i => ∑' j, a (j + i + N) with htail
  have hF1 : Tendsto tail atTop (𝓝 0) := by
    have := ENNReal.tendsto_sum_nat_add (fun n => a (n + N)) hsum
    simpa only [htail] using this
  have hF2 : ∀ i k, i + N ≤ k → a k ≤ tail i := fun i k hik => by
    have := ENNReal.le_tsum (f := fun j => a (j + i + N)) (k - i - N)
    simpa only [show k - i - N + i + N = k by omega] using this
  have hF3 : ∀ i k, ∑ n ∈ Finset.Ico (i + N) k, a n ≤ tail i := fun i k => by
    rw [Finset.sum_Ico_eq_sum_range]
    refine le_trans (le_of_eq ?_) (ENNReal.sum_le_tsum (Finset.range (k - (i + N))))
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ha]
    congr 2 <;> omega
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (radius k ^ (-expB γ α)) with hc
  have hck : ∀ k, c k * νZ k (annI s k) ≤ a k := fun k =>
    mul_le_mul' (ENNReal.ofReal_le_ofReal (radius_rpow_mono hγ α (Nat.le_succ k)))
      (le_annT νZ s le_rfl)
  have hcont : ∀ k, Tendsto (fun m => c k * νZ k (Ioo (s - radius m) (s + radius m))) atTop
      (𝓝 0) := by
    intro k
    have := hfin k
    have h := tendsto_measure_iInter_atTop (μ := νZ k)
      (s := fun m => Ioo (s - radius m) (s + radius m))
      (fun m => measurableSet_Ioo.nullMeasurableSet)
      (fun i j hij => Ioo_subset_Ioo (by linarith [AreaExist.aradius_anti hij])
        (by linarith [AreaExist.aradius_anti hij]))
      ⟨0, ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne⟩
    have hI : (⋂ m, Ioo (s - radius m) (s + radius m)) = {s} := by
      ext t
      simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
      constructor
      · intro h'
        by_contra hts
        have hpos : 0 < |t - s| := abs_pos.2 (sub_ne_zero.2 hts)
        obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2 : ℝ)⁻¹ < 1)
        have hm' : radius m < |t - s| := hm
        have := h' m
        have : |t - s| < radius m := abs_lt.2 ⟨by linarith [this.1], by linarith [this.2]⟩
        linarith
      · rintro rfl m
        have := radius_pos m
        constructor <;> linarith
    rw [hI, hnull k] at h
    have h2 := ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.ofReal_ne_top (r := radius k ^
      (-expB γ α))))
    rw [mul_zero] at h2
    exact h2
  have hε2 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 (by linarith)
  have hee : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
  have he : ENNReal.ofReal (ε / 2) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)
  have hev1 : ∀ᶠ i in atTop, tail i ≤ ENNReal.ofReal (ε / 2) :=
    hF1.eventually (eventually_le_nhds hε2)
  obtain ⟨i0, hi0⟩ := hev1.exists
  set K0 := i0 + N with hK0
  have hev2 : ∀ᶠ i in atTop, i0 ≤ i ∧ tail i ≤ ENNReal.ofReal (ε / 2) ∧
      ∀ k ∈ Finset.range K0,
        c k * νZ k (Ioo (s - radius (i + N)) (s + radius (i + N))) ≤ ENNReal.ofReal ε := by
    refine (eventually_ge_atTop i0).and (hev1.and ((Filter.eventually_all_finset _).2
      fun k _ => ?_))
    exact ((hcont k).comp (tendsto_add_atTop_nat N)).eventually
      (eventually_le_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨i1, hi1, hi1', hi2⟩ := hev2.exists
  refine ⟨radius (i1 + N), radius_pos _, fun k => ?_⟩
  rcases lt_or_ge (i1 + N) k with hmk | hkm
  · calc (νZ k).withDensity (fun t => ENNReal.ofReal (logFactor γ α s k t))
          (Ioo (s - radius (i1 + N)) (s + radius (i1 + N)))
        ≤ (∑ n ∈ Finset.Ico (i1 + N) k, annW γ α n * νZ k (annI s n)) +
            c k * νZ k (annI s k) := withDensity_logFactor_le_far hγ _ hmk
      _ ≤ (∑ n ∈ Finset.Ico (i1 + N) k, a n) + a k := by
          refine add_le_add (Finset.sum_le_sum fun n hn => ?_) (hck k)
          exact mul_le_mul_of_nonneg_left (le_annT νZ s (Finset.mem_Ico.1 hn).2.le) zero_le
      _ ≤ tail i1 + tail i1 := add_le_add (hF3 i1 k) (hF2 i1 k hmk.le)
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hi1' hi1'
      _ = ENNReal.ofReal ε := hee
  · have hnear := withDensity_logFactor_le_near (α := α) (s := s) hγ (νZ k) hkm
    by_cases hk0 : k < K0
    · exact hnear.trans (hi2 k (Finset.mem_range.2 hk0))
    · push_neg at hk0
      calc _ ≤ c k * νZ k (Ioo (s - radius (i1 + N)) (s + radius (i1 + N))) := hnear
        _ ≤ c k * νZ k (annI s k) := by
            refine mul_le_mul_of_nonneg_left (measure_mono ?_) zero_le
            refine Ioo_subset_Icc_self.trans (Icc_subset_Icc ?_ ?_) <;>
              linarith [AreaExist.aradius_anti hkm]
        _ ≤ a k := hck k
        _ ≤ tail i0 := hF2 i0 k hk0
        _ ≤ ENNReal.ofReal (ε / 2) := hi0
        _ ≤ ENNReal.ofReal ε := he

/-! ### (iii-c) The almost sure statement, under the M4-P3(b) bound -/

theorem radius_rpow (j : ℕ) (x : ℝ) : radius j ^ x = (2 : ℝ) ^ (-(j : ℝ) * x) := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num),
    Real.rpow_natCast]
  unfold radius
  rw [inv_pow]

/-- The geometric series behind "`α < Q − γp/2`". -/
theorem summable_annuli {b e p : ℝ} (hp : 0 ≤ p) (hneg : b * p + e < 0) :
    Summable fun n : ℕ => (radius (n + 1) ^ (-b)) ^ p * (2 : ℝ) ^ ((n : ℝ) * e) := by
  have hr : (2 : ℝ) ^ (b * p + e) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
  refine ((summable_geometric_of_lt_one (by positivity) hr).mul_left
    ((2 : ℝ) ^ (b * p))).congr fun n => ?_
  rw [radius_rpow, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul
    (by norm_num), ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  ring

section Prob

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

open BdryExist (zField)

/-- **The M4-P3(b) bound at `s`**, for the normalized field `Z = zField X R`, in the blueprint's
form with the supremum inside: for every `p ∈ (0,1]` and all large `n`,
`E (sup_{k ≥ n} ν_{2^{-k}}(s + 2^{-n}[−1,1]))^p ≤ C 2^{n(γ²p²/4 − p(1+γ²/4))}`
(discharged from `FracMom.fracMoment_dyadic` in `p3bBound`). -/
def P3bBound (P : Measure Ω) (X : Ω → FieldSample) (γ R s : ℝ) : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∫⁻ ω, annT (bdryApprox γ (zField X R ω)) s n ^ p ∂P ≤
      C * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 4 - p * (1 + γ ^ 2 / 4))))

theorem measurable_annT (hX : IsFreeGFFModConstH X P) (γ R s : ℝ) (n : ℕ) :
    Measurable fun ω => annT (bdryApprox γ (zField X R ω)) s n :=
  Measurable.iSup fun j => (Measure.measurable_coe measurableSet_Icc).comp
    ((measurable_bdryApprox γ _).comp (BdryExist.measurable_zField hX R))

/-- A.s. the weighted interval masses have a summable tail. -/
theorem ae_summable_tail [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (R : ℝ) {α : ℝ} (hα : α < Qc γ) (s : ℝ) (hP3 : P3bBound P X γ R s) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∑' n, annW γ α (n + N) *
      annT (bdryApprox γ (zField X R ω)) s (n + N) ≠ ⊤ := by
  set αp := max α 0 with hαp
  have hQ : γ * Qc γ = 2 + γ ^ 2 / 2 := by unfold Qc; field_simp
  have hQpos : 0 < Qc γ := by unfold Qc; positivity
  have hαQ : αp < Qc γ := max_lt hα hQpos
  set p := min 1 ((Qc γ - αp) / γ) with hpdef
  have hp0 : 0 < p := lt_min one_pos (div_pos (by linarith) hγ)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hpγ : γ * p ≤ Qc γ - αp := by
    have := min_le_right 1 ((Qc γ - αp) / γ)
    rw [le_div_iff₀ hγ] at this; linarith
  set e := γ ^ 2 * p ^ 2 / 4 - p * (1 + γ ^ 2 / 4) with he
  have hneg : expB γ α * p + e < 0 := by
    have hin : αp * γ / 2 + γ ^ 2 * p / 4 - 1 - γ ^ 2 / 4 < 0 := by
      have h1 : γ * (γ * p) ≤ γ * (Qc γ - αp) := mul_le_mul_of_nonneg_left hpγ hγ.le
      have h2 : γ * (αp - Qc γ) < 0 := mul_neg_of_pos_of_neg hγ (by linarith)
      nlinarith
    have : expB γ α * p + e = p * (αp * γ / 2 + γ ^ 2 * p / 4 - 1 - γ ^ 2 / 4) := by
      rw [he]; unfold expB; ring
    rw [this]
    exact mul_neg_of_pos_of_neg hp0 hin
  obtain ⟨C, hC, n₀, hbd⟩ := hP3 p hp0 hp1
  set T : ℕ → Ω → ℝ≥0∞ := fun n ω => annT (bdryApprox γ (zField X R ω)) s n with hT
  set u : ℕ → ℝ := fun n => (radius (n + 1) ^ (-expB γ α)) ^ p * (2 : ℝ) ^ ((n : ℝ) * e)
    with hu
  have hu0 : ∀ n, 0 ≤ u n := fun n =>
    mul_nonneg (Real.rpow_nonneg (Real.rpow_nonneg (radius_pos _).le _) _) (by positivity)
  have husum : Summable u := summable_annuli hp0.le hneg
  have hmeas : ∀ n, Measurable fun ω => (annW γ α (n + n₀) * T (n + n₀) ω) ^ p := fun n =>
    (measurable_const.mul (measurable_annT hX γ R s _)).pow_const p
  have hterm : ∀ n, ∫⁻ ω, (annW γ α (n + n₀) * T (n + n₀) ω) ^ p ∂P ≤
      C * ENNReal.ofReal (u (n + n₀)) := by
    intro n'
    set n := n' + n₀ with hn
    have hw : annW γ α n ^ p = ENNReal.ofReal ((radius (n + 1) ^ (-expB γ α)) ^ p) :=
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (radius_pos _).le _) hp0.le
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, hw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal ((radius (n + 1) ^ (-expB γ α)) ^ p) * ∫⁻ ω, T n ω ^ p ∂P
        ≤ ENNReal.ofReal ((radius (n + 1) ^ (-expB γ α)) ^ p) *
            (C * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * e))) := by
          gcongr; exact hbd n (Nat.le_add_left _ _)
      _ = C * ENNReal.ofReal (u n) := by
          rw [hu, ENNReal.ofReal_mul (Real.rpow_nonneg (Real.rpow_nonneg (radius_pos _).le _) _)]
          ring
  have hsumE : ∑' n, ∫⁻ ω, (annW γ α (n + n₀) * T (n + n₀) ω) ^ p ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => hu0 _)
      ((summable_nat_add_iff n₀).2 husum)]
    exact ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ ω ∂P, ∑' n, (annW γ α (n + n₀) * T (n + n₀) ω) ^ p < ⊤ := by
    refine ae_lt_top' (AEMeasurable.ennreal_tsum fun n => (hmeas n).aemeasurable) ?_
    rw [lintegral_tsum fun n => (hmeas n).aemeasurable]
    exact hsumE
  filter_upwards [hlt] with ω hω
  set b : ℕ → ℝ≥0∞ := fun n => (annW γ α (n + n₀) * T (n + n₀) ω) ^ p with hb
  have hb0 : Tendsto b atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  obtain ⟨N, hN⟩ := (hb0.eventually (eventually_le_nhds zero_lt_one)).exists_forall_of_atTop
  refine ⟨N + n₀, ne_top_of_le_ne_top hω.ne ?_⟩
  calc ∑' n, annW γ α (n + (N + n₀)) * T (n + (N + n₀)) ω ≤ ∑' n, b (n + N) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        rw [← Nat.add_assoc]
        have h1 : b (n + N) ≤ 1 := hN (n + N) (Nat.le_add_left _ _)
        have ha1 : annW γ α (n + N + n₀) * T (n + N + n₀) ω ≤ 1 := by
          by_contra h
          push_neg at h
          exact absurd h1 (not_le.2 (ENNReal.one_lt_rpow h hp0))
        calc annW γ α (n + N + n₀) * T (n + N + n₀) ω =
              (annW γ α (n + N + n₀) * T (n + N + n₀) ω) ^ (1 : ℝ) :=
              (ENNReal.rpow_one _).symm
          _ ≤ b (n + N) := ENNReal.rpow_le_rpow_of_exponent_ge ha1 hp1
    _ ≤ ∑' n, b n := ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective N) b

theorem isFiniteMeasureOnCompacts_bdryApprox {x : FieldSample} (hx : IsRegularSample x)
    (γ : ℝ) (k : ℕ) : IsFiniteMeasureOnCompacts (bdryApprox γ x k) := by
  obtain ⟨F, hF⟩ := hx
  exact ⟨fun K hK => by
    rw [← bdryR_radius γ hF k]
    exact bdryR_lt_top γ hF (by rw [one_mul]; exact radius_pos k) hK⟩

theorem bdryApprox_singleton (γ : ℝ) (x : FieldSample) (k : ℕ) (s : ℝ) :
    bdryApprox γ x k {s} = 0 := by
  unfold bdryApprox
  exact withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- **M4-P4 (boundary)**, under the M4-P3(b) bound. For `α < Q`, a.s. the field
`Y = Z + α(−log|·−s|)` has a boundary measure along the dyadic radii; it equals
`|t−s|^{−αγ/2} ν_Z` (restricted to `ℝ \ {s}`); it has no atom at `s`; and
`ν_Y((s−δ,s+δ)) → 0` as `δ → 0`. -/
theorem ae_logSingularity [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) {α : ℝ} (hα : α < Qc γ) (s : ℝ)
    (hP3 : P3bBound P X γ R s) :
    ∀ᵐ ω ∂P,
      IsVagueLimitR (bdryApprox γ (zField X R ω + ofFun (logPot α s)))
          (qBoundaryMeasure γ (zField X R ω + ofFun (logPot α s))) ∧
        qBoundaryMeasure γ (zField X R ω + ofFun (logPot α s)) =
          ((qBoundaryMeasure γ (zField X R ω)).restrict {s}ᶜ).withDensity
            (fun t => ENNReal.ofReal (|t - s| ^ (-(α * γ / 2)))) ∧
        qBoundaryMeasure γ (zField X R ω + ofFun (logPot α s)) {s} = 0 ∧
        Tendsto (fun δ => qBoundaryMeasure γ (zField X R ω + ofFun (logPot α s))
          (Ioo (s - δ) (s + δ))) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_summable_tail hX hγ R hα s hP3, RegSample.ae_isRegularSample hX,
    BdryExist.ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω hsum hreg hν
  obtain ⟨N, hN⟩ := hsum
  have hZ : IsRegularSample (zField X R ω) := hreg.addConst' _
  have hY : IsRegularSample (zField X R ω + ofFun (logPot α s)) := hZ.add_ofFun_log' α s
  set ν' := ((qBoundaryMeasure γ (zField X R ω)).restrict {s}ᶜ).withDensity
    (fun t => ENNReal.ofReal (|t - s| ^ (-(α * γ / 2)))) with hν'
  have hloc := isVagueLimitOnR_add_log hZ hν α s
  have htight := tight_of_annuli hγ (isFiniteMeasureOnCompacts_bdryApprox hZ γ)
    (fun k => bdryApprox_singleton γ _ k s) hN
  simp_rw [← bdryApprox_add_log hZ γ α s] at htight
  have hglob : IsVagueLimitR (bdryApprox γ (zField X R ω + ofFun (logPot α s))) ν' :=
    isVagueLimitR_of_local_of_tight hloc (isFiniteMeasureOnCompacts_bdryApprox hY γ) htight
  have hq := qBoundaryMeasure_eq hglob
  rw [hq]
  have hs0 : ν' {s} = 0 := by
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply (measurableSet_singleton s), inter_compl_self, measure_empty]
  refine ⟨hglob, rfl, hs0, ?_⟩
  have := hglob.1
  have h := tendsto_measure_biInter_gt (μ := ν') (s := fun δ => Ioo (s - δ) (s + δ)) (a := 0)
    (fun r _ => measurableSet_Ioo.nullMeasurableSet)
    (fun i j _ hij => Ioo_subset_Ioo (by linarith) (by linarith))
    ⟨1, one_pos, ((measure_mono Ioo_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne⟩
  have hI : (⋂ r > (0 : ℝ), Ioo (s - r) (s + r)) = {s} := by
    ext t
    simp only [mem_iInter, mem_Ioo, mem_singleton_iff]
    constructor
    · intro h'
      by_contra hts
      have hpos : 0 < |t - s| := abs_pos.2 (sub_ne_zero.2 hts)
      have := h' |t - s| hpos
      rcases abs_cases (t - s) with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at this <;>
        linarith [this.1, this.2]
    · rintro rfl r hr
      constructor <;> linarith
  rw [hI, hs0] at h
  exact h

/-- **M4-P4 in the interface of M4-P5** (`Atomless.LogSingNoAtom`, strength `α = γ < Q`, with
an added continuous `g`), under the M4-P3(b) bound at every point. -/
theorem logSingNoAtom_of_P3b [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hP3 : ∀ R : ℝ, 0 < R → ∀ s : ℝ, |s| + 1 ≤ R → P3bBound P X γ R s) :
    Atomless.LogSingNoAtom X P γ := by
  intro R hR s hs g hg
  have hαQ : γ < Qc γ := by
    unfold Qc
    have : γ / 2 < 2 / γ := by rw [lt_div_iff₀ hγ]; nlinarith
    linarith
  filter_upwards [ae_logSingularity hX hγ hγ2 R hαQ s (hP3 R hR s hs),
    RegSample.ae_isRegularSample hX] with ω hω hreg
  obtain ⟨hglob, -, hs0, -⟩ := hω
  have hY : IsRegularSample (zField X R ω + ofFun (logPot γ s)) :=
    (hreg.addConst' _).add_ofFun_log' γ s
  have h := LocalRule.isVagueLimitR_add_ofFun hY hglob isOpen_univ (fun t => mem_univ _)
    hg.continuousOn
  have hq := qBoundaryMeasure_eq h
  show IsVagueLimitR (bdryApprox γ (zField X R ω + ofFun (logPot γ s) + ofFun g))
      (qBoundaryMeasure γ (zField X R ω + ofFun (logPot γ s) + ofFun g)) ∧
    qBoundaryMeasure γ (zField X R ω + ofFun (logPot γ s) + ofFun g) {s} = 0
  rw [hq]
  exact ⟨h, withDensity_absolutelyContinuous _ _ hs0⟩

/-- **The P3(b) bound from M4-P3** (`FracMom.fracMoment_dyadic`), for `|s| + 1 ≤ R`. -/
theorem p3bBound [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : |s| + 1 ≤ R) : P3bBound P X γ R s := by
  intro p hp0 hp1
  obtain ⟨C, hC0, hC⟩ := FracMom.fracMoment_dyadic hX hγ hγ2 hR hp0 hp1
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, 2, fun n hn => ?_⟩
  have hrn : 4 * radius n ≤ 1 := by
    have h2 : radius n ≤ radius 2 := AreaExist.aradius_anti hn
    have : radius 2 = 1 / 4 := by simp [radius]; norm_num
    linarith
  obtain ⟨h1, -⟩ := hC n s (by linarith)
  have hsub : annI s n ⊆ FracMom.bI s (4 * radius n) := by
    unfold annI FracMom.bI
    exact Icc_subset_Icc (by linarith [radius_pos n]) (by linarith [radius_pos n])
  calc ∫⁻ ω, annT (bdryApprox γ (zField X R ω)) s n ^ p ∂P
      ≤ ∫⁻ ω, (⨆ m, bdryApprox γ (zField X R ω) (n + m) (FracMom.bI s (4 * radius n))) ^ p ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (iSup_le fun j => le_iSup_of_le j (by
          rw [add_comm j n]; exact measure_mono hsub)) hp0.le
    _ ≤ _ := h1
    _ = _ := by
        rw [ENNReal.ofReal_mul hC0, show (-(n : ℝ) * p * (1 + γ ^ 2 / 4) + n * (γ ^ 2 * p ^ 2 / 4))
          = (n : ℝ) * (γ ^ 2 * p ^ 2 / 4 - p * (1 + γ ^ 2 / 4)) by ring]

/-- **M4-P4 in the interface of M4-P5**, unconditional. -/
theorem logSingNoAtom [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : Atomless.LogSingNoAtom X P γ :=
  logSingNoAtom_of_P3b hX hγ hγ2 fun _ hR _ hs => p3bBound hX hγ hγ2 hR hs

end Prob

end LogSing
end QuantumZipper
