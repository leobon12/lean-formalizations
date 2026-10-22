import HigherDimLQGMetric.Main.WeakUniqueness
import HigherDimLQGMetric.KernelIndep.Exponent
import HigherDimLQGMetric.DGZ.Interfaces
import HigherDimLQGMetric.B3.Interfaces
import LQGMetric.Prob.Median
import GaussianLQG.Probability.Medians

/-!
# Real-cutoff and dyadic distance exponents

Packet L10a. The global exponent specializes to each kernel; the dyadic
median bridge is developed in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- A positive random variable's median stays a median after a decreasing logarithmic
change of scale; the two median half-lines exchange roles. -/
theorem l10a_isMedian_log_div_of_neg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hXm : Measurable X) (hXp : ∀ ω, 0 < X ω) {m a : ℝ}
    (hm : 0 < m) (ha : a < 0)
    (hmed : LQGMetric.IsMedian (P.map X) m) :
    LQGMetric.IsMedian (P.map (fun ω => Real.log (X ω) / a)) (Real.log m / a) := by
  have hY : Measurable (fun ω => Real.log (X ω) / a) :=
    (Real.measurable_log.comp hXm).div_const a
  obtain ⟨hl, hr⟩ := (LQGMetric.isMedian_map_iff hXm.aemeasurable).1 hmed
  apply (LQGMetric.isMedian_map_iff hY.aemeasurable).2
  constructor
  · have he : {ω | Real.log (X ω) / a ≤ Real.log m / a} = {ω | m ≤ X ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, div_le_div_right_of_neg ha,
        Real.log_le_log_iff hm (hXp ω)]
    rw [he]
    exact hr
  · have he : {ω | Real.log m / a ≤ Real.log (X ω) / a} = {ω | X ω ≤ m} := by
      ext ω
      simp only [Set.mem_ofPred_eq, div_le_div_right_of_neg ha,
        Real.log_le_log_iff (hXp ω) hm]
    rw [he]
    exact hl

/-- Medians of real random variables converging in probability to a constant
converge to that constant. -/
theorem l10a_medians_tendsto_const {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    {q : ℝ} (hX : ∀ᶠ n in atTop, AEMeasurable (X n) P)
    (hconv : TendstoInMeasure P X atTop (fun _ => q))
    {m : ℕ → ℝ} (hm : ∀ᶠ n in atTop, LQGMetric.IsMedian (P.map (X n)) (m n)) :
    Tendsto m atTop (𝓝 q) := by
  refine GaussianLQG.tendsto_of_isMedian_of_tendstoInMeasure hconv
    hX measurable_const.aemeasurable ?_ hm
  intro r hr
  obtain ⟨hl, hu⟩ := (LQGMetric.isMedian_map_iff measurable_const.aemeasurable).1 hr
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have : {ω : Ω | q ≤ r} = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun _ => not_le.mpr hlt)
    rw [this, measure_empty] at hl
    exact (not_le.mpr LQGMetric.inv_two_pos') hl
  · have : {ω : Ω | r ≤ q} = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun _ => not_le.mpr hgt)
    rw [this, measure_empty] at hu
    exact (not_le.mpr LQGMetric.inv_two_pos') hu

/-- Specialization of the kernel-independent exponent to one admissible kernel. -/
theorem l10a_isKernelExponent_of_isDistanceExponent {d : ℕ} {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ Q : ℝ}
    (hQ : IsDistanceExponent d ξ Q) : IsKernelExponent d κ ξ Q :=
  hQ κ hκ

/-- The chosen exponent satisfies the kernel-specific real-cutoff statement. -/
theorem l10a_distExp_isKernelExponent {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ξ : ℝ} (hξ : 0 < ξ) : IsKernelExponent d κ ξ (distExp d ξ) :=
  l10a_isKernelExponent_of_isDistanceExponent hκ (distExp_isDistanceExponent hd hξ)

/-- The real-cutoff LFPP exponent determines DGZ's dyadic median exponent.
The median step uses the decreasing map `x ↦ log x / log ε` for `ε < 1`. -/
theorem l10a_isDGZExponent_of_isKernelExponent {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ξ Q : ℝ} (hQ : IsKernelExponent d κ ξ Q) :
    DGZ.IsDGZExponent d κ ξ Q := by
  intro Ω _ P W H hH
  have hW := hH.whiteNoise
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  obtain ⟨G, hG⟩ := exists_bandVersion_family hκ hW
  let ε : ℕ → ℝ := fun n => ((2 : ℝ)⁻¹) ^ n
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlt (n : ℕ) (hn : 1 ≤ n) : ε n < 1 := by
    dsimp [ε]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hε : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    · exact Filter.Eventually.of_forall (fun n => hεpos n)
  have hreal := hQ Ω P W hW G hG
  let X : ℕ → Ω → ℝ := fun n ω =>
    Real.log (HigherDimLFPP.lfppDistance d ξ (fun z => G (ε n) z ω)) / Real.log (ε n)
  let m : ℕ → ℝ := fun n => Real.log (DGZ.aQ P H ξ n 2⁻¹) / Real.log (ε n)
  have hconv : TendstoInMeasure P X atTop (fun _ => 1 - ξ * Q) := by
    exact (hreal : TendstoInMeasure P _ (𝓝[>] (0 : ℝ)) _).comp hε
  have hXm : ∀ᶠ n in atTop, AEMeasurable (X n) P := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (((hG (ε n) ⟨hεpos n, hεlt n hn⟩).measurable_lfppDistance ξ).log.div_const _).aemeasurable
  have hmed : ∀ᶠ n in atTop, LQGMetric.IsMedian (P.map (X n)) (m n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hb := hG (ε n) ⟨hεpos n, hεlt n hn⟩
    have hbH : HigherDimLFPP.IsBandVersion P W κ (ε n) 1 (H n) := by
      simpa only [ε, inv_pow] using hH.band n
    let D : Ω → ℝ := fun ω => HigherDimLFPP.lfppDistance d ξ (fun z => G (ε n) z ω)
    have hDm : Measurable D := hb.measurable_lfppDistance ξ
    have hDp : ∀ ω, 0 < D ω := fun ω => HigherDimLFPP.lfppDistance_pos (by omega) (hb.continuous ω)
    let q : ℝ := LQGMetric.lowerQuantile (P.map D) 2⁻¹
    have hqp : 0 < q := hb.lowerQuantile_lfppDistance_pos (by omega) hW ξ
      LQGMetric.inv_two_pos' LQGMetric.inv_two_lt_one'
    letI : IsProbabilityMeasure (P.map D) :=
      (Measure.isProbabilityMeasure_map_iff hDm.aemeasurable).2 inferInstance
    have hmedD : LQGMetric.IsMedian (P.map D) q := LQGMetric.isMedian_lowerMedianLaw
    have hlog : Real.log (ε n) < 0 := Real.log_neg (hεpos n) (hεlt n hn)
    have hmedX := l10a_isMedian_log_div_of_neg hDm hDp hqp hlog hmedD
    have heq : DGZ.aQ P H ξ n 2⁻¹ = q := by
      exact hbH.lowerQuantile_lfppDistance_eq hb hW hW ξ 2⁻¹
    simpa only [X, m, D, heq] using hmedX
  have hmt : Tendsto m atTop (𝓝 (1 - ξ * Q)) :=
    l10a_medians_tendsto_const hXm hconv hmed
  have hlogε : ∀ n : ℕ, Real.log (ε n) = -(n : ℝ) * Real.log 2 := by
    intro n
    simp only [ε, Real.log_pow, Real.log_inv]
    ring_nf
  have hlin : Tendsto (fun n => -(Real.log 2) * m n) atTop
      (𝓝 (-(1 - ξ * Q) * Real.log 2)) := by
    convert hmt.const_mul (-(Real.log 2)) using 1
    ring_nf
  refine hlin.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  dsimp [m]
  rw [hlogε]
  field_simp

/-- The canonical exponent supplies all four standing DGZ hypotheses. -/
theorem l10a_dgzHyp {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ) :
    DGZ.DGZHyp d κ ξ (distExp d ξ) :=
  ⟨hd, hκ, hξ,
    l10a_isDGZExponent_of_isKernelExponent hd hκ
      (l10a_distExp_isKernelExponent hd hκ hξ), hsub⟩

end HigherDimLQGMetric
