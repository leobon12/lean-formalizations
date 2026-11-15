/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafCloseJLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Continuous closed martingales are stable under L¹ approximation

Doob and Borel–Cantelli give a continuous pathwise limit of fast
approximations. L¹ contraction of conditional expectation identifies every
fixed-time value. Null completeness then transfers adaptedness to the limit.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

/-- L¹ convergence of closing variables implies convergence in measure of
their conditional expectations, for any sub-sigma algebra. -/
theorem tendstoInMeasure_condExp_of_L1
    {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ mΩ)
    {Z : Ω → ℝ} {Y : ℕ → Ω → ℝ} (hZ : Integrable Z P)
    (hY : ∀ n, Integrable (Y n) P)
    (hlim : Tendsto (fun n => ∫ ω, ‖Y n ω - Z ω‖ ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => P[Y n | m]) atTop P[Z | m] := by
  have hb (n : ℕ) : eLpNorm (P[Y n | m] - P[Z | m]) 1 P ≤
      ENNReal.ofReal (∫ ω, ‖Y n ω - Z ω‖ ∂P) := by
    calc
      _ = eLpNorm P[Y n - Z | m] 1 P :=
        eLpNorm_congr_ae (condExp_sub (hY n) hZ m).symm
      _ ≤ eLpNorm (Y n - Z) 1 P := eLpNorm_condExp_le_eLpNorm _ le_rfl
      _ = _ := by
        rw [eLpNorm_one_eq_lintegral_enorm]
        exact (ofReal_integral_norm_eq_lintegral_enorm ((hY n).sub hZ)).symm
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    (fun _ => (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable)
    (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => ENNReal.ofReal (∫ ω, ‖Y n ω - Z ω‖ ∂P)) atTop (𝓝 0) from
      by simpa only [ENNReal.ofReal_zero, Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim)
    (fun _ => bot_le) hb

/-- Fast L¹ approximations with continuous closed versions construct a
continuous closed version of the limit. Right continuity of the filtration
and square integrability are unnecessary for this approximation argument. -/
theorem exists_continuous_closed_process_of_fast_L1_approx
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (𝓓 : Filtration ℝ≥0 mΩ) (hn : ∀ t, nullSigma P ≤ 𝓓 t)
    {Z : Ω → ℝ} {Y : ℕ → Ω → ℝ} (hZ : Integrable Z P)
    (hY : ∀ n, Integrable (Y n) P)
    (herr : ∀ n, (∫ ω, ‖Y n ω - Z ω‖ ∂P) ≤ (1 / 4 : ℝ) ^ n)
    (happrox : ∀ n, ∃ M : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 M ∧
      (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
      ∀ t, M t =ᵐ[P] P[Y n | 𝓓 t]) :
    ∃ X : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 X ∧
      (∀ᵐ ω ∂P, Continuous (fun t => X t ω)) ∧
      ∀ t, X t =ᵐ[P] P[Z | 𝓓 t] := by
  have hgood (n : ℕ) : ∃ M : ℝ≥0 → Ω → ℝ, StronglyAdapted 𝓓 M ∧
      (∀ ω, Continuous (fun t => M t ω)) ∧ ∀ t, M t =ᵐ[P] P[Y n | 𝓓 t] := by
    obtain ⟨M, hMa, hMc, hMe⟩ := happrox n
    obtain ⟨M', hM'a, hM'c, _, hM'e⟩ := exists_continuous_closed_version hMa hn hMc hMe
    exact ⟨M', hM'a, hM'c, hM'e⟩
  choose M hMa hMc hMe using hgood
  have hMm (n : ℕ) : Martingale (M n) 𝓓 P :=
    (martingale_condExp (Y n) 𝓓 P).congr (hMa n) (fun t => (hMe n t).symm)
  have hd (n : ℕ) : (∫ ω, ‖Y n ω - Y (n + 1) ω‖ ∂P) ≤ 2 * (1 / 4 : ℝ) ^ n := by
    calc
      _ ≤ ∫ ω, ‖Y n ω - Z ω‖ + ‖Y (n + 1) ω - Z ω‖ ∂P := by
        apply integral_mono ((hY n).sub (hY (n + 1))).norm
          (((hY n).sub hZ).norm.add ((hY (n + 1)).sub hZ).norm)
        intro ω
        dsimp only [Pi.sub_apply, Pi.add_apply]
        simpa only [dist_eq_norm] using dist_triangle_right (Y n ω) (Y (n + 1) ω) (Z ω)
      _ = (∫ ω, ‖Y n ω - Z ω‖ ∂P) + ∫ ω, ‖Y (n + 1) ω - Z ω‖ ∂P :=
        integral_add ((hY n).sub hZ).norm ((hY (n + 1)).sub hZ).norm
      _ ≤ (1 / 4 : ℝ) ^ n + (1 / 4 : ℝ) ^ (n + 1) := add_le_add (herr n) (herr (n + 1))
      _ ≤ _ := by
        rw [pow_succ]
        nlinarith only [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n]
  let X (t : ℝ≥0) (ω : Ω) : ℝ := limUnder atTop fun n => M n t ω
  have hpath : ∀ᵐ ω ∂P, Continuous (fun t => X t ω) ∧
      ∀ t, Tendsto (fun n => M n t ω) atTop (𝓝 (X t ω)) := by
    filter_upwards [ae_eventually_closed_increments_le hMm hMc hY hMe hd] with ω hω
    exact continuous_limUnder_of_local_geometric (fun n => hMc n ω) hω
  have he (t : ℝ≥0) : X t =ᵐ[P] P[Z | 𝓓 t] := by
    have ht : Tendsto (fun n => ∫ ω, ‖Y n ω - Z ω‖ ∂P) atTop (𝓝 0) :=
      squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _) herr
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    have hce := tendstoInMeasure_condExp_of_L1 (𝓓.le t) hZ hY ht
    have hmv : TendstoInMeasure P (fun n => M n t) atTop P[Z | 𝓓 t] :=
      hce.congr (fun n => (hMe n t).symm) EventuallyEq.rfl
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_ae
        (fun n => ((hMa n t).mono (𝓓.le t)).aestronglyMeasurable)
        (hpath.mono fun _ hω => hω.2 t)) hmv
  have hXm (t : ℝ≥0) : Measurable (X t) :=
    (StronglyMeasurable.limUnder fun n => (hMa n t).mono (𝓓.le t)).measurable
  refine ⟨X, fun t => ?_, hpath.mono fun _ hω => hω.1, he⟩
  apply Measurable.stronglyMeasurable
  exact Sec2.Restart.measurable_of_ae_eq_of_null (𝓓.le t)
    (fun A hA hA0 => hn t A (MeasurableSpace.measurableSet_generateFrom ⟨hA, hA0⟩))
    stronglyMeasurable_condExp.measurable (hXm t) (he t).symm

end InteractingSLE.WFS
