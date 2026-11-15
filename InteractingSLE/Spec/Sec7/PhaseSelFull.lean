/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux117

/-!
# §7.4, Aux. lemma 122 before a stopping lifetime, part 1: Laurent extraction up to the lifetime

Packet PROVE-STRIPSYS5 (specification §7.4, Aux. lemma 122, `source/spec/p385-432.md` L104–L131: "Consider a
continuous Loewner trace from zero in `ℍ`, with continuous driver and positive stopping lifetime `T`, in a usual
filtration. Retain a stopped Gaussian field kernel whose harmonic mean `M_t(z)` is a continuous local martingale until
`z` is swallowed").

The landed Theorem 2.4 converse (`MartChar.martingale_driftProc_quadProc_of_couplingMean`) assumes the coupling means
to be local martingales before swallowing at **all** times, and a deterministic initial word. Here:

* `setIntegral_indicator_stoppedProcess_eq`: a local martingale before `ζ`, stopped at a stopping time
  `τ ≤ ζ` (equality allowed: then the process must be left-continuous at `τ`) and restricted to an `𝓕₀`-event `E` on
  which it is bounded up to `τ`, has constant set integrals;
* `martingale_driftProc_quadProc_of_setIntegral`: the Laurent extraction of the landed proof with its two inputs made
  hypotheses — the set-integral constancy of the explicit coupling means stopped at `τ` (at every far point), and a
  bound `K` of the coordinates up to `τ`. No deterministic initial word and no particular `τ` are used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelFull

open MartChar

section LocalMart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **A local martingale before `ζ`, stopped at a stopping time `τ ≤ ζ` and restricted to an `𝓕₀`-event on
which it is bounded up to `τ`, has constant set integrals.** Unlike the landed
`MartChar.setIntegral_stoppedProcess_eq_of_isLocalMartingaleBefore`, `τ` may reach `ζ`; the process is then required to
be left-continuous at the stopped times on `E`. -/
theorem setIntegral_indicator_stoppedProcess_eq [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → ℝ} {ζ τ : Ω → WithTop ℝ≥0} (hX : IsLocalMartingaleBefore 𝓕 P ζ X)
    (hrc : ∀ ω (s : ℝ≥0), (s : WithTop ℝ≥0) < ζ ω → ContinuousWithinAt (X · ω) (Ici s) s)
    (hτ : IsStoppingTime 𝓕 τ) {E : Set Ω} (hE : MeasurableSet[𝓕 0] E) (hτζ : ∀ ω ∈ E, τ ω ≤ ζ ω)
    (hlc : ∀ ω ∈ E, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ τ ω → ContinuousWithinAt (X · ω) (Iic u) u)
    {C : ℝ} (hC : ∀ ω ∈ E, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → |X t ω| ≤ C) :
    (∀ t, Integrable (E.indicator (stoppedProcess X τ t)) P) ∧
      ∀ s t : ℝ≥0, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
        ∫ ω in A, E.indicator (stoppedProcess X τ t) ω ∂P =
          ∫ ω in A, E.indicator (stoppedProcess X τ s) ω ∂P := by
  obtain ⟨σ, -, hσζ, hσlim, hσmart⟩ := hX
  set Z : ℕ → ℝ≥0 → Ω → ℝ := fun n => stoppedProcess (stoppedProcess X (σ n)) τ with hZ
  have hZmart : ∀ n, Martingale (Z n) 𝓕 P := fun n =>
    Martingale.stoppedProcess_of_rightContinuous (hσmart n)
      (continuousWithinAt_stoppedProcess (hσζ n) hrc) hτ
  set θ : ℝ≥0 → Ω → ℝ≥0 := fun t ω => (min (t : WithTop ℝ≥0) (τ ω)).untopA with hθ
  have hθτ : ∀ t ω, ((θ t ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := fun t ω => by
    simp only [hθ]
    rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  have hXτ : ∀ t ω, stoppedProcess X τ t ω = X (θ t ω) ω := fun t ω => rfl
  have hZval : ∀ n t ω, Z n t ω = X (min ((θ t ω : ℝ≥0) : WithTop ℝ≥0) (σ n ω)).untopA ω :=
    fun n t ω => rfl
  have hmin_le : ∀ n t ω, (((min ((θ t ω : ℝ≥0) : WithTop ℝ≥0) (σ n ω)).untopA : ℝ≥0) : WithTop ℝ≥0)
      ≤ τ ω := fun n t ω => by
    rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
    exact (min_le_left _ _).trans (hθτ t ω)
  -- the bounds on `E`
  have hZbd : ∀ n t, ∀ ω ∈ E, |Z n t ω| ≤ C := fun n t ω hω => by
    rw [hZval]; exact hC ω hω _ (hmin_le n t ω)
  have hXbd : ∀ t, ∀ ω ∈ E, |stoppedProcess X τ t ω| ≤ C := fun t ω hω => by
    rw [hXτ]; exact hC ω hω _ (hθτ t ω)
  -- convergence on `E`
  have hlim : ∀ᵐ ω ∂P, ω ∈ E → ∀ t, Tendsto (fun n => Z n t ω) atTop (𝓝 (stoppedProcess X τ t ω)) := by
    filter_upwards [hσlim] with ω hω hωE t
    set u : ℝ≥0 := θ t ω with hu
    have huζ : (u : WithTop ℝ≥0) ≤ ζ ω := (hθτ t ω).trans (hτζ ω hωE)
    have hconv : Tendsto (fun n => (min (u : WithTop ℝ≥0) (σ n ω)).untopA) atTop (𝓝[≤] u) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun r hr => ?_, fun r hr => ?_⟩,
        Eventually.of_forall fun n => ?_⟩
      · have hrζ : (r : WithTop ℝ≥0) < ζ ω := (WithTop.coe_lt_coe.2 hr).trans_le huζ
        filter_upwards [hω r hrζ] with n hn
        have h1 : (r : WithTop ℝ≥0) < min (u : WithTop ℝ≥0) (σ n ω) :=
          lt_min (WithTop.coe_lt_coe.2 hr) hn
        rw [← coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))] at h1
        exact WithTop.coe_lt_coe.1 h1
      · refine Eventually.of_forall fun n => lt_of_le_of_lt ?_ hr
        have h1 : (((min (u : WithTop ℝ≥0) (σ n ω)).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ u := by
          rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
          exact min_le_left _ _
        exact WithTop.coe_le_coe.1 h1
      · show (min (u : WithTop ℝ≥0) (σ n ω)).untopA ∈ Iic u
        have h1 : (((min (u : WithTop ℝ≥0) (σ n ω)).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ u := by
          rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
          exact min_le_left _ _
        exact WithTop.coe_le_coe.1 h1
    have hc := (hlc ω hωE u (hθτ t ω)).tendsto.comp hconv
    rw [hXτ]
    exact hc
  have hZm : ∀ n t, StronglyMeasurable[mΩ] (Z n t) := fun n t => ((hZmart n).1 t).mono (𝓕.le t)
  have hE' : MeasurableSet E := 𝓕.le 0 E hE
  have hlimI : ∀ t, ∀ᵐ ω ∂P, Tendsto (fun n => E.indicator (Z n t) ω) atTop
      (𝓝 (E.indicator (stoppedProcess X τ t) ω)) := fun t => by
    filter_upwards [hlim] with ω hω
    by_cases hωE : ω ∈ E
    · simp only [Set.indicator_of_mem hωE]; exact hω hωE t
    · simp only [Set.indicator_of_notMem hωE]; exact tendsto_const_nhds
  have hmeas : ∀ t, AEStronglyMeasurable (E.indicator (stoppedProcess X τ t)) P := fun t =>
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => ((hZm n t).indicator hE').aestronglyMeasurable) (hlimI t)
  have hIbd : ∀ t ω, ‖E.indicator (stoppedProcess X τ t) ω‖ ≤ |C| := fun t ω => by
    by_cases hωE : ω ∈ E
    · rw [Set.indicator_of_mem hωE, Real.norm_eq_abs]; exact (hXbd t ω hωE).trans (le_abs_self C)
    · rw [Set.indicator_of_notMem hωE, norm_zero]; exact abs_nonneg C
  have hZIbd : ∀ n t ω, ‖E.indicator (Z n t) ω‖ ≤ |C| := fun n t ω => by
    by_cases hωE : ω ∈ E
    · rw [Set.indicator_of_mem hωE, Real.norm_eq_abs]; exact (hZbd n t ω hωE).trans (le_abs_self C)
    · rw [Set.indicator_of_notMem hωE, norm_zero]; exact abs_nonneg C
  refine ⟨fun t => Integrable.of_bound (hmeas t) |C| (Eventually.of_forall (hIbd t)),
    fun s t hst A hA => ?_⟩
  have hdct : ∀ v, Tendsto (fun n => ∫ ω in A, E.indicator (Z n v) ω ∂P) atTop
      (𝓝 (∫ ω in A, E.indicator (stoppedProcess X τ v) ω ∂P)) := fun v =>
    tendsto_integral_of_dominated_convergence (fun _ => |C|)
      (fun n => ((hZm n v).indicator hE').aestronglyMeasurable.restrict) (integrable_const |C|)
      (fun n => Eventually.of_forall fun ω => hZIbd n v ω) (ae_restrict_of_ae (hlimI v))
  have heq : ∀ n, ∫ ω in A, E.indicator (Z n t) ω ∂P = ∫ ω in A, E.indicator (Z n s) ω ∂P := by
    intro n
    have hAE : MeasurableSet[𝓕 s] (A ∩ E) := hA.inter (𝓕.mono bot_le E hE)
    have h := (hZmart n).setIntegral_eq hst hAE
    rw [setIntegral_indicator hE', setIntegral_indicator hE']
    exact h.symm
  exact tendsto_nhds_unique ((hdct t).congr heq) (hdct s)

end LocalMart

section Extract

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The Laurent-coefficient processes are martingales up to `τ`** (the extraction of the landed
`MartChar.martingale_driftProc_quadProc_of_couplingMean`, with its two inputs made hypotheses): for a stopping time
`τ ≤ T` up to which the coordinates are bounded by `K`, if every explicit coupling mean `𝔥(z)` at a far point
(`laurentRadius K T ≤ ‖z‖`), stopped at `τ`, has constant set integrals, then `N^τ` and `Q^τ` are martingales. -/
theorem martingale_driftProc_quadProc_of_setIntegral [IsProbabilityMeasure P] {κ : ℝ}
    (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω)
    (hVLc : ∀ i ω, Continuous fun t => VL i t ω) (hVRc : ∀ i ω, Continuous fun t => VR i t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) {T : ℝ≥0}
    (hτT : ∀ ω, τ ω ≤ T) {K : ℝ}
    (hbd : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → |W t ω| ≤ K ∧ ∀ j, |jointV VL VR j t ω| ≤ K)
    (hset : ∀ z ∈ H, laurentRadius K T ≤ ‖z‖ →
      (∀ t, Integrable (stoppedProcess (coupProc κ ρL ρR W VL VR z) τ t) P) ∧
        ∀ s t : ℝ≥0, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
          ∫ ω in A, stoppedProcess (coupProc κ ρL ρR W VL VR z) τ t ω ∂P
            = ∫ ω in A, stoppedProcess (coupProc κ ρL ρR W VL VR z) τ s ω ∂P) :
    Martingale (stoppedProcess (driftProc (jointρ ρL ρR) W (jointV VL VR)) τ) 𝓕 P ∧
      Martingale (stoppedProcess (quadProc κ (jointρ ρL ρR) W (jointV VL VR)) τ) 𝓕 P := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  set c : ℝ := Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i) with hc
  set R := laurentRadius K T with hR
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hsk : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  -- stopped times and bounds
  set θ : ℝ≥0 → Ω → ℝ≥0 := fun u ω => (min (u : WithTop ℝ≥0) (τ ω)).untopA with hθ
  have hθτ : ∀ u ω, ((θ u ω : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := fun u ω => by
    simp only [hθ]
    rw [coe_untopA_of_ne_top (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _))]
    exact min_le_right _ _
  have hθT : ∀ u ω, (θ u ω : ℝ) ≤ T := fun u ω => by
    have := (hθτ u ω).trans (hτT ω)
    exact_mod_cast (WithTop.coe_le_coe.1 this)
  have hbd' : ∀ u ω, |W (θ u ω) ω| ≤ K ∧ ∀ j, |V j (θ u ω) ω| ≤ K := fun u ω => hbd ω _ (hθτ u ω)
  have hpb : ∀ u ω, ∀ r ∈ Icc (0 : ℝ) (θ u ω), |wpath W ω r| ≤ K := fun u ω r hr =>
    (hbd ω _ ((WithTop.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)).trans (hθτ u ω))).1
  have hw0 : ∀ ω, wpath W ω 0 = 0 := fun ω => by simp [wpath, hW0]
  -- the identity at stopped times
  have hstop : ∀ (z : ℂ), z ∈ H → R ≤ ‖z‖ → ∀ u ω,
      stoppedProcess (coupProc κ ρL ρR W VL VR z) τ u ω
        = c + harmPart κ ρ (wpath W ω) (θ u ω) (fun j => V j (θ u ω) ω) z := by
    intro z hzH hzR u ω
    have hR4 : K + 3 * Real.sqrt T + 1 ≤ ‖z‖ :=
      (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
    have hns : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) (θ u ω) := by
      refine mem_diff_fwdHull_of_norm (continuous_wpath hWc ω) (NNReal.coe_nonneg _) (hpb u ω)
        hzH ?_
      have := Real.sqrt_le_sqrt (hθT u ω)
      linarith
    show coupProc κ ρL ρR W VL VR z (θ u ω) ω = _
    rw [coupProc_eq hWc hordL hordR le_rfl hns, jointV_apply_eq]
  -- the radii
  set Y : ℕ → ℝ := fun k => (k : ℝ) + R with hY
  have hR1 : 1 ≤ R := one_le_laurentRadius K T
  have hYR : ∀ k, R ≤ Y k := fun k => by simp only [hY]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hYpos : ∀ k, 0 < Y k := fun k => by linarith [hYR k]
  have hYtop : Tendsto Y atTop atTop := tendsto_atTop_add_const_right _ R tendsto_natCast_atTop_atTop
  have hzI : ∀ k, ((Y k : ℂ) * Complex.I) ∈ H ∧ R ≤ ‖(Y k : ℂ) * Complex.I‖ := fun k => by
    refine ⟨?_, ?_⟩
    · show 0 < ((Y k : ℂ) * Complex.I).im
      simp [hYpos k]
    · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hYpos k)]
      exact hYR k
  have hzD : ∀ k, ((Y k : ℂ) * (1 + Complex.I)) ∈ H ∧ R ≤ ‖(Y k : ℂ) * (1 + Complex.I)‖ :=
    fun k => by
      refine ⟨?_, ?_⟩
      · show 0 < ((Y k : ℂ) * (1 + Complex.I)).im
        simp [hYpos k]
      · have h1I : (1 : ℝ) ≤ ‖(1 : ℂ) + Complex.I‖ := by
          have h := Complex.abs_re_le_norm ((1 : ℂ) + Complex.I)
          simp only [Complex.add_re, Complex.one_re, Complex.I_re, add_zero, abs_one] at h
          exact h
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hYpos k)]
        nlinarith [hYR k, hYpos k]
  -- the two coupling processes at the radii
  have hI := fun k => hset _ (hzI k).1 (hzI k).2
  have hD := fun k => hset _ (hzD k).1 (hzD k).2
  -- adaptedness and integrability of `N^τ`, `Q^τ`
  have hNc : ∀ ω, Continuous fun t => driftProc ρ W V t ω := fun ω => by
    simp only [driftProc, driftValue]
    exact (continuous_const.mul (hWc ω)).add (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (hVc j ω))
  have hQc : ∀ ω, Continuous fun t => quadProc κ ρ W V t ω := fun ω => by
    simp only [quadProc, quadValue]
    exact (((hWc ω).pow 2).add (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((hVc j ω).pow 2)))).sub
      (continuous_const.mul NNReal.continuous_coe)
  have hNa : StronglyAdapted 𝓕 (driftProc ρ W V) := fun t => by
    have h1 := (hWa t).measurable
    have h2 := fun j => ((hVa j) t).measurable
    have : Measurable[𝓕 t] (driftProc ρ W V t) := by
      show Measurable[𝓕 t] fun ω => 2 * W t ω + ∑ j, ρ j * V j t ω
      fun_prop
    exact this.stronglyMeasurable
  have hQa : StronglyAdapted 𝓕 (quadProc κ ρ W V) := fun t => by
    have h1 := (hWa t).measurable
    have h2 := fun j => ((hVa j) t).measurable
    have : Measurable[𝓕 t] (quadProc κ ρ W V t) := by
      show Measurable[𝓕 t] fun ω =>
        W t ω ^ 2 + 1 / 2 * (∑ j, ρ j * V j t ω ^ 2) - (2 * (∑ j, ρ j) + κ) * (t : ℝ)
      fun_prop
    exact this.stronglyMeasurable
  have hNsa := stronglyAdapted_stoppedProcess_of_continuous hNa hNc hτ
  have hQsa := stronglyAdapted_stoppedProcess_of_continuous hQa hQc hτ
  have hNval : ∀ u ω, stoppedProcess (driftProc ρ W V) τ u ω
      = driftValue ρ (wpath W ω (θ u ω)) (fun j => V j (θ u ω) ω) := fun u ω => by
    rw [wpath_coe]; rfl
  have hQval : ∀ u ω, stoppedProcess (quadProc κ ρ W V) τ u ω
      = quadValue κ ρ (wpath W ω (θ u ω)) (fun j => V j (θ u ω) ω) (θ u ω) := fun u ω => by
    rw [wpath_coe]; rfl
  set Rρ : ℝ := ∑ j, |ρ j| with hRρ
  have hRρ0 : 0 ≤ Rρ := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hNb : ∀ u ω, |stoppedProcess (driftProc ρ W V) τ u ω| ≤ 2 * K + Rρ * K := fun u ω => by
    rw [hNval, wpath_coe]
    simp only [driftValue]
    have h1 : |∑ j, ρ j * V j (θ u ω) ω| ≤ Rρ * K := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hRρ, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((hbd' u ω).2 j) (abs_nonneg _)
    have h2 : |2 * W (θ u ω) ω| ≤ 2 * K := by
      rw [abs_mul, abs_two]; linarith [(hbd' u ω).1]
    exact (abs_add_le _ _).trans (by linarith)
  have hQb : ∀ u ω, |stoppedProcess (quadProc κ ρ W V) τ u ω|
      ≤ K ^ 2 + Rρ * K ^ 2 + |2 * (∑ j, ρ j) + κ| * T := fun u ω => by
    rw [hQval, wpath_coe]
    simp only [quadValue]
    have h1 : |∑ j, ρ j * V j (θ u ω) ω ^ 2| ≤ Rρ * K ^ 2 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hRρ, Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ((hbd' u ω).2 j) 2)
          (abs_nonneg _)
    have h2 : |W (θ u ω) ω ^ 2| ≤ K ^ 2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd' u ω).1 2
    have h3 : |(2 * (∑ j, ρ j) + κ) * (θ u ω : ℝ)| ≤ |2 * (∑ j, ρ j) + κ| * T := by
      rw [abs_mul, NNReal.abs_eq]
      exact mul_le_mul_of_nonneg_left (hθT u ω) (abs_nonneg _)
    have h4 : |1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2| ≤ Rρ * K ^ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have : 0 ≤ Rρ * K ^ 2 := by positivity
      linarith
    calc _ ≤ |W (θ u ω) ω ^ 2 + 1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2|
          + |(2 * (∑ j, ρ j) + κ) * (θ u ω : ℝ)| := abs_sub _ _
      _ ≤ _ := by linarith [abs_add_le (W (θ u ω) ω ^ 2) (1 / 2 * ∑ j, ρ j * V j (θ u ω) ω ^ 2)]
  have hNint : ∀ u, Integrable (stoppedProcess (driftProc ρ W V) τ u) P := fun u =>
    Integrable.of_bound ((hNsa u).mono (𝓕.le u)).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hNb u ω)
  have hQint : ∀ u, Integrable (stoppedProcess (quadProc κ ρ W V) τ u) P := fun u =>
    Integrable.of_bound ((hQsa u).mono (𝓕.le u)).aestronglyMeasurable _
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hQb u ω)
  set C := harmConst κ ρ K T with hCdef
  -- set integrals of an affine function of a process
  have haff : ∀ (X : ℝ≥0 → Ω → ℝ), (∀ u, Integrable (X u) P) → ∀ (a b : ℝ) (u : ℝ≥0) (A : Set Ω),
      ∫ ω in A, (a * X u ω + b) ∂P = a * ∫ ω in A, X u ω ∂P + b * (P A).toReal := by
    intro X hX a b u A
    rw [integral_add ((hX u).integrableOn.const_mul a) (integrable_const b),
      integral_const_mul, setIntegral_const, smul_eq_mul, mul_comm (P.real A)]
    rfl
  -- the first coefficient
  have hNmart : Martingale (stoppedProcess (driftProc ρ W V) τ) 𝓕 P := by
    refine martingale_of_forall_abs_sub_le hNsa hNint
      (G := fun k t ω => -(Real.sqrt κ * Y k)
        * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * Complex.I)) τ t ω
        + Real.sqrt κ * Y k * (c + phiI κ ρ))
      (fun k t => (((hI k).1 t).aestronglyMeasurable.const_mul _).add aestronglyMeasurable_const)
      (ε := fun k => Real.sqrt κ * C / Y k ^ 2) ?_ ?_ ?_
    · exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hYtop)
    · intro k t ω
      rw [hstop _ (hzI k).1 (hzI k).2, hNval]
      have hl := abs_laurent_one_le κ ρ (continuous_wpath hWc ω) (hw0 ω) (NNReal.coe_nonneg _)
        (hθT t ω) (hpb t ω) (hbd' t ω).2 (hYR k)
      have hid : -(Real.sqrt κ * Y k) * (c + harmPart κ ρ (wpath W ω) (θ t ω)
          (fun j => V j (θ t ω) ω) ((Y k : ℂ) * Complex.I)) + Real.sqrt κ * Y k * (c + phiI κ ρ)
          - driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
          = -(Real.sqrt κ * (Y k * (harmPart κ ρ (wpath W ω) (θ t ω) (fun j => V j (θ t ω) ω)
              ((Y k : ℂ) * Complex.I) - phiI κ ρ)
            + driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) / Real.sqrt κ)) := by
        field_simp; ring
      rw [hid, abs_neg, abs_mul, abs_of_pos hsk]
      calc _ ≤ Real.sqrt κ * (C / Y k ^ 2) := mul_le_mul_of_nonneg_left hl hsk.le
        _ = Real.sqrt κ * C / Y k ^ 2 := by ring
    · intro k s t hst A hA
      rw [haff _ (hI k).1, haff _ (hI k).1, (hI k).2 s t hst A hA]
  refine ⟨hNmart, ?_⟩
  -- the second coefficient
  refine martingale_of_forall_abs_sub_le hQsa hQint
    (G := fun k t ω => -(2 * Y k ^ 2 * Real.sqrt κ)
      * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ t ω
      + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
      - Y k * stoppedProcess (driftProc ρ W V) τ t ω)
    (fun k t => ((((hD k).1 t).aestronglyMeasurable.const_mul _).add
      aestronglyMeasurable_const).sub ((hNint t).aestronglyMeasurable.const_mul _))
    (ε := fun k => 2 * Real.sqrt κ * C / Y k) ?_ ?_ ?_
  · exact tendsto_const_nhds.div_atTop hYtop
  · intro k t ω
    rw [hstop _ (hzD k).1 (hzD k).2, hNval, hQval]
    have hl := abs_laurent_two_le hκ ρ (continuous_wpath hWc ω) (hw0 ω) (NNReal.coe_nonneg _)
      (hθT t ω) (hpb t ω) (hbd' t ω).2 (hYR k)
    have hid : -(2 * Y k ^ 2 * Real.sqrt κ) * (c + harmPart κ ρ (wpath W ω) (θ t ω)
        (fun j => V j (θ t ω) ω) ((Y k : ℂ) * (1 + Complex.I)))
        + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
        - Y k * driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
        - quadValue κ ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) (θ t ω)
        = -(2 * Y k ^ 2 * Real.sqrt κ * (harmPart κ ρ (wpath W ω) (θ t ω) (fun j => V j (θ t ω) ω)
            ((Y k : ℂ) * (1 + Complex.I)) - phiD κ ρ)
          + Y k * driftValue ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω)
          + quadValue κ ρ (wpath W ω (θ t ω)) (fun j => V j (θ t ω) ω) (θ t ω)) := by ring
    rw [hid, abs_neg]
    exact hl
  · intro k s t hst A hA
    have hX := (hD k).1
    have h1 : ∀ u, ∫ ω in A, (-(2 * Y k ^ 2 * Real.sqrt κ)
        * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω
        + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)
        - Y k * stoppedProcess (driftProc ρ W V) τ u ω) ∂P
        = (-(2 * Y k ^ 2 * Real.sqrt κ) * ∫ ω in A,
            stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω ∂P
          + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ) * (P A).toReal)
          - Y k * ∫ ω in A, stoppedProcess (driftProc ρ W V) τ u ω ∂P := fun u => by
      have hI1 : IntegrableOn (fun ω => -(2 * Y k ^ 2 * Real.sqrt κ)
          * stoppedProcess (coupProc κ ρL ρR W VL VR ((Y k : ℂ) * (1 + Complex.I))) τ u ω
          + 2 * Y k ^ 2 * Real.sqrt κ * (c + phiD κ ρ)) A P :=
        ((hX u).integrableOn.const_mul _).add (integrable_const _)
      have hI2 : IntegrableOn (fun ω => Y k * stoppedProcess (driftProc ρ W V) τ u ω) A P :=
        (hNint u).integrableOn.const_mul _
      rw [integral_sub hI1 hI2, integral_const_mul, haff _ hX]
    rw [h1, h1, (hD k).2 s t hst A hA, hNmart.setIntegral_eq hst hA]

end Extract

section Coup

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **A far point is not swallowed while the driver is bounded** (the landed argument of
`MartChar.setIntegral_stoppedProcess_coupProc_eq`): if `|W| ≤ K` on `[0, t]`, `t ≤ T`, and
`laurentRadius K T ≤ ‖z‖`, then `z` is not in the hull at `t` and `t` comes before its swallowing time. -/
theorem mem_diff_fwdHull_of_bound {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω) {ω : Ω}
    {z : ℂ} (hzH : z ∈ H) {K : ℝ} {T t : ℝ≥0} (htT : t ≤ T)
    (hb : ∀ r : ℝ≥0, r ≤ t → |W r ω| ≤ K) (hzR : laurentRadius K T ≤ ‖z‖) :
    z ∈ H \ QuantumZipper.fwdHull (wpath W ω) t ∧
      (t : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) := by
  have hpb : ∀ r ∈ Icc (0 : ℝ) t, |wpath W ω r| ≤ K := fun r hr =>
    hb r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2)
  have hR4 : K + 3 * Real.sqrt T + 1 ≤ ‖z‖ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  have hns : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) t := by
    refine mem_diff_fwdHull_of_norm (continuous_wpath hWc ω) (NNReal.coe_nonneg t) hpb hzH ?_
    have := Real.sqrt_le_sqrt (show (t : ℝ) ≤ T by exact_mod_cast htT)
    linarith
  refine ⟨hns, ?_⟩
  have hnot : ¬ QuantumZipper.swallowTime (wpath W ω) z ≤ ENNReal.ofReal t := fun h => hns.2 ⟨hzH, h⟩
  rw [not_le, ENNReal.ofReal_coe_nnreal] at hnot
  exact hnot

/-- **The explicit coupling mean is continuous in time before swallowing** (the landed right-continuity argument of
`MartChar.setIntegral_stoppedProcess_coupProc_eq`, two-sided). -/
theorem continuousAt_coupProc {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hVLc : ∀ i ω, Continuous fun t => VL i t ω)
    (hVRc : ∀ i ω, Continuous fun t => VR i t ω) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω) {z : ℂ} (hzH : z ∈ H) (ω : Ω) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) :
    ContinuousAt (coupProc κ ρL ρR W VL VR z · ω) s := by
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  set c : ℝ := Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i) with hc
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  obtain ⟨T', hsT', hT'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
  have hsT'' : s < T' := ENNReal.coe_lt_coe.1 hsT'
  have hzT' : z ∈ H \ QuantumZipper.fwdHull (wpath W ω) T' := by
    refine ⟨hzH, fun h => ?_⟩
    have h2 := h.2
    rw [ENNReal.ofReal_coe_nnreal] at h2
    exact absurd h2 (not_le.2 hT')
  set g : ℝ → ℝ := fun x => c + harmPart κ ρ (wpath W ω) x (fun j => V j x.toNNReal ω) z with hg_def
  have hg : ContinuousOn g (Icc 0 T') :=
    continuousOn_const.add (continuousOn_harmPart κ ρ (continuous_wpath hWc ω)
      (NNReal.coe_nonneg T') hzT' fun j => ((hVc j ω).comp continuous_real_toNNReal).continuousOn)
  have heq : ∀ t : ℝ≥0, t ≤ T' → coupProc κ ρL ρR W VL VR z t ω = g t := fun t ht => by
    rw [coupProc_eq hWc hordL hordR ht hzT', hg_def, jointV_apply_eq]
    simp only [Real.toNNReal_coe, hc, hρ, hV]
  have hgc : ContinuousOn (fun t : ℝ≥0 => g t) (Iic T') :=
    hg.comp NNReal.continuous_coe.continuousOn fun t ht =>
      ⟨NNReal.coe_nonneg t, by exact_mod_cast ht⟩
  have hca : ContinuousAt (fun t : ℝ≥0 => g t) s := hgc.continuousAt (Iic_mem_nhds hsT'')
  have heq' : (fun t : ℝ≥0 => g t) =ᶠ[𝓝 s] (coupProc κ ρL ρR W VL VR z · ω) := by
    filter_upwards [Iic_mem_nhds hsT''] with t ht
    exact (heq t ht).symm
  exact hca.congr heq'

/-- **The bound of the explicit coupling mean at a far point** (the landed bound of
`MartChar.setIntegral_stoppedProcess_coupProc_eq`). -/
theorem abs_coupProc_le {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω) {z : ℂ} (hzH : z ∈ H) {ω : Ω} {K : ℝ} {T t : ℝ≥0}
    (htT : t ≤ T) (hb : ∀ r : ℝ≥0, r ≤ t → |W r ω| ≤ K ∧ ∀ j, |jointV VL VR j r ω| ≤ K)
    (hzR : laurentRadius K T ≤ ‖z‖) :
    |coupProc κ ρL ρR W VL VR z t ω| ≤
      |Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i)| + harmBound κ (jointρ ρL ρR) K T := by
  have hns := (mem_diff_fwdHull_of_bound hWc hzH htT (fun r hr => (hb r hr).1) hzR).1
  have hpb : ∀ r ∈ Icc (0 : ℝ) t, |wpath W ω r| ≤ K := fun r hr =>
    (hb r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2)).1
  have hR1 : 1 ≤ ‖z‖ := (one_le_laurentRadius _ _).trans hzR
  have hR3 : 2 * dispConst K T + 1 ≤ ‖z‖ :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hzR))
  rw [coupProc_eq hWc hordL hordR le_rfl hns]
  refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [jointV_apply_eq]
  exact abs_harmPart_le κ _ (continuous_wpath hWc ω) (by simp [wpath, hW0])
    (NNReal.coe_nonneg t) (by exact_mod_cast htT) hpb _ hns hR1 (by linarith)

end Coup

section Piecewise

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- `c √t` with `c² = 4` is a force path of the zero driver: the mark of the empty word started at the driver. -/
theorem isForcePath_mul_sqrt {c : ℝ} (hc : c ^ 2 = 4) (hm : 0 ≤ c ∨ c ≤ 0) :
    IsForcePath (fun _ : ℝ≥0 => (0 : ℝ)) (fun t : ℝ≥0 => c * Real.sqrt t) := by
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc
  have hsm : Monotone fun t : ℝ≥0 => Real.sqrt t := fun a b hab =>
    Real.sqrt_le_sqrt (by exact_mod_cast hab)
  refine ⟨continuous_const.mul (Real.continuous_sqrt.comp NNReal.continuous_coe), ?_, ?_, ?_⟩
  · rcases hm with h | h
    · exact Or.inl fun a b hab => mul_le_mul_of_nonneg_left (hsm hab) h
    · exact Or.inr fun a b hab => mul_le_mul_of_nonpos_left (hsm hab) h
  · intro u hu _
    have heq : (fun s : ℝ => c * Real.sqrt (s.toNNReal : ℝ)) =ᶠ[𝓝 u] fun s => c * Real.sqrt s := by
      filter_upwards [Ioi_mem_nhds hu] with s hs
      rw [Real.coe_toNNReal _ (le_of_lt hs)]
    have hd := (Real.hasDerivAt_sqrt hu.ne').const_mul c
    have hsq : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
    have hval : c * (1 / (2 * Real.sqrt u)) = 2 / (c * Real.sqrt (u.toNNReal : ℝ) - 0) := by
      rw [Real.coe_toNNReal _ hu.le, sub_zero, eq_div_iff (mul_ne_zero hc0 hsq.ne')]
      field_simp
      linear_combination hc
    rw [← hval]
    exact hd.congr_of_eventuallyEq heq
  · refine measure_mono_null (t := {0}) ?_ (measure_singleton 0)
    rintro u ⟨hu0, hu⟩
    have h1 : Real.sqrt (u.toNNReal : ℝ) = 0 := by
      rcases mul_eq_zero.1 hu with h | h
      · exact absurd h hc0
      · exact h
    rw [Real.coe_toNNReal _ hu0, Real.sqrt_eq_zero hu0] at h1
    exact h1

open scoped Classical in
/-- The process `X` on the event `E` and `Y` off it. -/
def pwProc (E : Set Ω) (X Y : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t => E.piecewise (X t) (Y t)

theorem pwProc_of_mem {E : Set Ω} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ω ∈ E) (t : ℝ≥0) :
    pwProc E X Y t ω = X t ω := by
  classical
  simp only [pwProc]; convert Set.piecewise_eq_of_mem E (X t) (Y t) h

theorem pwProc_of_notMem {E : Set Ω} {X Y : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ω ∉ E) (t : ℝ≥0) :
    pwProc E X Y t ω = Y t ω := by
  classical
  simp only [pwProc]; convert Set.piecewise_eq_of_notMem E (X t) (Y t) h

theorem stronglyAdapted_pwProc {E : Set Ω} (hE : MeasurableSet[𝓕 0] E) {X Y : ℝ≥0 → Ω → ℝ}
    (hX : StronglyAdapted 𝓕 X) (hY : StronglyAdapted 𝓕 Y) : StronglyAdapted 𝓕 (pwProc E X Y) := by
  classical
  intro t
  exact (hX t).piecewise (𝓕.mono bot_le E hE) (hY t)

end Piecewise

section Lifetime

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- The `𝓕₀`-event on which the initial coordinates are below the level `n`. -/
def initEvent {ι : Type*} [Fintype ι] (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) (n : ℕ) : Set Ω :=
  {ω | absSum W V 0 ω < n}

open scoped Classical in
/-- **The localizing times before the lifetime `T`**: `min (locTime n n) T` on `initEvent n`, `0` off it. -/
def lifeLoc {ι : Type*} [Fintype ι] (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0)
    (n : ℕ) : Ω → WithTop ℝ≥0 :=
  (initEvent W V n).piecewise (fun ω => min (locTime W V n n ω) (T ω)) fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)

theorem lifeLoc_of_mem {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ}
    {T : Ω → WithTop ℝ≥0} {n : ℕ} {ω : Ω} (h : ω ∈ initEvent W V n) :
    lifeLoc W V T n ω = min (locTime W V n n ω) (T ω) := by
  classical
  simp only [lifeLoc]; convert Set.piecewise_eq_of_mem _ _ _ h

theorem lifeLoc_of_notMem {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ}
    {T : Ω → WithTop ℝ≥0} {n : ℕ} {ω : Ω} (h : ω ∉ initEvent W V n) :
    lifeLoc W V T n ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := by
  classical
  simp only [lifeLoc]; convert Set.piecewise_eq_of_notMem _ _ _ h

theorem lifeLoc_le_T {ι : Type*} [Fintype ι] (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) : lifeLoc W V T n ω ≤ T ω := by
  by_cases h : ω ∈ initEvent W V n
  · rw [lifeLoc_of_mem h]; exact min_le_right _ _
  · rw [lifeLoc_of_notMem h]; exact bot_le

theorem lifeLoc_le_n {ι : Type*} [Fintype ι] (W : ℝ≥0 → Ω → ℝ) (V : ι → ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) : lifeLoc W V T n ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := by
  by_cases h : ω ∈ initEvent W V n
  · rw [lifeLoc_of_mem h]; exact (min_le_left _ _).trans (locTime_le n n ω)
  · rw [lifeLoc_of_notMem h]; exact WithTop.coe_le_coe.2 bot_le

theorem measurableSet_initEvent {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ}
    (hWa : StronglyAdapted 𝓕 W) (hVa : ∀ j, StronglyAdapted 𝓕 (V j)) (n : ℕ) :
    MeasurableSet[𝓕 0] (initEvent W V n) := by
  have h1 : Measurable[𝓕 0] (W 0) := (hWa 0).measurable
  have h2 : ∀ j, Measurable[𝓕 0] (V j 0) := fun j => (hVa j 0).measurable
  have hm : Measurable[𝓕 0] (absSum W V 0) := by
    show Measurable[𝓕 0] fun ω => |W 0 ω| + ∑ j, |V j 0 ω|
    fun_prop
  exact measurableSet_lt hm measurable_const

theorem isStoppingTime_lifeLoc {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hVc : ∀ j ω, Continuous fun t => V j t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVa : ∀ j, StronglyAdapted 𝓕 (V j)) {T : Ω → WithTop ℝ≥0}
    (hT : IsStoppingTime 𝓕 T) (n : ℕ) : IsStoppingTime 𝓕 (lifeLoc W V T n) := by
  classical
  have h := IsStoppingTime.piecewise_of_le ((isStoppingTime_locTime hWc hVc hWa hVa n n).min hT)
    (isStoppingTime_const 𝓕 (0 : ℝ≥0)) (fun _ => (WithTop.coe_le_coe.2 bot_le).trans
      (show (((⊥ : ℝ≥0)) : WithTop ℝ≥0) ≤ _ from by rw [WithTop.coe_bot]; exact bot_le))
    (fun _ => le_rfl) (measurableSet_initEvent hWa hVa n)
  exact h

/-- **Up to `lifeLoc n` on `initEvent n`, the coordinates are bounded by `n`.** -/
theorem abs_le_of_le_lifeLoc {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ℝ} {V : ι → ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous fun t => W t ω) (hVc : ∀ j ω, Continuous fun t => V j t ω)
    {T : Ω → WithTop ℝ≥0} {n : ℕ} {ω : Ω} (hω : ω ∈ initEvent W V n) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) ≤ lifeLoc W V T n ω) : |W t ω| ≤ n ∧ ∀ j, |V j t ω| ≤ n := by
  have hZc := continuous_absSum hWc hVc
  have hpos : ⊥ < MathFin.exitTime (absSum W V) n ω := by
    rw [bot_lt_iff_ne_bot]
    intro h0
    have hle : MathFin.exitTime (absSum W V) n ω ≤ ((0 : ℝ≥0) : WithTop ℝ≥0) := by
      rw [h0]; exact bot_le
    obtain ⟨s, hs, hsN⟩ := (MathFin.exitTime_le_iff hZc n 0 ω).1 hle
    have hs0 : s = 0 := le_antisymm hs.2 bot_le
    subst hs0
    have h1 : absSum W V 0 ω < n := hω
    have h2 : 0 ≤ absSum W V 0 ω := by
      simp only [absSum]; positivity
    rw [abs_of_nonneg h2] at hsN
    linarith
  rw [lifeLoc_of_mem hω] at ht
  have hZ := MathFin.abs_le_of_le_exitTime hZc hpos ((ht.trans (min_le_left _ _)).trans (min_le_right _ _))
  have hZ' : absSum W V t ω ≤ n := (le_abs_self _).trans hZ
  have hle : ∀ j, |V j t ω| ≤ absSum W V t ω := fun j => by
    have := Finset.single_le_sum (f := fun j => |V j t ω|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    simp only [absSum]
    linarith [abs_nonneg (W t ω)]
  have hleW : |W t ω| ≤ absSum W V t ω := by
    simp only [absSum]
    linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (V j t ω)]
  exact ⟨hleW.trans hZ', fun j => (hle j).trans hZ'⟩

/-- **The driver's martingale part and its square compensator are martingales up to `lifeLoc n`**, when every
explicit coupling mean is a local martingale before swallowing **and before the lifetime `T`**. The initial word is
random (any adapted coordinates). Proof: the processes are replaced off `initEvent n` by the empty word
`(0, ∓2√t)` (`pwProc`), stopped at `0` there; the coupling means of the replaced processes stopped at `lifeLoc n`
have constant set integrals (`setIntegral_indicator_stoppedProcess_eq`), so the Laurent extraction
(`martingale_driftProc_quadProc_of_setIntegral`) and the landed cell identities apply. -/
theorem martingale_martProc_lifeLoc [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hWa : StronglyAdapted 𝓕 W) (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i))
    (hVRa : ∀ i, StronglyAdapted 𝓕 (VR i)) (hordL : ∀ ω t i, VL i t ω ≤ W t ω)
    (hordR : ∀ ω t i, W t ω ≤ VR i t ω)
    (hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpathR : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VR i t ω))
    {T : Ω → WithTop ℝ≥0} (hT : IsStoppingTime 𝓕 T)
    (hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓕 P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (T ω))
      (coupProc κ ρL ρR W VL VR z)) (n : ℕ) :
    Martingale (stoppedProcess (martProc (jointρ ρL ρR) W (jointV VL VR))
        (lifeLoc W (jointV VL VR) T n)) 𝓕 P ∧
      Martingale (stoppedProcess (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω ^ 2 - κ * t)
        (lifeLoc W (jointV VL VR) T n)) 𝓕 P := by
  classical
  set V := jointV VL VR with hV
  set ρ := jointρ ρL ρR with hρ
  set E := initEvent W V n with hEdef
  set τ := lifeLoc W V T n with hτdef
  set τ' : Ω → WithTop ℝ≥0 := fun ω => min (locTime W V n n ω) (T ω) with hτ'def
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ i ω, Continuous fun t => VR i t ω := fun i ω => (hpathR ω i).1
  have hVc : ∀ j ω, Continuous fun t => V j t ω := fun j ω => by
    cases j with
    | inl i => exact hVLc i ω
    | inr i => exact hVRc i ω
  have hVa : ∀ j, StronglyAdapted 𝓕 (V j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hE : MeasurableSet[𝓕 0] E := measurableSet_initEvent hWa hVa n
  have hτ : IsStoppingTime 𝓕 τ := isStoppingTime_lifeLoc hWc hVc hWa hVa hT n
  have hτ' : IsStoppingTime 𝓕 τ' := (isStoppingTime_locTime hWc hVc hWa hVa n n).min hT
  have hτn : ∀ ω, τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := lifeLoc_le_n W V T n
  have hττ' : ∀ ω ∈ E, τ ω = τ' ω := fun ω hω => lifeLoc_of_mem hω
  have hτ0 : ∀ ω, ω ∉ E → τ ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := fun ω hω => lifeLoc_of_notMem hω
  -- the replaced processes
  set W' : ℝ≥0 → Ω → ℝ := pwProc E W fun _ _ => 0 with hW'
  set VL' : Fin nL → ℝ≥0 → Ω → ℝ := fun i => pwProc E (VL i) fun t _ => -2 * Real.sqrt t with hVL'
  set VR' : Fin nR → ℝ≥0 → Ω → ℝ := fun i => pwProc E (VR i) fun t _ => 2 * Real.sqrt t with hVR'
  set V' := jointV VL' VR' with hV'
  have hsqc : Continuous fun t : ℝ≥0 => Real.sqrt t := Real.continuous_sqrt.comp NNReal.continuous_coe
  have hW'c : ∀ ω, Continuous fun t => W' t ω := fun ω => by
    by_cases h : ω ∈ E
    · simp only [hW', pwProc_of_mem h]; exact hWc ω
    · simp only [hW', pwProc_of_notMem h]; exact continuous_const
  have hVL'c : ∀ i ω, Continuous fun t => VL' i t ω := fun i ω => by
    by_cases h : ω ∈ E
    · simp only [hVL', pwProc_of_mem h]; exact hVLc i ω
    · simp only [hVL', pwProc_of_notMem h]; exact continuous_const.mul hsqc
  have hVR'c : ∀ i ω, Continuous fun t => VR' i t ω := fun i ω => by
    by_cases h : ω ∈ E
    · simp only [hVR', pwProc_of_mem h]; exact hVRc i ω
    · simp only [hVR', pwProc_of_notMem h]; exact continuous_const.mul hsqc
  have hsqa : ∀ c : ℝ, StronglyAdapted 𝓕 (fun (t : ℝ≥0) (_ : Ω) => c * Real.sqrt t) := fun c t =>
    stronglyMeasurable_const
  have hW'a : StronglyAdapted 𝓕 W' := stronglyAdapted_pwProc hE hWa fun t => stronglyMeasurable_const
  have hVL'a : ∀ i, StronglyAdapted 𝓕 (VL' i) := fun i => stronglyAdapted_pwProc hE (hVLa i) (hsqa _)
  have hVR'a : ∀ i, StronglyAdapted 𝓕 (VR' i) := fun i => stronglyAdapted_pwProc hE (hVRa i) (hsqa _)
  have hsq0 : ∀ t : ℝ≥0, 0 ≤ Real.sqrt t := fun t => Real.sqrt_nonneg _
  have hordL' : ∀ ω t i, VL' i t ω ≤ W' t ω := fun ω t i => by
    by_cases h : ω ∈ E
    · simp only [hVL', hW', pwProc_of_mem h]; exact hordL ω t i
    · simp only [hVL', hW', pwProc_of_notMem h]; nlinarith [hsq0 t]
  have hordR' : ∀ ω t i, W' t ω ≤ VR' i t ω := fun ω t i => by
    by_cases h : ω ∈ E
    · simp only [hVR', hW', pwProc_of_mem h]; exact hordR ω t i
    · simp only [hVR', hW', pwProc_of_notMem h]; nlinarith [hsq0 t]
  have hpath' : ∀ ω j, IsForcePath (fun t => W' t ω) (fun t => V' j t ω) := fun ω j => by
    by_cases h : ω ∈ E
    · cases j with
      | inl i => simpa only [hV', hVL', hW', jointV, Sum.elim_inl, pwProc_of_mem h] using hpathL ω i
      | inr i => simpa only [hV', hVR', hW', jointV, Sum.elim_inr, pwProc_of_mem h] using hpathR ω i
    · cases j with
      | inl i =>
        simpa only [hV', hVL', hW', jointV, Sum.elim_inl, pwProc_of_notMem h] using
          isForcePath_mul_sqrt (c := -2) (by norm_num) (Or.inr (by norm_num))
      | inr i =>
        simpa only [hV', hVR', hW', jointV, Sum.elim_inr, pwProc_of_notMem h] using
          isForcePath_mul_sqrt (c := 2) (by norm_num) (Or.inl (by norm_num))
  -- the bounds
  have hbd' : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) ≤ τ ω → |W' t ω| ≤ n ∧ ∀ j, |V' j t ω| ≤ n := by
    intro ω t ht
    by_cases h : ω ∈ E
    · have hb := abs_le_of_le_lifeLoc hWc hVc h ht
      refine ⟨by simpa only [hW', pwProc_of_mem h] using hb.1, fun j => ?_⟩
      cases j with
      | inl i =>
        simp only [hV', hVL', jointV, Sum.elim_inl, pwProc_of_mem h]; exact hb.2 (Sum.inl i)
      | inr i =>
        simp only [hV', hVR', jointV, Sum.elim_inr, pwProc_of_mem h]; exact hb.2 (Sum.inr i)
    · rw [hτ0 ω h] at ht
      have ht0 : t = 0 := le_antisymm (WithTop.coe_le_coe.1 ht) bot_le
      subst ht0
      refine ⟨by simp [hW', pwProc_of_notMem h], fun j => ?_⟩
      cases j with
      | inl i => simp [hV', hVL', jointV, pwProc_of_notMem h]
      | inr i => simp [hV', hVR', jointV, pwProc_of_notMem h]
  have hW'0 : ∀ ω, W' 0 ω = 0 := fun ω => by
    by_cases h : ω ∈ E
    · simp only [hW', pwProc_of_mem h]; exact hW0 ω
    · simp only [hW', pwProc_of_notMem h]
  have hV'a : ∀ j, StronglyAdapted 𝓕 (V' j) := fun j => by
    cases j with
    | inl i => exact hVL'a i
    | inr i => exact hVR'a i
  -- the original coordinates up to `τ'` on `E`
  have hbE : ∀ ω ∈ E, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ τ' ω →
      (|W u ω| ≤ n ∧ ∀ j, |V j u ω| ≤ n) ∧ u ≤ (n : ℝ≥0) := fun ω h u hu => by
    have hu' : (u : WithTop ℝ≥0) ≤ τ ω := by rw [hττ' ω h]; exact hu
    exact ⟨abs_le_of_le_lifeLoc hWc hVc h hu', WithTop.coe_le_coe.1 (hu'.trans (hτn ω))⟩
  -- the set integrals of the replaced coupling means
  have hset : ∀ z ∈ H, laurentRadius (n : ℝ) ((n : ℝ≥0) : ℝ) ≤ ‖z‖ →
      (∀ t, Integrable (stoppedProcess (coupProc κ ρL ρR W' VL' VR' z) τ t) P) ∧
        ∀ s t : ℝ≥0, s ≤ t → ∀ A, MeasurableSet[𝓕 s] A →
          ∫ ω in A, stoppedProcess (coupProc κ ρL ρR W' VL' VR' z) τ t ω ∂P
            = ∫ ω in A, stoppedProcess (coupProc κ ρL ρR W' VL' VR' z) τ s ω ∂P := by
    intro z hz hzR
    set X := coupProc κ ρL ρR W VL VR z with hX
    set c₀ : ℝ := couplingMean κ (fun _ => 0) 0
      (meanExt κ ρL ρR 0 (fun _ => -2 * Real.sqrt ((0 : ℝ≥0) : ℝ))
        (fun _ => 2 * Real.sqrt ((0 : ℝ≥0) : ℝ))) z with hc₀
    have hval : ∀ t ω, stoppedProcess (coupProc κ ρL ρR W' VL' VR' z) τ t ω =
        E.indicator (stoppedProcess X τ' t) ω + Eᶜ.indicator (fun _ => c₀) ω := by
      intro t ω
      by_cases h : ω ∈ E
      · have hc : ω ∉ Eᶜ := fun h' => h' h
        rw [Set.indicator_of_mem h, Set.indicator_of_notMem hc, add_zero]
        have hwp : wpath (pwProc E W fun _ _ => 0) ω = wpath W ω := funext fun s => by
          simp only [wpath, pwProc_of_mem h]
        simp only [stoppedProcess, hττ' ω h, hX, coupProc, hwp, hW', hVL', hVR', pwProc_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (show ω ∈ Eᶜ from h), zero_add]
        have hwp : wpath (pwProc E W fun _ _ => 0) ω = fun _ => 0 := funext fun s => by
          simp only [wpath, pwProc_of_notMem h]
        have h0 : (min ((t : ℝ≥0) : WithTop ℝ≥0) (((0 : ℝ≥0) : WithTop ℝ≥0))).untopA = 0 := by
          rw [← WithTop.coe_min]; simp
        simp only [stoppedProcess, hτ0 ω h, h0, coupProc, hwp, hW', hVL', hVR', pwProc_of_notMem h, hc₀,
          NNReal.coe_zero]
    have hfar : ∀ ω ∈ E, ∀ u : ℝ≥0, (u : WithTop ℝ≥0) ≤ τ' ω →
        (u : WithTop ℝ≥0) < (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) := by
      intro ω h u hu
      exact (mem_diff_fwdHull_of_bound hWc hz (hbE ω h u hu).2
        (fun r hr => (hbE ω h r ((WithTop.coe_le_coe.2 hr).trans hu)).1.1) hzR).2
    have hP1 := setIntegral_indicator_stoppedProcess_eq (hmart z hz)
      (fun ω s hs => (continuousAt_coupProc hWc hVLc hVRc hordL hordR hz ω
        (lt_of_lt_of_le hs (min_le_left _ _))).continuousWithinAt) hτ' hE
      (fun ω h => by
        refine le_min ?_ (min_le_right _ _)
        have hne : τ' ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top
          ((min_le_left _ _).trans (locTime_le n n ω))
        rw [← coe_untopA_of_ne_top hne]
        exact (hfar ω h _ (coe_untopA_of_ne_top hne).le).le)
      (fun ω h u hu => (continuousAt_coupProc hWc hVLc hVRc hordL hordR hz ω
        (hfar ω h u hu)).continuousWithinAt)
      (C := |Real.pi / Real.sqrt κ * (1 + ∑ i, ρR i)| + harmBound κ (jointρ ρL ρR) n (n : ℝ≥0))
      (fun ω h t ht => abs_coupProc_le hW0 hWc hordL hordR hz (hbE ω h t ht).2
        (fun r hr => (hbE ω h r ((WithTop.coe_le_coe.2 hr).trans ht)).1) hzR)
    have hIc : Integrable (fun ω => Eᶜ.indicator (fun _ => c₀) ω) P :=
      (integrable_const c₀).indicator (MeasurableSet.compl (𝓕.le 0 E hE))
    refine ⟨fun t => ?_, fun s t hst A hA => ?_⟩
    · have e : stoppedProcess (coupProc κ ρL ρR W' VL' VR' z) τ t =
          fun ω => E.indicator (stoppedProcess X τ' t) ω + Eᶜ.indicator (fun _ => c₀) ω := funext (hval t)
      rw [e]; exact (hP1.1 t).add hIc
    · simp_rw [hval]
      rw [integral_add (hP1.1 t).integrableOn hIc.integrableOn,
        integral_add (hP1.1 s).integrableOn hIc.integrableOn, hP1.2 s t hst A hA]
  have hNQ := martingale_driftProc_quadProc_of_setIntegral hκ hW'0 hW'c hVL'c hVR'c hW'a hVL'a hVR'a
    hordL' hordR' hτ hτn hbd' hset
  have hM' := martingale_stoppedProcess_martProc (ρ := ρ) (W := W') (V := V') hτn hNQ.1
  have hM2' := martingale_stoppedProcess_martProc_sq_sub (κ := κ) (ρ := ρ) hτ hτn hbd' hW'c hW'a hV'a
    hpath' hNQ.1 hNQ.2
  have hWeq : ∀ ω ∈ E, ∀ u, W' u ω = W u ω := fun ω h u => by simp only [hW', pwProc_of_mem h]
  have hVeq : ∀ ω ∈ E, ∀ j u, V' j u ω = V j u ω := fun ω h j u => by
    cases j with
    | inl i => simp only [hV', hV, jointV, Sum.elim_inl, hVL', pwProc_of_mem h]
    | inr i => simp only [hV', hV, jointV, Sum.elim_inr, hVR', pwProc_of_mem h]
  have hmeq : ∀ t ω, stoppedProcess (martProc ρ W V) τ t ω = stoppedProcess (martProc ρ W' V') τ t ω := by
    intro t ω
    by_cases h : ω ∈ E
    · simp only [stoppedProcess, martProc, hWeq ω h, hVeq ω h]
    · have h0 : (min ((t : ℝ≥0) : WithTop ℝ≥0) (τ ω)).untopA = 0 := by
        rw [hτ0 ω h, ← WithTop.coe_min]; simp
      simp only [stoppedProcess, martProc, martValue, h0, sub_self, mul_zero, Finset.sum_const_zero,
        zero_add]
  have he1 : stoppedProcess (martProc ρ W V) τ = stoppedProcess (martProc ρ W' V') τ :=
    funext fun t => funext fun ω => hmeq t ω
  have he2 : stoppedProcess (fun t ω => martProc ρ W V t ω ^ 2 - κ * t) τ =
      stoppedProcess (fun t ω => martProc ρ W' V' t ω ^ 2 - κ * t) τ := by
    funext t ω
    have := hmeq t ω
    simp only [stoppedProcess] at this ⊢
    rw [this]
  rw [he1, he2]
  exact ⟨hM', hM2'⟩

end Lifetime

end PhaseSelFull

end Sec7

end InteractingSLE
