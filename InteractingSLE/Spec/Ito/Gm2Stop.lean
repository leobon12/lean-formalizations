import InteractingSLE.Spec.Ito.Gm2Bracket
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import BrownianMotion.Auxiliary.Martingale

/-!
# Stopping the data of the mixed Itô formula

Packet PROVE-ITO-GEN2. Tools to reduce the local (lifetime) form of the mixed Itô formula to its
bounded core:

* `stopStieltjes U r`: the integrator `s ↦ U(min s r)`, with
  `∫_{(0,t]} g d(U stopped at r) = ∫_{(0, t ∧ r]} g dU` (`integral_stopStieltjes`);
* `measurable_stoppedProcess_of_rightContinuousBefore`: an adapted process that is right-continuous up
  to a stopping time `ρ` (on `{ρ > 0}`) is adapted after stopping at `ρ` — no progressive measurability
  of the unstopped process is needed, so processes that are regular only before a lifetime can be
  stopped strictly before it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace InteractingSLE.Ito.Gm2

/-! ### Stopped integrators -/

/-- The Stieltjes function `s ↦ U(min s r)`. -/
def stopStieltjes (U : StieltjesFunction ℝ≥0) (r : ℝ≥0) : StieltjesFunction ℝ≥0 where
  toFun s := U (min s r)
  mono' _ _ h := U.mono (min_le_min_right r h)
  right_continuous' x := by
    have hf : ContinuousWithinAt (fun s : ℝ≥0 => min s r) (Ici x) x :=
      (continuous_id.min continuous_const).continuousWithinAt
    exact ContinuousWithinAt.comp (f := fun s : ℝ≥0 => min s r) (x := x) (U.right_continuous (min x r))
      hf fun _ hs => min_le_min_right r hs

@[simp] lemma stopStieltjes_apply (U : StieltjesFunction ℝ≥0) (r s : ℝ≥0) :
    stopStieltjes U r s = U (min s r) := rfl

lemma continuous_stopStieltjes {U : StieltjesFunction ℝ≥0} (hU : Continuous U) (r : ℝ≥0) :
    Continuous (stopStieltjes U r) :=
  hU.comp (continuous_id.min continuous_const)

lemma stieltjes_measure_Ioc_ne_top (U : StieltjesFunction ℝ≥0) (a b : ℝ≥0) :
    U.measure (Ioc a b) ≠ ∞ := by
  rw [StieltjesFunction.measure_Ioc]; exact ENNReal.ofReal_ne_top

/-- **The measure of a stopped integrator on `(0, t]`** is that of the integrator on `(0, t ∧ r]`. -/
theorem restrict_stopStieltjes_measure (U : StieltjesFunction ℝ≥0) (r t : ℝ≥0) :
    (stopStieltjes U r).measure.restrict (Ioc 0 t) = U.measure.restrict (Ioc 0 (min t r)) := by
  have : IsFiniteMeasure ((stopStieltjes U r).measure.restrict (Ioc 0 t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (stieltjes_measure_Ioc_ne_top _ _ _).lt_top⟩
  have key : ∀ α β : ℝ≥0, ENNReal.ofReal (U (min β r) - U (min α r)) =
      ENNReal.ofReal (U (min β r) - U α) := by
    intro α β
    rcases le_total α r with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, ENNReal.ofReal_of_nonpos (sub_nonpos.2 (U.mono (min_le_right _ _))),
        ENNReal.ofReal_of_nonpos (sub_nonpos.2 (U.mono ((min_le_right _ _).trans h)))]
  refine Measure.ext_of_Ioc_finite _ _ ?_ fun a b _ => ?_
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc,
      StieltjesFunction.measure_Ioc, stopStieltjes_apply, stopStieltjes_apply]
    rw [show min (0 : ℝ≥0) r = 0 from min_eq_left bot_le]
  · rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
      Ioc_inter_Ioc, Ioc_inter_Ioc, StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
      stopStieltjes_apply, stopStieltjes_apply, ← min_assoc, key]

/-- **Integrals against a stopped integrator.** -/
theorem integral_stopStieltjes {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : StieltjesFunction ℝ≥0) (r t : ℝ≥0) (g : ℝ≥0 → G) :
    ∫ u in Ioc 0 t, g u ∂(stopStieltjes U r).measure = ∫ u in Ioc 0 (min t r), g u ∂U.measure := by
  rw [restrict_stopStieltjes_measure]

/-- On `(0, t ∧ r]` a density read at `u ∧ r` is the density itself. -/
theorem integral_stopStieltjes_comp_min {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (U : StieltjesFunction ℝ≥0) (r t : ℝ≥0) (g : ℝ≥0 → G) :
    ∫ u in Ioc 0 t, g (min u r) ∂(stopStieltjes U r).measure =
      ∫ u in Ioc 0 (min t r), g u ∂U.measure := by
  rw [integral_stopStieltjes]
  exact setIntegral_congr_fun measurableSet_Ioc fun u hu => by
    rw [min_eq_left (hu.2.trans (min_le_right _ _))]

/-! ### Stopping keeps adaptedness -/

section Approx

variable {Ω : Type*} {G : Type*} [MeasurableSpace G]

/-- The capped dyadic approximations of a process read at a measurable random time `r ≤ t` are
measurable, for a σ-algebra `m` for which the process is measurable at all times `≤ t`. -/
lemma measurable_cappedDyadic_approx {m : MeasurableSpace Ω} {Z : ℝ≥0 → Ω → G} {t : ℝ≥0}
    (hZ : ∀ s ≤ t, Measurable[m] (Z s)) {r : Ω → ℝ≥0} (hr : Measurable[m] r) {S : Set Ω}
    (hS : MeasurableSet[m] S) [DecidablePred (· ∈ S)] (n : ℕ) :
    Measurable[m] fun ω => if ω ∈ S then Z (cappedDyadicUp n t (r ω)) ω else Z 0 ω := by
  have hfl : Measurable[m] fun ω => ⌊(2 : ℝ≥0) ^ n * r ω⌋₊ :=
    Nat.floor_mono.measurable.comp (measurable_const.mul hr)
  have h1 : Measurable[m] fun ω => Z (cappedDyadicUp n t (r ω)) ω := by
    intro B hB
    have heq : (fun ω => Z (cappedDyadicUp n t (r ω)) ω) ⁻¹' B =
        ⋃ k : ℕ, {ω | ⌊(2 : ℝ≥0) ^ n * r ω⌋₊ = k} ∩
          (Z (min (((k + 1 : ℕ) : ℝ≥0) / 2 ^ n) t)) ⁻¹' B := by
      ext ω
      simp only [mem_preimage, mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro h; exact ⟨_, rfl, h⟩
      · rintro ⟨k, hk, h⟩; rw [← hk] at h; exact h
    rw [heq]
    exact MeasurableSet.iUnion fun k => (hfl (measurableSet_singleton k)).inter
      ((hZ _ (min_le_right _ _)) hB)
  exact Measurable.ite hS h1 (hZ 0 bot_le)

end Approx


section Adapted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

lemma untopA_min_coe_le (t : ℝ≥0) (x : WithTop ℝ≥0) :
    (((min (t : WithTop ℝ≥0) x).untopA : ℝ≥0) : WithTop ℝ≥0) = min (t : WithTop ℝ≥0) x := by
  have hne : min (t : WithTop ℝ≥0) x ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]

/-- **Stopping a process that is right-continuous up to the stopping time keeps it adapted.** The
unstopped process need only be adapted, and right-continuous at the times `s ≤ ρ` on `{ρ > 0}`. -/
theorem measurable_stoppedProcess_of_rightContinuousBefore {G : Type*} [TopologicalSpace G]
    [TopologicalSpace.PseudoMetrizableSpace G] [MeasurableSpace G] [BorelSpace G] {Z : ℝ≥0 → Ω → G}
    (hZ : ∀ t, Measurable[𝓕 t] (Z t)) {ρ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime 𝓕 ρ)
    (hrc : ∀ ω, 0 < ρ ω → ∀ s : ℝ≥0, (s : WithTop ℝ≥0) ≤ ρ ω →
      ContinuousWithinAt (Z · ω) (Ici s) s) (t : ℝ≥0) :
    Measurable[𝓕 t] (stoppedProcess Z ρ t) := by
  set r : Ω → ℝ≥0 := fun ω => (min (t : WithTop ℝ≥0) (ρ ω)).untopA with hr
  have hrm : Measurable[𝓕 t] r :=
    ((isStronglyProgressive_min_stopping_time hρ).stronglyAdapted t).measurable
  have hrt (ω : Ω) : r ω ≤ t := by
    have := untopA_min_coe_le t (ρ ω)
    exact WithTop.coe_le_coe.1 (this ▸ min_le_left _ _)
  have hrρ (ω : Ω) : (r ω : WithTop ℝ≥0) ≤ ρ ω := (untopA_min_coe_le t (ρ ω)).symm ▸ min_le_right _ _
  have hpos : MeasurableSet[𝓕 t] {ω | 0 < ρ ω} := 𝓕.mono bot_le _ (hρ.measurableSet_gt 0)
  -- the dyadic approximations from the right, capped at `t`
  set V : ℕ → Ω → G := fun n ω =>
    if ω ∈ {ω | 0 < ρ ω} then Z (cappedDyadicUp n t (r ω)) ω else Z 0 ω with hV
  have hVm (n : ℕ) : Measurable[𝓕 t] (V n) :=
    measurable_cappedDyadic_approx (m := 𝓕 t) (fun s hs => (hZ s).mono (𝓕.mono hs) le_rfl) hrm
      hpos n
  have hVlim (ω : Ω) : Tendsto (fun n => V n ω) atTop (𝓝 (stoppedProcess Z ρ t ω)) := by
    by_cases h0 : 0 < ρ ω
    · have hVn : (fun n => V n ω) = fun n => Z (cappedDyadicUp n t (r ω)) ω :=
        funext fun n => ite_eq_left_iff.2 fun h => absurd h0 h
      rw [hVn]
      have h1 : Tendsto (fun n => cappedDyadicUp n t (r ω)) atTop (𝓝[Ici (r ω)] (r ω)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
          le_min (lt_dyadicUp n (r ω)).le (hrt ω)⟩
        have h := (tendsto_nhdsWithin_iff.1 (tendsto_dyadicUp (r ω))).1.min
          (tendsto_const_nhds (x := t))
        rwa [min_eq_left (hrt ω)] at h
      exact (hrc ω h0 (r ω) (hrρ ω)).tendsto.comp h1
    · have hρ0 : ρ ω = 0 := le_antisymm (not_lt.1 h0) bot_le
      have hz : (min (t : WithTop ℝ≥0) 0).untopA = 0 := by
        rw [min_eq_right (show (0 : WithTop ℝ≥0) ≤ t from bot_le),
          WithTop.untopA_eq_untop WithTop.zero_ne_top, WithTop.untop_zero]
      have hsp : stoppedProcess Z ρ t ω = Z 0 ω := by
        show Z (min (t : WithTop ℝ≥0) (ρ ω)).untopA ω = Z 0 ω
        rw [hρ0, hz]
      have hVn : (fun n => V n ω) = fun _ => Z 0 ω :=
        funext fun n => ite_eq_right_iff.2 fun h => absurd h h0
      rw [hVn, hsp]
      exact tendsto_const_nhds
  exact @measurable_of_tendsto_metrizable Ω G (𝓕 t) _ _ _ _ V _ hVm (tendsto_pi_nhds.2 hVlim)

end Adapted

/-! ### Stopping strictly before a lifetime -/

section Before

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}

lemma stoppedProcess_of_eq_coe {G : Type*} (Z : ℝ≥0 → Ω → G) {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    {r : ℝ≥0} (h : τ ω = r) (t : ℝ≥0) : stoppedProcess Z τ t ω = Z (min t r) ω := by
  simp only [stoppedProcess, h, ← WithTop.coe_min]
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]

lemma stoppedProcess_of_eq_zero {G : Type*} (Z : ℝ≥0 → Ω → G) {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (h : τ ω = 0) (t : ℝ≥0) : stoppedProcess Z τ t ω = Z 0 ω := by
  rw [stoppedProcess_of_eq_coe Z (r := 0) (by rw [h]; rfl),
    min_eq_right (show (0 : ℝ≥0) ≤ t from bot_le)]

lemma exists_eq_coe_of_lt {τ ζ : WithTop ℝ≥0} (h : τ < ζ) : ∃ r : ℝ≥0, τ = r :=
  WithTop.ne_top_iff_exists.1 (ne_top_of_lt h) |>.imp fun _ h => h.symm

/-- **A path that is continuous before its lifetime, stopped at a time that is `0` or strictly below
the lifetime, is continuous.** -/
theorem continuous_stoppedProcess_of_continuousOn {G : Type*} [TopologicalSpace G]
    {Z : ℝ≥0 → Ω → G} {ζ τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hZ : ContinuousOn (Z · ω) {t | (t : WithTop ℝ≥0) < ζ ω}) (hτ : τ ω = 0 ∨ τ ω < ζ ω) :
    Continuous fun t => stoppedProcess Z τ t ω := by
  rcases hτ with h0 | hlt
  · simp only [stoppedProcess_of_eq_zero Z h0]; exact continuous_const
  · obtain ⟨r, hr⟩ := exists_eq_coe_of_lt hlt
    simp only [stoppedProcess_of_eq_coe Z hr]
    refine hZ.comp_continuous (continuous_id.min continuous_const) fun t => ?_
    show ((min t r : ℝ≥0) : WithTop ℝ≥0) < ζ ω
    exact lt_of_le_of_lt (WithTop.coe_le_coe.2 (min_le_right t r)) (hr ▸ hlt)

/-- The indicator version of `continuous_stoppedProcess_of_continuousOn`. -/
theorem continuous_stoppedProcess_indicator_of_continuousOn {G : Type*} [TopologicalSpace G]
    [Zero G] {Z : ℝ≥0 → Ω → G} {ζ τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hZ : ContinuousOn (Z · ω) {t | (t : WithTop ℝ≥0) < ζ ω}) (hτ : τ ω = 0 ∨ τ ω < ζ ω)
    (S : Set Ω) : Continuous fun t => stoppedProcess (fun t => S.indicator (Z t)) τ t ω := by
  simp only [stoppedProcess_indicator_comm]
  by_cases hω : ω ∈ S
  · simp only [Set.indicator_of_mem hω]
    exact continuous_stoppedProcess_of_continuousOn hZ hτ
  · simp only [Set.indicator_of_notMem hω]; exact continuous_const

/-- **Re-localizing a localized martingale.** If `X` stopped at `σ` (zeroed on `{σ = 0}`) is a
martingale with continuous paths, then so is `X` stopped at any stopping time `τ ≤ σ`. -/
theorem martingale_stoppedProcess_indicator_of_le {P : Measure Ω} [IsFiniteMeasure P]
    {X : ℝ≥0 → Ω → ℝ} {σ τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) (hτσ : ∀ ω, τ ω ≤ σ ω)
    (hZ : Martingale (stoppedProcess (fun t => {ω | 0 < σ ω}.indicator (X t)) σ) 𝓕 P)
    (hZc : ∀ ω, Continuous fun t => stoppedProcess (fun t => {ω | 0 < σ ω}.indicator (X t)) σ t ω) :
    Martingale (stoppedProcess (fun t => {ω | 0 < τ ω}.indicator (X t)) τ) 𝓕 P := by
  have h1 := InteractingSLE.Martingale.stoppedProcess_of_rightContinuous hZ
    (fun ω t => (hZc ω).continuousWithinAt) hτ
  rw [stoppedProcess_stoppedProcess_of_le_right hτσ] at h1
  have hS : MeasurableSet[𝓕 ⊥] {ω | 0 < τ ω} := hτ.measurableSet_gt 0
  have h2 := h1.indicator hS
  convert h2 using 1
  funext t ω
  simp only [stoppedProcess_indicator_comm]
  by_cases hω : 0 < τ ω
  · have hσ : 0 < σ ω := hω.trans_le (hτσ ω)
    simp only [Set.indicator_of_mem (show ω ∈ {ω | 0 < τ ω} from hω),
      Set.indicator_of_mem (show ω ∈ {ω | 0 < σ ω} from hσ)]
  · simp only [Set.indicator_of_notMem (show ω ∉ {ω | 0 < τ ω} from hω)]

end Before

end InteractingSLE.Ito.Gm2
