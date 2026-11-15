/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.PushforwardMeas
import InteractingSLE.GFF.PushforwardLaw
import InteractingSLE.Spec.Ito.Measurability
import InteractingSLE.Spec.Ito.Loewner

/-!
# The field transported by the Loewner map of a random driver

Packet PROVE-PUSHFWD. For a driving process `W` with continuous paths, `W 0 = 0`, adapted to `(𝓖ₜ)`, the Loewner
chart at time `s`, `c_ω = (f_s, f_s⁻¹, arg f_s′)` of the path `t ↦ W t ω` (`loewnerChartAt W s ω`, built from the
frozen `Chart.loewner` and `Chart.id`), satisfies the pointwise hypotheses of `Chart.measurable_chartTransport_random'`
and of the random-chart law theorems of `GFF/PushforwardLaw.lean`, with the σ-algebra `𝓖 s`:

* `mem_dom_loewner_iff`: the chart domain is `ℍ \ K_s = {z ∈ ℍ | a forward solution from z exists on [0, s]}`;
* `measurableSet_mem_dom_loewnerChartAt`, `measurable_indicator_fwd_loewnerChartAt`,
  `measurable_indicator_lift_loewnerChartAt` (from the alive-set measurability of `Spec/Ito/Measurability`);
* `continuousOn_lift_loewnerChartAt`;
* **`measurable_chartTransport_loewnerChartAt`**: `ω ↦ σ (h ω) ∘ f_s⁻¹ + a + k arg f_s′ ∘ f_s⁻¹` is a random
  distribution.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H isOpen_H)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE

namespace Chart

/-- The domain of a centred Loewner chart is the complement of the hull: the points with a forward solution. -/
theorem mem_dom_loewner_iff {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ} :
    z ∈ (Chart.id.loewner w t).dom ↔ 0 < z.im ∧ ∃ u, QuantumZipper.IsForwardSol w z t u := by
  rw [← SetLike.mem_coe, (isConformal_id.loewner hw hw0 ht).coe_dom]
  change z ∈ QuantumZipper.fwdMapInv w t '' H ↔ _
  rw [QuantumZipper.RS.image_fwdMapInv_H hw hw0 ht]
  constructor
  · intro hz
    exact ⟨hz.1, Ito.exists_isForwardSol_of_mem ht hz⟩
  · rintro ⟨hz, u, hu⟩
    exact ⟨hz, Ito.notMem_fwdHull_of_isForwardSol hw hz ht hu⟩

/-- The lift of a centred Loewner chart is continuous on its domain. -/
theorem continuousOn_lift_loewner {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (Chart.id.loewner w t).2.2 (Chart.id.loewner w t).dom := by
  intro z hz
  have hz' : z ∈ H \ QuantumZipper.fwdHull w t := by
    have hz2 : z ∈ (Chart.id.loewner w t).dom := hz
    rw [mem_dom_loewner_iff hw hw0 ht] at hz2
    obtain ⟨hz, u, hu⟩ := hz2
    exact ⟨hz, Ito.notMem_fwdHull_of_isForwardSol hw hz ht hu⟩
  change ContinuousWithinAt (fun z => (QuantumZipper.logDerivFwd w t z).im + 0) _ z
  exact ((Complex.continuous_im.continuousAt.comp (continuousAt_logDerivFwd hw ht hz')).add
    continuousAt_const).continuousWithinAt

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓖 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The Loewner chart at time `s` of the driver path `t ↦ W t ω`. -/
abbrev loewnerChartAt (W : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : Chart :=
  Chart.id.loewner (Ito.rpath (W · ω)) s

theorem continuous_rpath_of_continuous {ω : Ω} (hWc : Continuous fun t => W t ω) :
    Continuous (Ito.rpath (W · ω)) :=
  hWc.comp continuous_real_toNNReal

theorem rpath_zero_of {ω : Ω} (hW0 : W 0 ω = 0) : Ito.rpath (W · ω) 0 = 0 := by
  simp [Ito.rpath, hW0]

theorem isConformal_loewnerChartAt (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (s : ℝ≥0) (ω : Ω) : (loewnerChartAt W s ω).IsConformal :=
  isConformal_id.loewner (continuous_rpath_of_continuous (hWc ω)) (rpath_zero_of (hW0 ω)) s.coe_nonneg

theorem adaptedBefore_top (hWa : Adapted 𝓖 W) : AdaptedBefore 𝓖 (fun _ => ⊤) W := by
  intro t A hA
  have he : {ω | (t : ℝ≥0∞) < ⊤ ∧ W t ω ∈ A} = W t ⁻¹' A := by
    ext ω
    simp
  rw [he]
  exact hWa t hA

/-- For `z ∈ ℍ`, the domain event is the alive set of the Itô coordinates. -/
theorem setOf_mem_dom_loewnerChartAt (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (s : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    {ω | z ∈ (loewnerChartAt W s ω).dom} = Ito.aliveSet W (fun _ => ⊤) univ z s := by
  ext ω
  rw [mem_ofPred_eq, mem_dom_loewner_iff (continuous_rpath_of_continuous (hWc ω)) (rpath_zero_of (hW0 ω))
    s.coe_nonneg]
  simp only [Ito.aliveSet, mem_ofPred_eq, mem_univ, true_and, ENNReal.coe_lt_top, hz]

theorem setOf_mem_dom_loewnerChartAt_of_im_nonpos (hWc : ∀ ω, Continuous fun t => W t ω)
    (hW0 : ∀ ω, W 0 ω = 0) (s : ℝ≥0) {z : ℂ} (hz : ¬ 0 < z.im) :
    {ω | z ∈ (loewnerChartAt W s ω).dom} = ∅ := by
  ext ω
  rw [mem_ofPred_eq, mem_dom_loewner_iff (continuous_rpath_of_continuous (hWc ω)) (rpath_zero_of (hW0 ω))
    s.coe_nonneg]
  simp [hz]

variable (hWa : Adapted 𝓖 W) (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
include hWa hWc hW0

theorem measurableSet_mem_dom_loewnerChartAt (s : ℝ≥0) (z : ℂ) :
    MeasurableSet[𝓖 s] {ω | z ∈ (loewnerChartAt W s ω).dom} := by
  by_cases hz : 0 < z.im
  · rw [setOf_mem_dom_loewnerChartAt hWc hW0 s hz]
    exact Ito.measurableSet_aliveSet (adaptedBefore_top hWa)
      (fun ω _ => (hWc ω).continuousOn) (@MeasurableSet.univ Ω (𝓖 0)) hz s
  · rw [setOf_mem_dom_loewnerChartAt_of_im_nonpos hWc hW0 s hz]
    exact @MeasurableSet.empty Ω (𝓖 s)

theorem measurable_indicator_fwd_loewnerChartAt (s : ℝ≥0) (z : ℂ) :
    Measurable[𝓖 s] ({ω | z ∈ (loewnerChartAt W s ω).dom}.indicator fun ω => (loewnerChartAt W s ω).1 z) := by
  classical
  by_cases hz : 0 < z.im
  · rw [setOf_mem_dom_loewnerChartAt hWc hW0 s hz]
    have h := Ito.measurable_fwdMap_alive (adaptedBefore_top hWa)
      (fun ω _ => (hWc ω).continuousOn) (@MeasurableSet.univ Ω (𝓖 0)) hz s
    convert h using 1
    funext ω
    simp only [indicator, loewnerChartAt]
    rfl
  · rw [setOf_mem_dom_loewnerChartAt_of_im_nonpos hWc hW0 s hz, indicator_empty]
    exact measurable_const

theorem measurable_indicator_lift_loewnerChartAt (s : ℝ≥0) (z : ℂ) :
    Measurable[𝓖 s] ({ω | z ∈ (loewnerChartAt W s ω).dom}.indicator fun ω => (loewnerChartAt W s ω).2.2 z) := by
  classical
  by_cases hz : 0 < z.im
  · rw [setOf_mem_dom_loewnerChartAt hWc hW0 s hz]
    have h := Ito.measurable_logDerivFwd_alive (adaptedBefore_top hWa)
      (fun ω _ => (hWc ω).continuousOn) (@MeasurableSet.univ Ω (𝓖 0)) hz s
    have h' := (Complex.continuous_im.measurable.comp h).add_const (0 : ℝ)
    convert h' using 1
    funext ω
    by_cases hω : ω ∈ Ito.aliveSet W (fun _ => ⊤) univ z s
    · simp only [indicator_of_mem hω, Function.comp_apply, hω, ↓reduceIte]
      rfl
    · simp only [indicator_of_notMem hω, Function.comp_apply, hω, ↓reduceIte, Complex.zero_im, add_zero]
  · rw [setOf_mem_dom_loewnerChartAt_of_im_nonpos hWc hW0 s hz, indicator_empty]
    exact measurable_const

/-- **The field transported by the Loewner map of an adapted continuous driver at time `s` is a random
distribution** (measurable for the ambient σ-algebra; the chart data are `𝓖 s`-measurable). -/
theorem measurable_chartTransport_loewnerChartAt (s : ℝ≥0) {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (σ a k : ℝ) :
    Measurable fun ω => chartTransport (isConformal_loewnerChartAt hWc hW0 s ω) σ a k (h ω) :=
  measurable_chartTransport_random' (isConformal_loewnerChartAt hWc hW0 s)
    (fun z => 𝓖.le s _ (measurableSet_mem_dom_loewnerChartAt hWa hWc hW0 s z))
    (fun z => (measurable_indicator_fwd_loewnerChartAt hWa hWc hW0 s z).mono (𝓖.le s) le_rfl)
    (fun z => (measurable_indicator_lift_loewnerChartAt hWa hWc hW0 s z).mono (𝓖.le s) le_rfl)
    (fun ω => continuousOn_lift_loewner (continuous_rpath_of_continuous (hWc ω))
      (rpath_zero_of (hW0 ω)) s.coe_nonneg) hh σ a k

end Random

/-! ### Random times: dyadic upper approximations -/

/-- The dyadic upper approximation `⌈2ⁿ t⌉ / 2ⁿ` of a time `t`. -/
def dyadicUp (n : ℕ) (t : ℝ≥0) : ℝ≥0 := (⌈(t : ℝ) * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n

theorem coe_dyadicUp (n : ℕ) (t : ℝ≥0) : (dyadicUp n t : ℝ) = (⌈(t : ℝ) * 2 ^ n⌉₊ : ℝ) / 2 ^ n := by
  simp [dyadicUp]

theorem le_dyadicUp (n : ℕ) (t : ℝ≥0) : (t : ℝ) ≤ dyadicUp n t := by
  rw [coe_dyadicUp, le_div_iff₀ (by positivity)]
  exact Nat.le_ceil _

theorem dyadicUp_lt (n : ℕ) (t : ℝ≥0) : (dyadicUp n t : ℝ) < t + 1 / 2 ^ n := by
  rw [coe_dyadicUp, div_lt_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
  exact Nat.ceil_lt_add_one (by positivity)

theorem tendsto_dyadicUp (t : ℝ≥0) : Tendsto (fun n => (dyadicUp n t : ℝ)) atTop (𝓝 t) := by
  have h2 : Tendsto (fun n : ℕ => (t : ℝ) + 1 / 2 ^ n) atTop (𝓝 t) := by
    have h0 : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simp_rw [one_div_pow] at h0
    simpa using tendsto_const_nhds.add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun n => le_dyadicUp n t)
    fun n => (dyadicUp_lt n t).le

section Dyadic

variable {Ω : Type*} [MeasurableSpace Ω] {τ : Ω → ℝ≥0}

theorem measurable_comp_dyadicUp {β : Type*} [MeasurableSpace β] (hτ : Measurable τ)
    {M : ℝ≥0 → Ω → β} (hM : ∀ q, Measurable (M q)) (n : ℕ) :
    Measurable fun ω => M (dyadicUp n (τ ω)) ω := by
  have hk : Measurable fun ω => ⌈(τ ω : ℝ) * 2 ^ n⌉₊ :=
    Nat.measurable_ceil.comp ((measurable_coe_nnreal_real.comp hτ).mul_const _)
  have h := (measurable_from_prod_countable_left (f := fun p : Ω × ℕ => M ((p.2 : ℝ≥0) / 2 ^ n) p.1)
    fun k => hM ((k : ℝ≥0) / 2 ^ n)).comp (measurable_id.prodMk hk)
  exact h

theorem measurableSet_dyadicUp (hτ : Measurable τ) {S : ℝ≥0 → Set Ω} (hS : ∀ q, MeasurableSet (S q))
    (n : ℕ) : MeasurableSet {ω | ω ∈ S (dyadicUp n (τ ω))} := by
  have hk : Measurable fun ω => ⌈(τ ω : ℝ) * 2 ^ n⌉₊ :=
    Nat.measurable_ceil.comp ((measurable_coe_nnreal_real.comp hτ).mul_const _)
  have he : {ω | ω ∈ S (dyadicUp n (τ ω))} =
      ⋃ k : ℕ, ((fun ω => ⌈(τ ω : ℝ) * 2 ^ n⌉₊) ⁻¹' {k}) ∩ S ((k : ℝ≥0) / 2 ^ n) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff, dyadicUp]
    exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨k, hk, h⟩ => hk ▸ h⟩
  rw [he]
  exact MeasurableSet.iUnion fun k => (hk (measurableSet_singleton k)).inter (hS _)

/-- A masked value at a random time is measurable when it is the limit of the values at the dyadic upper
approximations on the mask. -/
theorem measurable_indicator_of_dyadic {β : Type*} [TopologicalSpace β] [PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] [Zero β] (hτ : Measurable τ) {M : ℝ≥0 → Ω → β}
    (hM : ∀ q, Measurable (M q)) {A : Set Ω} (hA : MeasurableSet A) {F : Ω → β}
    (hlim : ∀ ω ∈ A, Tendsto (fun n : ℕ => M (dyadicUp n (τ ω)) ω) atTop (𝓝 (F ω))) :
    Measurable (A.indicator F) := by
  refine measurable_of_tendsto_metrizable (f := fun n => A.indicator fun ω => M (dyadicUp n (τ ω)) ω)
    (fun n => (measurable_comp_dyadicUp hτ hM n).indicator hA) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ A
  · simp only [indicator_of_mem hω]
    exact hlim ω hω
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

end Dyadic

/-! ### The Loewner chart at a random time -/

/-- If `z` is not swallowed at time `t`, it is not swallowed slightly after `t`, the dyadic approximations of `t`
eventually lie there, and the flow and its log-derivative branch are continuous in time up to then. -/
theorem exists_alive_after {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ≥0} {z : ℂ}
    (hz : z ∈ (Chart.id.loewner w t).dom) :
    ∃ T' : ℝ, (t : ℝ) < T' ∧ (∀ᶠ n in atTop, z ∈ (Chart.id.loewner w (dyadicUp n t)).dom ∧
        (dyadicUp n t : ℝ) ∈ Icc 0 T') ∧
      ContinuousOn (fun s => QuantumZipper.fwdMap w s z) (Icc 0 T') ∧
      ContinuousOn (fun s => QuantumZipper.logDerivFwd w s z) (Icc 0 T') := by
  rw [mem_dom_loewner_iff hw hw0 t.coe_nonneg] at hz
  obtain ⟨hzi, u, hu⟩ := hz
  have hK := Ito.notMem_fwdHull_of_isForwardSol hw hzi t.coe_nonneg hu
  obtain ⟨-, T', hT', u', hu'⟩ := (QuantumZipper.FwdHolo.mem_compl_fwdHull_iff t.coe_nonneg).1 ⟨hzi, hK⟩
  have hT'0 : 0 ≤ T' := t.coe_nonneg.trans hT'.le
  refine ⟨T', hT', ?_, Ito.continuousOn_fwdMap_of_continuousOn hT'0 hw.continuousOn hzi ⟨u', hu'⟩,
    Ito.continuousOn_logDerivFwd hw hT'0
      ⟨hzi, Ito.notMem_fwdHull_of_isForwardSol hw hzi hT'0 hu'⟩⟩
  filter_upwards [(tendsto_dyadicUp t).eventually (Iio_mem_nhds hT')] with n hn
  have hle : (dyadicUp n t : ℝ) ≤ T' := le_of_lt hn
  refine ⟨?_, (dyadicUp n t).coe_nonneg, hle⟩
  rw [mem_dom_loewner_iff hw hw0 (dyadicUp n t).coe_nonneg]
  exact ⟨hzi, u', Ito.isForwardSol_of_le hu' (dyadicUp n t).coe_nonneg hle⟩

section RandomTime

variable {Ω : Type*} {𝓗 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ}
  {τ : Ω → ℝ≥0}

/-- The Loewner chart at the random time `τ` of the driver path `t ↦ W t ω`. -/
abbrev loewnerChartAtTime (W : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) : Chart :=
  Chart.id.loewner (Ito.rpath (W · ω)) (τ ω)

/-- The driver stopped at `τ`. -/
def stoppedDrv (W : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ := fun t ω => W (min t (τ ω)) ω

omit mΩ in
theorem isConformal_loewnerChartAtTime (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (ω : Ω) : (loewnerChartAtTime W τ ω).IsConformal :=
  isConformal_id.loewner (continuous_rpath_of_continuous (hWc ω)) (rpath_zero_of (hW0 ω)) (τ ω).coe_nonneg

omit mΩ in
theorem eqOn_rpath_stoppedDrv (ω : Ω) :
    EqOn (Ito.rpath (W · ω)) (Ito.rpath (stoppedDrv W τ · ω)) (Icc 0 (τ ω : ℝ)) := by
  intro r hr
  simp only [Ito.rpath, stoppedDrv]
  rw [min_eq_left (Real.toNNReal_le_iff_le_coe.2 hr.2)]

omit mΩ in
/-- The domain at `τ` only depends on the driver up to `τ`. -/
theorem mem_dom_loewnerChartAtTime_iff (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (ω : Ω) {z : ℂ} :
    z ∈ (loewnerChartAtTime W τ ω).dom ↔ z ∈ (loewnerChartAt (stoppedDrv W τ) (τ ω) ω).dom := by
  have hsc : ∀ ω, Continuous fun t => stoppedDrv W τ t ω := fun ω =>
    (hWc ω).comp (continuous_id.min continuous_const)
  rw [mem_dom_loewner_iff (continuous_rpath_of_continuous (hWc ω)) (rpath_zero_of (hW0 ω)) (τ ω).coe_nonneg,
    mem_dom_loewner_iff (continuous_rpath_of_continuous (hsc ω))
      (rpath_zero_of (by simp [stoppedDrv, hW0])) (τ ω).coe_nonneg]
  simp only [Ito.isForwardSol_iff_of_eqOn (eqOn_rpath_stoppedDrv (W := W) (τ := τ) ω)]

omit mΩ in
theorem fwd_loewnerChartAtTime (ω : Ω) (z : ℂ) :
    (loewnerChartAtTime W τ ω).1 z = (loewnerChartAt (stoppedDrv W τ) (τ ω) ω).1 z :=
  Ito.fwdMap_congr_of_eqOn (eqOn_rpath_stoppedDrv ω)

omit mΩ in
theorem lift_loewnerChartAtTime (ω : Ω) (z : ℂ) :
    (loewnerChartAtTime W τ ω).2.2 z = (loewnerChartAt (stoppedDrv W τ) (τ ω) ω).2.2 z := by
  change (QuantumZipper.logDerivFwd _ _ z).im + 0 = (QuantumZipper.logDerivFwd _ _ z).im + 0
  rw [Ito.logDerivFwd_congr_of_eqOn (eqOn_rpath_stoppedDrv ω) (τ ω).coe_nonneg le_rfl]

omit mΩ in
theorem continuous_stoppedDrv (hWc : ∀ ω, Continuous fun t => W t ω) (ω : Ω) :
    Continuous fun t => stoppedDrv W τ t ω :=
  (hWc ω).comp (continuous_id.min continuous_const)

omit mΩ in
theorem stoppedDrv_zero (hW0 : ∀ ω, W 0 ω = 0) (ω : Ω) : stoppedDrv W τ 0 ω = 0 := by
  simp [stoppedDrv, hW0]

/-- The constant filtration `𝓗`. -/
def constFiltration (h𝓗 : 𝓗 ≤ mΩ) : Filtration ℝ≥0 mΩ :=
  ⟨fun _ => 𝓗, fun _ _ _ => le_rfl, fun _ => h𝓗⟩

variable (h𝓗 : 𝓗 ≤ mΩ) (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
  (hτ : Measurable[𝓗] τ) (hWs : ∀ t, Measurable[𝓗] (stoppedDrv W τ t))
include h𝓗 hWc hW0 hτ hWs

theorem measurableSet_mem_dom_loewnerChartAtTime (z : ℂ) :
    MeasurableSet[𝓗] {ω | z ∈ (loewnerChartAtTime W τ ω).dom} := by
  have hS : ∀ q : ℝ≥0, MeasurableSet[𝓗] {ω | z ∈ (loewnerChartAt (stoppedDrv W τ) q ω).dom} := fun q =>
    measurableSet_mem_dom_loewnerChartAt (𝓖 := constFiltration h𝓗) (fun t => hWs t)
      (continuous_stoppedDrv hWc) (stoppedDrv_zero hW0) q z
  have he : {ω | z ∈ (loewnerChartAtTime W τ ω).dom} = ⋃ n : ℕ,
      {ω | ω ∈ (fun q : ℝ≥0 => {ω | z ∈ (loewnerChartAt (stoppedDrv W τ) q ω).dom}) (dyadicUp n (τ ω))} := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq]
    rw [mem_dom_loewnerChartAtTime_iff hWc hW0]
    have hc := continuous_rpath_of_continuous (continuous_stoppedDrv (τ := τ) hWc ω)
    have h0 := rpath_zero_of (stoppedDrv_zero (τ := τ) hW0 ω)
    constructor
    · intro hz
      obtain ⟨T', -, hev, -, -⟩ := exists_alive_after hc h0 hz
      exact hev.exists.imp fun n hn => hn.1
    · rintro ⟨n, hn⟩
      change z ∈ (Chart.id.loewner _ _).dom at hn
      rw [mem_dom_loewner_iff hc h0 (dyadicUp n (τ ω)).coe_nonneg] at hn
      change z ∈ (Chart.id.loewner _ _).dom
      rw [mem_dom_loewner_iff hc h0 (τ ω).coe_nonneg]
      obtain ⟨hzi, u, hu⟩ := hn
      exact ⟨hzi, u, Ito.isForwardSol_of_le hu (τ ω).coe_nonneg (le_dyadicUp n (τ ω))⟩
  rw [he]
  exact MeasurableSet.iUnion fun n => @measurableSet_dyadicUp Ω 𝓗 τ hτ _ hS n

theorem measurable_indicator_fwd_loewnerChartAtTime (z : ℂ) :
    Measurable[𝓗] ({ω | z ∈ (loewnerChartAtTime W τ ω).dom}.indicator
      fun ω => (loewnerChartAtTime W τ ω).1 z) := by
  have hF : (fun ω => (loewnerChartAtTime W τ ω).1 z) = fun ω =>
      QuantumZipper.fwdMap (Ito.rpath (stoppedDrv W τ · ω)) (τ ω) z :=
    funext fun ω => fwd_loewnerChartAtTime ω z
  rw [hF]
  refine @measurable_indicator_of_dyadic Ω 𝓗 τ ℂ _ _ _ _ _ hτ
    (fun q => {ω | z ∈ (loewnerChartAt (stoppedDrv W τ) q ω).dom}.indicator
      fun ω => (loewnerChartAt (stoppedDrv W τ) q ω).1 z)
    (fun q => measurable_indicator_fwd_loewnerChartAt (𝓖 := constFiltration h𝓗) (fun t => hWs t)
      (continuous_stoppedDrv hWc) (stoppedDrv_zero hW0) q z) _
    (measurableSet_mem_dom_loewnerChartAtTime h𝓗 hWc hW0 hτ hWs z) _ fun ω hω => ?_
  have hω' := (mem_dom_loewnerChartAtTime_iff hWc hW0 ω).1 hω
  obtain ⟨T', hT', hev, hcont, -⟩ := exists_alive_after (continuous_rpath_of_continuous
    (continuous_stoppedDrv (τ := τ) hWc ω)) (rpath_zero_of (stoppedDrv_zero (τ := τ) hW0 ω)) hω'
  have ht : Tendsto (fun n => (dyadicUp n (τ ω) : ℝ)) atTop (𝓝[Icc 0 T'] (τ ω : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicUp _, hev.mono fun n hn => hn.2⟩
  refine ((hcont (τ ω) ⟨(τ ω).coe_nonneg, hT'.le⟩).tendsto.comp ht).congr' ?_
  filter_upwards [hev] with n hn
  rw [Function.comp_apply, indicator_of_mem
    (show ω ∈ {ω' | z ∈ (loewnerChartAt (stoppedDrv W τ) (dyadicUp n (τ ω)) ω').dom} from hn.1)]
  rfl

theorem measurable_indicator_lift_loewnerChartAtTime (z : ℂ) :
    Measurable[𝓗] ({ω | z ∈ (loewnerChartAtTime W τ ω).dom}.indicator
      fun ω => (loewnerChartAtTime W τ ω).2.2 z) := by
  have hF : (fun ω => (loewnerChartAtTime W τ ω).2.2 z) = fun ω =>
      (QuantumZipper.logDerivFwd (Ito.rpath (stoppedDrv W τ · ω)) (τ ω) z).im + 0 :=
    funext fun ω => lift_loewnerChartAtTime ω z
  rw [hF]
  refine @measurable_indicator_of_dyadic Ω 𝓗 τ ℝ _ _ _ _ _ hτ
    (fun q => {ω | z ∈ (loewnerChartAt (stoppedDrv W τ) q ω).dom}.indicator
      fun ω => (loewnerChartAt (stoppedDrv W τ) q ω).2.2 z)
    (fun q => measurable_indicator_lift_loewnerChartAt (𝓖 := constFiltration h𝓗) (fun t => hWs t)
      (continuous_stoppedDrv hWc) (stoppedDrv_zero hW0) q z) _
    (measurableSet_mem_dom_loewnerChartAtTime h𝓗 hWc hW0 hτ hWs z) _ fun ω hω => ?_
  have hω' := (mem_dom_loewnerChartAtTime_iff hWc hW0 ω).1 hω
  obtain ⟨T', hT', hev, -, hcont⟩ := exists_alive_after (continuous_rpath_of_continuous
    (continuous_stoppedDrv (τ := τ) hWc ω)) (rpath_zero_of (stoppedDrv_zero (τ := τ) hW0 ω)) hω'
  have ht : Tendsto (fun n => (dyadicUp n (τ ω) : ℝ)) atTop (𝓝[Icc 0 T'] (τ ω : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadicUp _, hev.mono fun n hn => hn.2⟩
  refine (((Complex.continuous_im.tendsto _).comp
    ((hcont (τ ω) ⟨(τ ω).coe_nonneg, hT'.le⟩).tendsto.comp ht)).add_const (0 : ℝ)).congr' ?_
  filter_upwards [hev] with n hn
  rw [indicator_of_mem
    (show ω ∈ {ω' | z ∈ (loewnerChartAt (stoppedDrv W τ) (dyadicUp n (τ ω)) ω').dom} from hn.1)]
  rfl

/-- **The field transported by the Loewner map `f_τ` at a random time is a random distribution**: for a driver
with continuous paths and `W 0 = 0`, a random time `τ` and a σ-algebra `𝓗 ≤ 𝓕` for which `τ` and the stopped
driver `W_{t ∧ τ}` are measurable (e.g. `𝓗 = 𝓕_τ` for a stopping time of a filtration to which `W` is adapted). -/
theorem measurable_chartTransport_loewnerChartAtTime {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (σ a k : ℝ) :
    Measurable fun ω => chartTransport (isConformal_loewnerChartAtTime (τ := τ) hWc hW0 ω) σ a k (h ω) :=
  measurable_chartTransport_random' (isConformal_loewnerChartAtTime hWc hW0)
    (fun z => h𝓗 _ (measurableSet_mem_dom_loewnerChartAtTime h𝓗 hWc hW0 hτ hWs z))
    (fun z => (measurable_indicator_fwd_loewnerChartAtTime h𝓗 hWc hW0 hτ hWs z).mono h𝓗 le_rfl)
    (fun z => (measurable_indicator_lift_loewnerChartAtTime h𝓗 hWc hW0 hτ hWs z).mono h𝓗 le_rfl)
    (fun ω => continuousOn_lift_loewner (continuous_rpath_of_continuous (hWc ω)) (rpath_zero_of (hW0 ω))
      (τ ω).coe_nonneg) hh σ a k

/-- **Conditional law of the field transported by `f_τ`** (support-restricted hypothesis, the form of the frozen
optional hull coupling at a stopping time: conditionally on `𝓗`, `h` has the characteristic functional
`exp(i M(φ) − ½ ‖φ‖²_{H⁻¹(ℍ∖K_τ)})` for test functions supported off the hull). Then `h ∘ f_τ⁻¹` has, conditionally on
`𝓗`, the characteristic functional `exp(i (M ∘ f_τ⁻¹)(φ) − ½ ‖φ‖²_{H⁻¹(ℍ)})` for every test function `φ`. -/
theorem condExp_cexp_pullField_loewnerChartAtTime {P : Measure Ω} [IsProbabilityMeasure P]
    {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ (loewnerChartAtTime W τ ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝓗] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((loewnerChartAtTime W τ ω).dom : Set ℂ) φ φ : ℝ) : ℂ)))
    (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => Complex.exp (Complex.I *
        (pullField (isConformal_loewnerChartAtTime (τ := τ) hWc hW0 ω) (h ω) φ : ℂ)) | 𝓗] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * (pullField (isConformal_loewnerChartAtTime (τ := τ) hWc hW0 ω) (M ω) φ : ℂ) -
        (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov H φ φ : ℝ) : ℂ)) :=
  condExp_cexp_pullField_random_of_subset h𝓗 (isConformal_loewnerChartAtTime hWc hW0)
    (measurableSet_mem_dom_loewnerChartAtTime h𝓗 hWc hW0 hτ hWs)
    (measurable_indicator_fwd_loewnerChartAtTime h𝓗 hWc hW0 hτ hWs) hh hcond φ

end RandomTime

end Chart

end InteractingSLE
