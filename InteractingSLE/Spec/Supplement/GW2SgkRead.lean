/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Supplement.GW2KM2StopLaw
import InteractingSLE.Spec.Sec5.CrossRestartLawMeas
import InteractingSLE.Spec.Sec5.CrossRestartLawPath
import InteractingSLE.WangWu.UnboundedComponent

/-!
# GW2's stage stop `σ_k`, part 1: the capacity read off a counterflow's own killed path

Packet PROVE-GW2-STAGEMEAN, σ round. At launch `k` the retained counterflow of the stage is the conditional
counterflow `W_k` (`GW2TipSystem.HasLaunchPairEq`), read up to the own time `σ_k` at which the original counterflow
reaches its fixed time `s`. With the launch chart's boundary extension `f`, the original counterflow's trace at the
changed time is `Φ(γ_k r) = −1/f(−1/γ_k r)`, and the original capacity (`2ℓ_k(t)`) is the capacity of
`Φ ∘ γ_k` on `[0, t]`. This file builds that reader on paths and proves it adapted:

* `bdryB f`, `physRead f`: a Borel version of `f` (equal to `f` on `ℍ̄`) and `Φ` (`0` at `0`);
* `capRead f t w`: the capacity of `Φ` applied to the traces of the path `w` at the rational grid of `[0, t]`
  (`LP.traceAt`, `Sec5.CrossRestart.ratGrid`); measurable on path space and depending on `w` on `[0, t]` only;
* `killedPath W ζ ω`: the killed path; **`measurableSet_capRead_lt`**: `{2s < capRead f q (killed path)}` is an
  event of the killed driver's σ-algebra at `q` (`GW2KM2.killedDriverSigma`);
* `capStop f s W ζ`: the first rational time at which the reader exceeds `2s`; **`isStoppingTime_capStop`**: capped
  at any `N`, a stopping time of every driving filtration of `W` (optional time of a right-continuous filtration,
  `isStoppingTime_of_measurableSet_lt`).

Deterministic/measurability; no probabilistic input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW2Sgk

open WangWu (negInv)

/-! ### Optional times of a right-continuous filtration -/

/-- **An optional time of a right-continuous filtration indexed by `ℝ≥0` is a stopping time.** -/
theorem isStoppingTime_of_measurableSet_lt {Ω : Type*} {m : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 m}
    [h𝓕 : 𝓕.IsRightContinuous] {τ : Ω → WithTop ℝ≥0}
    (h : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | τ ω < (t : WithTop ℝ≥0)}) : IsStoppingTime 𝓕 τ := by
  intro t
  apply Filtration.IsRightContinuous.measurableSet
  rw [Filtration.rightCont_eq, MeasurableSpace.measurableSet_iInf]
  intro j
  rw [MeasurableSpace.measurableSet_iInf]
  intro hj
  have hset : {ω | τ ω ≤ (t : WithTop ℝ≥0)} =
      ⋂ n : ℕ, {ω | τ ω < ((min (t + 1 / ((n : ℝ≥0) + 1)) j : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro hle n
      refine lt_of_le_of_lt hle (WithTop.coe_lt_coe.2 (lt_min ?_ hj))
      exact lt_add_of_pos_right t (by positivity)
    · intro hlt
      obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, τ ω = a := WithTop.ne_top_iff_exists.1 (fun htop => by
        have := hlt 0
        rw [htop] at this
        exact not_top_lt this) |>.imp fun _ h => h.symm
      rw [ha]
      have hlim : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ≥0) + 1)) atTop (𝓝 t) := by
        simpa only [add_zero] using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
      refine WithTop.coe_le_coe.2 (ge_of_tendsto' hlim fun n => ?_)
      have h1 := hlt n
      rw [ha, WithTop.coe_lt_coe] at h1
      simpa only [add_zero] using (h1.trans_le (min_le_left _ _)).le
  rw [hset]
  refine MeasurableSet.iInter fun n => 𝓕.mono (min_le_right _ _) _ (h _)

/-! ### The reader -/

/-- A Borel version of a boundary extension: `f` on `ℍ̄`, `0` elsewhere. -/
def bdryB (f : ℂ → ℂ) : ℂ → ℂ := by
  classical
  exact Hbar.piecewise f fun _ => 0

/-- The physical point read in the original counterflow's chart: `Φ z = −1/f(−1/z)`, `Φ 0 = 0`. -/
def physRead (f : ℂ → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if z = 0 then 0 else negInv (bdryB f (negInv z))

/-- **The original capacity read off a path through the chart's boundary extension.** -/
def capRead (f : ℂ → ℂ) (t : ℝ≥0) (w : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  WholeField.hcapHit ((fun q => physRead f (LP.traceAt q w)) '' Sec5.CrossRestart.ratGrid t)

theorem bdryB_eq {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ Hbar) : bdryB f z = f z := by
  classical
  simp only [bdryB, piecewise_eq_of_mem _ _ _ hz]

theorem measurable_bdryB {f : ℂ → ℂ} (hfc : ContinuousOn f Hbar) : Measurable (bdryB f) := by
  classical
  exact hfc.measurable_piecewise continuousOn_const QuantumZipper.isClosed_Hbar.measurableSet

theorem measurable_negInv : Measurable negInv := by
  have : negInv = fun z : ℂ => -z⁻¹ := rfl
  rw [this]
  exact measurable_inv.neg

theorem measurable_physRead {f : ℂ → ℂ} (hfc : ContinuousOn f Hbar) : Measurable (physRead f) := by
  classical
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  exact measurable_negInv.comp ((measurable_bdryB hfc).comp measurable_negInv)

theorem measurable_capRead {f : ℂ → ℂ} (hfc : ContinuousOn f Hbar) (t : ℝ≥0) : Measurable (capRead f t) :=
  Sec5.CrossRestart.measurable_hcapHit_image_of_countable (Sec5.CrossRestart.countable_ratGrid t)
    fun q => (measurable_physRead hfc).comp (LP.measurable_traceAt q)

theorem le_of_mem_ratGrid {t q : ℝ≥0} (hq : q ∈ Sec5.CrossRestart.ratGrid t) : q ≤ t := by
  obtain ⟨r, rfl⟩ := hq
  exact inf_le_right

/-- The reader depends on the path on `[0, t]` only. -/
theorem capRead_congr (f : ℂ → ℂ) {t : ℝ≥0} {w w' : ℝ≥0 → ℝ} (h : ∀ r ≤ t, w r = w' r) :
    capRead f t w = capRead f t w' := by
  unfold capRead
  congr 1
  refine image_congr fun q hq => ?_
  rw [LP.traceAt_congr fun r hr => h r (hr.trans (le_of_mem_ratGrid hq))]

/-! ### The killed path and the adapted stop -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The killed path of a driver. -/
def killedPath (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℝ := by
  classical
  exact fun r => if (r : ℝ≥0∞) < ζ ω then W r ω else 0

omit mΩ in
theorem measurable_killedPath_apply {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {q r : ℝ≥0} (hr : r ≤ q) :
    Measurable[GW2KM2.killedDriverSigma W ζ q] fun ω => killedPath W ζ ω r := by
  classical
  intro B hB
  have hlive : MeasurableSet[GW2KM2.killedDriverSigma W ζ q] {ω | (r : ℝ≥0∞) < ζ ω} := by
    refine MeasurableSpace.measurableSet_generateFrom ⟨r, hr, univ, MeasurableSet.univ, ?_⟩
    ext ω
    simp only [mem_ofPred_eq, mem_univ, and_true]
  have hW : MeasurableSet[GW2KM2.killedDriverSigma W ζ q] {ω | (r : ℝ≥0∞) < ζ ω ∧ W r ω ∈ B} :=
    MeasurableSpace.measurableSet_generateFrom ⟨r, hr, B, hB, rfl⟩
  have e : (fun ω => killedPath W ζ ω r) ⁻¹' B =
      {ω | (r : ℝ≥0∞) < ζ ω ∧ W r ω ∈ B} ∪ ({ω | (r : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ B}) := by
    ext ω
    simp only [killedPath, mem_preimage, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff]
    split_ifs with h0
    · simp [h0]
    · simp [h0]
  rw [e]
  exact hW.union (hlive.compl.inter (MeasurableSet.const _))

omit mΩ in
/-- **The reader's exceedance event at `q` is an event of the killed driver up to `q`.** -/
theorem measurableSet_capRead_lt {f : ℂ → ℂ} (hfc : ContinuousOn f Hbar) {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (a : ℝ≥0∞) (q : ℝ≥0) :
    MeasurableSet[GW2KM2.killedDriverSigma W ζ q] {ω | a < capRead f q (killedPath W ζ ω)} := by
  let _ : MeasurableSpace Ω := GW2KM2.killedDriverSigma W ζ q
  have e : (fun ω => capRead f q (killedPath W ζ ω)) =
      fun ω => capRead f q (fun r => killedPath W ζ ω (min r q)) := funext fun ω =>
    capRead_congr f fun r hr => by rw [min_eq_left hr]
  have hm : Measurable[GW2KM2.killedDriverSigma W ζ q] fun ω => capRead f q (killedPath W ζ ω) := by
    rw [e]
    exact (measurable_capRead hfc q).comp (measurable_pi_iff.2 fun r =>
      measurable_killedPath_apply (W := W) (ζ := ζ) (min_le_right r q))
  exact measurableSet_lt measurable_const hm

/-- **The first rational time at which the reader exceeds `2s`.** -/
def capStop (f : ℂ → ℂ) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ := by
  classical
  exact ⨅ q : ℚ, if 0 ≤ q ∧ 2 * (s : ℝ≥0∞) < capRead f (q : ℝ).toNNReal (killedPath W ζ ω) then
    (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) else ⊤

/-- **The capped stop is a stopping time of every driving filtration of the driver.** -/
theorem isStoppingTime_capStop {f : ℂ → ℂ} (hfc : ContinuousOn f Hbar) {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (P : Measure Ω)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (s N : ℝ≥0) :
    IsStoppingTime (drivingFiltration P hX) fun ω => min (capStop f s W ζ ω) (N : ℝ≥0∞) := by
  classical
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  refine isStoppingTime_of_measurableSet_lt fun t => ?_
  have e : {ω | min (capStop f s W ζ ω) (N : ℝ≥0∞) < (t : ℝ≥0∞)} =
      (⋃ q : ℚ, {ω | (0 ≤ q ∧ (q : ℝ).toNNReal < t) ∧
        2 * (s : ℝ≥0∞) < capRead f (q : ℝ).toNNReal (killedPath W ζ ω)}) ∪ {_ω | N < t} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, min_lt_iff]
    have hN : ((N : ℝ≥0∞) < (t : ℝ≥0∞)) ↔ N < t := ENNReal.coe_lt_coe
    rw [hN]
    refine or_congr ?_ Iff.rfl
    unfold capStop
    rw [iInf_lt_iff]
    refine exists_congr fun q => ?_
    split_ifs with hc
    · have h1 : ((((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (t : ℝ≥0∞)) ↔ (q : ℝ).toNNReal < t :=
        ENNReal.coe_lt_coe
      rw [h1]
      tauto
    · constructor
      · intro h
        exact absurd h not_top_lt
      · rintro ⟨⟨hq, -⟩, hcap⟩
        exact absurd ⟨hq, hcap⟩ hc
  change MeasurableSet[drivingFiltration P hX t] {ω | min (capStop f s W ζ ω) (N : ℝ≥0∞) < (t : ℝ≥0∞)}
  rw [e]
  refine MeasurableSet.union (MeasurableSet.iUnion fun q => ?_) (MeasurableSet.const _)
  by_cases hq : 0 ≤ q ∧ (q : ℝ).toNNReal < t
  · have h1 := measurableSet_capRead_lt hfc (W := W) (ζ := ζ) (2 * (s : ℝ≥0∞)) (q : ℝ).toNNReal
    have h2 := GW2KM2.killedDriverSigma_le_drivingFiltration P hX (q : ℝ).toNNReal _ h1
    have h3 := (drivingFiltration P hX).mono hq.2.le _ h2
    simpa only [hq, true_and] using h3
  · convert MeasurableSet.empty
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    exact fun h => hq h.1

end InteractingSLE.Theorem14.GW2Sgk
