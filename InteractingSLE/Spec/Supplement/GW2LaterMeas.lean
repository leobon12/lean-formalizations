/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2Later
import InteractingSLE.Spec.Supplement.GW2SchedulePast
import InteractingSLE.Spec.Restart.ChartMeasPath

/-!
# GW2a's later pieces: measurable charts of a run and a measurable form of the containment event

Packet PROVE-T14-BR6. The conditional step (`GW2Later.ae_condExpKernel_piece_subset_of_pair`) holds under the regular
conditional law given the retained past. Passing to `P` needs the containment event to be measurable (the
disintegration of a non-measurable event fails in general; ruling R51). This file supplies the measurable objects:

* `measurable_fwdMapInv_of_continuous`: the inverse Loewner map of a measurable continuous driver, at a measurable
  point of `ℍ`, is measurable (Carathéodory: holomorphic in the point, measurable in `ω`);
* `measurable_succChart_inv`: the inverse of the chart of a GW2 run after `k` successful regular pieces, at a
  measurable point of `ℍ` (`GW2Schedule.succChart`);
* `cfDense`, `measurable_infEdist_cfDense`, `closure_cfDense_eq`: the completed counterflow range is the closure of a
  countable set of measurable points (the inverted trace at rational times, read by `LP.traceAt`), so the distance to
  it is measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Later

open CounterflowRange GW2Schedule Exist.StagedLaw

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The inverse Loewner map at a random point -/

omit [MeasurableSpace Ω] in
/-- The inverse Loewner map of a continuous driver is continuous on `ℍ` (as a map on the subtype). -/
theorem continuous_fwdMapInv_subtype {B : ℝ≥0 → Ω → ℝ} (hBc : ∀ ω, Continuous fun t => B t ω)
    (hB0 : ∀ ω, B 0 ω = 0) {T : ℝ} (hT : 0 ≤ T) (ω : Ω) :
    Continuous fun w : {w : ℂ // w ∈ H} => fwdMapInv (fun x : ℝ => B x.toNNReal ω) T w := by
  have hc : Continuous fun x : ℝ => B x.toNNReal ω := (hBc ω).comp continuous_real_toNNReal
  have hc0 : (fun x : ℝ => B x.toNNReal ω) 0 = 0 := by simpa using hB0 ω
  have hd := QuantumZipper.RS.differentiableOn_fwdMapInv hc hc0 hT
  exact hd.continuousOn.comp_continuous continuous_subtype_val fun w => w.2

/-- The inverse Loewner map of a measurable continuous driver at a fixed point of `ℍ` is measurable
(QuantumZipper's `RS.measurable_fwdMapInv_drive` at `κ = 1`). -/
theorem measurable_fwdMapInv_apply {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (hB0 : ∀ ω, B 0 ω = 0) {T : ℝ} (hT : 0 ≤ T)
    (w : {w : ℂ // w ∈ H}) : Measurable fun ω => fwdMapInv (fun x : ℝ => B x.toNNReal ω) T w := by
  have h := QuantumZipper.RS.measurable_fwdMapInv_drive hBm hBc hB0 1 hT w.2
  have heq : (fun ω => fwdMapInv (QuantumZipper.drive 1 B ω) T w) =
      fun ω => fwdMapInv (fun x : ℝ => B x.toNNReal ω) T w := by
    funext ω
    congr 1
    funext x
    simp [QuantumZipper.drive]
  exact heq ▸ h

/-- **Carathéodory at a random point of `ℍ`**: a family continuous on `ℍ` and measurable in `ω` is measurable at a
measurable point of `ℍ`. -/
theorem measurable_apply_subtype_H {u : {w : ℂ // w ∈ H} → Ω → ℂ} (hc : ∀ ω, Continuous fun w => u w ω)
    (hm : ∀ w, Measurable (u w)) {Z : Ω → ℂ} (hZ : Measurable Z) (hZH : ∀ ω, Z ω ∈ H) :
    Measurable fun ω => u ⟨Z ω, hZH ω⟩ ω := by
  have hU : Measurable (Function.uncurry u) := measurable_uncurry_of_continuous_of_measurable hc hm
  have hp : Measurable fun ω => ((⟨Z ω, hZH ω⟩ : {w : ℂ // w ∈ H}), ω) :=
    (hZ.subtype_mk (h := hZH)).prodMk measurable_id
  exact hU.comp hp

/-- **The inverse Loewner map of a measurable continuous driver, at a measurable point of `ℍ`, is measurable.** -/
theorem measurable_fwdMapInv_of_continuous {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (hB0 : ∀ ω, B 0 ω = 0) {T : ℝ} (hT : 0 ≤ T) {Z : Ω → ℂ}
    (hZ : Measurable Z) (hZH : ∀ ω, Z ω ∈ H) :
    Measurable fun ω => fwdMapInv (fun x : ℝ => B x.toNNReal ω) T (Z ω) :=
  measurable_apply_subtype_H (u := fun w ω => fwdMapInv (fun x : ℝ => B x.toNNReal ω) T w)
    (continuous_fwdMapInv_subtype hBc hB0 hT) (measurable_fwdMapInv_apply hBm hBc hB0 hT) hZ hZH

/-! ### The chart of a GW2 run after successful regular pieces -/

open Classical in
/-- The driver of piece `j` stopped at its own time `Δ`, on the event `M` (`0` off `M`). -/
def regDrv (M : Set Ω) (Δ : ℝ≥0∞) (e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ M then (e ω).1 (min (t : ℝ≥0∞) Δ).toNNReal else 0

theorem measurable_regDrv {M : Set Ω} (hM : MeasurableSet M) (Δ : ℝ≥0∞) {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : Measurable e) (t : ℝ≥0) : Measurable (regDrv M Δ e t) := by
  classical
  exact Measurable.ite hM ((measurable_pi_apply _).comp (measurable_fst.comp he)) measurable_const

omit [MeasurableSpace Ω] in
theorem continuous_regDrv {M : Set Ω} {Δ : ℝ≥0∞} (hΔ : Δ ≠ ⊤) {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hc : ∀ ω ∈ M, ContinuousOn (e ω).1 {t | (t : ℝ≥0∞) ≤ Δ}) (ω : Ω) :
    Continuous fun t => regDrv M Δ e t ω := by
  classical
  unfold regDrv
  by_cases hω : ω ∈ M
  · simp only [hω, ite_true]
    have he : ∀ t : ℝ≥0, (min (t : ℝ≥0∞) Δ).toNNReal = min t Δ.toNNReal := fun t => by
      rw [← ENNReal.coe_toNNReal hΔ, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
    simp_rw [he]
    refine (hc ω hω).comp_continuous (continuous_id.min continuous_const) fun t => ?_
    show ((min t Δ.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ Δ
    rw [ENNReal.coe_min, ENNReal.coe_toNNReal hΔ]
    exact min_le_right _ _
  · simp only [hω, ite_false]
    exact continuous_const

omit [MeasurableSpace Ω] in
theorem regDrv_zero {M : Set Ω} {Δ : ℝ≥0∞} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (h0 : ∀ ω ∈ M, (e ω).1 0 = 0)
    (ω : Ω) : regDrv M Δ e 0 ω = 0 := by
  classical
  unfold regDrv
  by_cases hω : ω ∈ M
  · simp only [hω, ite_true, ENNReal.coe_zero, zero_le, min_eq_left, ENNReal.toNNReal_zero]
    exact h0 ω hω
  · simp [hω]

omit [MeasurableSpace Ω] in
/-- On the event `M`, the launch driver of a successful piece is the regularized driver. -/
theorem stopDrv_eq_regDrv {M : Set Ω} {Δ : ℝ≥0∞} {e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω} (hω : ω ∈ M)
    (hs : Δ < (e ω).2) : stopDrv Δ (e ω) = fun x : ℝ => regDrv M Δ e x.toNNReal ω := by
  classical
  funext x
  simp only [stopDrv, retOf, regDrv, hω, ite_true, min_eq_left hs.le]

omit [MeasurableSpace Ω] in
theorem stopTime_eq_of_lt {Δ : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hs : Δ < e.2) :
    stopTime Δ e = (Δ.toNNReal : ℝ) := by
  simp only [stopTime, min_eq_left hs.le]

/-- **The chart of a GW2 run after `k` successful regular pieces is measurable at a measurable point of `ℍ`**: on the
event `M` (on which the first `k` pieces were successful and are continuous up to their own times), the inverse chart
at `Z ω ∈ ℍ` agrees with a measurable function. -/
theorem exists_measurable_succChart_inv (x₀ : ℝ) {Δ : ℕ → ℝ≥0∞} (hΔ : ∀ j, Δ j ≠ ⊤)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hE : ∀ j, Measurable (E j)) {M : Set Ω} (hM : MeasurableSet M) :
    ∀ (k : ℕ), (∀ ω ∈ M, AllSucc Δ (fun j => E j ω) k) →
      (∀ ω ∈ M, ∀ j < k, (E j ω).1 0 = 0 ∧ ContinuousOn (E j ω).1 {t | (t : ℝ≥0∞) ≤ Δ j}) →
      ∀ {Z : Ω → ℂ}, Measurable Z → (∀ ω, Z ω ∈ H) →
        ∃ Y : Ω → ℂ, Measurable Y ∧ ∀ ω ∈ M, (succChart x₀ Δ (fun j => E j ω) k).2.1 (Z ω) = Y ω
  | 0, _, _, Z, hZ, _ => ⟨fun ω => Z ω + x₀, hZ.add_const _, fun _ _ => rfl⟩
  | k + 1, hsucc, hreg, Z, hZ, hZH => by
    have hc : ∀ ω ∈ M, ContinuousOn (E k ω).1 {t | (t : ℝ≥0∞) ≤ Δ k} := fun ω hω =>
      (hreg ω hω k (Nat.lt_succ_self k)).2
    have h0 : ∀ ω ∈ M, (E k ω).1 0 = 0 := fun ω hω => (hreg ω hω k (Nat.lt_succ_self k)).1
    set B : ℝ≥0 → Ω → ℝ := fun t ω => regDrv M (Δ k) (E k) t ω with hBdef
    have hBm : ∀ t, Measurable (B t) := measurable_regDrv hM (Δ k) (hE k)
    have hBc : ∀ ω, Continuous fun t => B t ω := continuous_regDrv (hΔ k) hc
    have hB0 : ∀ ω, B 0 ω = 0 := regDrv_zero h0
    have hT : (0 : ℝ) ≤ ((Δ k).toNNReal : ℝ) := NNReal.coe_nonneg _
    set Z' : Ω → ℂ := fun ω => fwdMapInv (fun x : ℝ => B x.toNNReal ω) ((Δ k).toNNReal : ℝ) (Z ω) with hZ'def
    have hZ'm : Measurable Z' := measurable_fwdMapInv_of_continuous hBm hBc hB0 hT hZ hZH
    have hZ'H : ∀ ω, Z' ω ∈ H := fun ω =>
      QuantumZipper.RS.fwdMapInv_mem_H ((hBc ω).comp continuous_real_toNNReal) (by simpa using hB0 ω) hT (hZH ω)
    obtain ⟨Y, hYm, hY⟩ := exists_measurable_succChart_inv x₀ hΔ hE hM k
      (fun ω hω => ((allSucc_succ.1 (hsucc ω hω)).1))
      (fun ω hω j hj => hreg ω hω j (Nat.lt_succ_of_lt hj)) hZ'm hZ'H
    refine ⟨Y, hYm, fun ω hω => ?_⟩
    have hs : Δ k < (E k ω).2 := (allSucc_succ.1 (hsucc ω hω)).2
    rw [← hY ω hω]
    show (succChart x₀ Δ (fun j => E j ω) k).2.1
        (fwdMapInv (stopDrv (Δ k) (E k ω)) (stopTime (Δ k) (E k ω)) (Z ω)) = _
    rw [stopDrv_eq_regDrv hω hs, stopTime_eq_of_lt hs]

/-! ### The completed counterflow range as the closure of countably many measurable points -/

/-- The inverted counterflow trace point at the rational time `r` (empty if the trace point is `0`). -/
def cfPt (W : ℝ≥0 → ℝ) (r : ℚ) : Set ℂ :=
  {z | LP.traceAt (r : ℝ).toNNReal W ≠ 0 ∧ z = -(LP.traceAt (r : ℝ).toNNReal W)⁻¹}

/-- `0` and the inverted counterflow trace at rational times: a countable dense subset of the completed range. -/
def cfDense (W : ℝ≥0 → ℝ) : Set ℂ := {0} ∪ ⋃ r : ℚ, cfPt W r

theorem infEDist_cfPt (W : ℝ≥0 → ℝ) (r : ℚ) (x : ℂ) :
    infEDist x (cfPt W r) = if LP.traceAt (r : ℝ).toNNReal W ≠ 0 then
      edist x (-(LP.traceAt (r : ℝ).toNNReal W)⁻¹) else ⊤ := by
  by_cases h : LP.traceAt (r : ℝ).toNNReal W ≠ 0
  · have : cfPt W r = {-(LP.traceAt (r : ℝ).toNNReal W)⁻¹} := by
      ext z
      simp [cfPt, h]
    rw [this, infEDist_singleton]
    exact (ite_eq_left_iff.2 fun h' => absurd h h').symm
  · have : cfPt W r = ∅ := by
      ext z
      simp only [cfPt, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun h' => absurd h' h
    rw [this, infEDist_empty]
    exact (ite_eq_right_iff.2 fun h' => absurd h' h).symm

/-- **The distance to the dense set is measurable** for a driver measurable at each time and a measurable point. -/
theorem measurable_infEDist_cfDense {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, Measurable (W t)) {X : Ω → ℂ}
    (hX : Measurable X) : Measurable fun ω => infEDist (X ω) (cfDense fun t => W t ω) := by
  classical
  have hWm : Measurable fun ω => fun t => W t ω := Measurable.of_eval hW
  have htr : ∀ r : ℚ, Measurable fun ω => LP.traceAt (r : ℝ).toNNReal fun t => W t ω := fun r =>
    (LP.measurable_traceAt _).comp hWm
  simp only [cfDense, infEDist_union, infEDist_singleton, infEDist_iUnion, infEDist_cfPt]
  refine (hX.edist measurable_const).min (Measurable.iInf fun r => ?_)
  refine Measurable.ite ?_ (hX.edist ((htr r).inv.neg)) measurable_const
  exact (htr r) (measurableSet_singleton 0).compl

omit [MeasurableSpace Ω] in
/-- **The completed counterflow range is the closure of the dense set** (continuous transient trace). -/
theorem closure_cfDense_eq {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W)
    (hW0 : W 0 = 0) (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    closure (cfDense W) = counterflowCompletedRange W := by
  have htrace : ∀ t : ℝ≥0, LP.traceAt t W = γ t := fun t =>
    LP.traceAt_eq_of_isGeneratingTrace hγ hW.continuousOn hW0 ENNReal.coe_lt_top
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hR := tipSet_infinitySourceChart_top hγ hW hW0
  apply Subset.antisymm
  · refine (isClosed_counterflowCompletedRange hγ hW hW0 htr).closure_subset_iff.2 ?_
    rintro z (hz | hz)
    · exact Or.inr hz
    · obtain ⟨r, hr0, rfl⟩ := mem_iUnion.1 hz
      left
      rw [hR]
      refine ⟨(r : ℝ).toNNReal, ?_, ?_⟩
      · rw [← htrace]; exact hr0
      · rw [← htrace]
  · rintro z (hz | hz)
    · rw [hR] at hz
      obtain ⟨t, ht0, rfl⟩ := hz
      have hφ : ContinuousAt (fun s => -(γ s)⁻¹) t :=
        ((hγc.continuousAt).inv₀ ht0).neg
      rw [mem_closure_iff_nhds]
      intro U hU
      have hV : (fun s => -(γ s)⁻¹) ⁻¹' U ∩ {s | γ s ≠ 0} ∈ 𝓝 t :=
        Filter.inter_mem (hφ hU) ((hγc.continuousAt).eventually_ne ht0)
      obtain ⟨V, hVsub, hVo, htV⟩ := _root_.mem_nhds_iff.1 hV
      obtain ⟨r, hr⟩ := Exist.StagedLaw.denseRange_rat_toNNReal.exists_mem_open hVo ⟨t, htV⟩
      have hr' := hVsub hr
      refine ⟨-(γ (r : ℝ).toNNReal)⁻¹, hr'.1, Or.inr (mem_iUnion.2 ⟨r, ?_, ?_⟩)⟩
      · rw [htrace]; exact hr'.2
      · rw [htrace]
    · exact subset_closure (Or.inl hz)

/-! ### Equal records give equal charts -/

omit [MeasurableSpace Ω] in
/-- A driver continuous up to a finite own time, stopped there, is continuous. -/
theorem continuous_stopAt {Δ : ℝ≥0∞} (hΔ : Δ ≠ ⊤) {w : ℝ≥0 → ℝ} (hc : ContinuousOn w {t | (t : ℝ≥0∞) ≤ Δ}) :
    Continuous fun t : ℝ≥0 => w (min (t : ℝ≥0∞) Δ).toNNReal := by
  have he : ∀ t : ℝ≥0, (min (t : ℝ≥0∞) Δ).toNNReal = min t Δ.toNNReal := fun t => by
    rw [← ENNReal.coe_toNNReal hΔ, ← ENNReal.coe_min, ENNReal.toNNReal_coe, ENNReal.toNNReal_coe]
  simp_rw [he]
  refine hc.comp_continuous (continuous_id.min continuous_const) fun t => ?_
  show ((min t Δ.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ Δ
  rw [ENNReal.coe_min, ENNReal.coe_toNNReal hΔ]
  exact min_le_right _ _

omit [MeasurableSpace Ω] in
/-- **Equal records of two successful pieces continuous up to their own time give equal launch drivers.** -/
theorem stopDrv_eq_of_recOf_eq {Δ : ℝ≥0∞} (hΔ : Δ ≠ ⊤) {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (hs : Δ < e.2)
    (hs' : Δ < e'.2) (hc : ContinuousOn e.1 {t | (t : ℝ≥0∞) ≤ Δ}) (hc' : ContinuousOn e'.1 {t | (t : ℝ≥0∞) ≤ Δ})
    (h : recOf Δ e = recOf Δ e') : stopDrv Δ e = stopDrv Δ e' := by
  have hf : (fun t : ℝ≥0 => e.1 (min (t : ℝ≥0∞) Δ).toNNReal) =
      fun t : ℝ≥0 => e'.1 (min (t : ℝ≥0∞) Δ).toNNReal := by
    refine Continuous.ext_on Exist.StagedLaw.denseRange_rat_toNNReal (continuous_stopAt hΔ hc)
      (continuous_stopAt hΔ hc') ?_
    rintro _ ⟨q, rfl⟩
    have h1 := congrFun (congrArg Prod.fst h) q
    simp only [recOf, readRec, retOf, min_eq_left hs.le, min_eq_left hs'.le] at h1
    exact h1
  funext x
  simp only [stopDrv, retOf, min_eq_left hs.le, min_eq_left hs'.le]
  exact congrFun hf x.toNNReal

omit [MeasurableSpace Ω] in
/-- **Equal records of successful regular pieces give equal charts of a GW2 run.** -/
theorem succChart_eq_of_recOf_eq (x₀ : ℝ) {Δ : ℕ → ℝ≥0∞} (hΔ : ∀ j, Δ j ≠ ⊤)
    {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} :
    ∀ (k : ℕ), AllSucc Δ D k → AllSucc Δ D' k →
      (∀ j < k, ContinuousOn (D j).1 {t | (t : ℝ≥0∞) ≤ Δ j}) →
      (∀ j < k, ContinuousOn (D' j).1 {t | (t : ℝ≥0∞) ≤ Δ j}) →
      (∀ j < k, recOf (Δ j) (D j) = recOf (Δ j) (D' j)) → succChart x₀ Δ D k = succChart x₀ Δ D' k
  | 0, _, _, _, _, _ => rfl
  | k + 1, hs, hs', hc, hc', h => by
    have ih := succChart_eq_of_recOf_eq x₀ hΔ k (allSucc_succ.1 hs).1 (allSucc_succ.1 hs').1
      (fun j hj => hc j (Nat.lt_succ_of_lt hj)) (fun j hj => hc' j (Nat.lt_succ_of_lt hj))
      (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hk := (allSucc_succ.1 hs).2
    have hk' := (allSucc_succ.1 hs').2
    simp only [succChart]
    rw [ih, stopDrv_eq_of_recOf_eq (hΔ k) hk hk' (hc k (Nat.lt_succ_self k)) (hc' k (Nat.lt_succ_self k))
      (h k (Nat.lt_succ_self k)), stopTime_eq_of_lt hk, stopTime_eq_of_lt hk']

/-! ### The containment event at rational times -/

/-- The points `y_n i`, `y_n = 1/(n+1)`, approaching `0` from inside `ℍ`. -/
def yPt (n : ℕ) : ℂ := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I

theorem yPt_mem_H (n : ℕ) : yPt n ∈ H := by
  show 0 < (yPt n).im
  simp only [yPt, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re,
    mul_zero, add_zero]
  positivity

/-- Along `y_n`, a radial limit is a sequential limit. -/
theorem tendsto_comp_yPt {g : ℝ → ℂ} {p : ℂ} (hg : Tendsto (fun y : ℝ => g y) (𝓝[>] 0) (𝓝 p)) :
    Tendsto (fun n : ℕ => g (1 / ((n : ℝ) + 1))) atTop (𝓝 p) := by
  refine hg.comp (tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩)
  exact Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity

omit [MeasurableSpace Ω] in
/-- The points of a continuous generating trace up to its stop lie in `ℍ̄`. -/
theorem trace_mem_Hbar_of_le {w : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w S α)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) ≤ S}) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ S) : α t ∈ Hbar := by
  have hlt : ∀ s : ℝ≥0, (s : ℝ≥0∞) < S → α s ∈ Hbar := fun s hs =>
    QuantumZipper.isClosed_Hbar.mem_of_tendsto
      (hα.tendsto_fwdMapInv_mul_I (hw.mono fun r (hr : (r : ℝ≥0∞) < S) => show (r : ℝ≥0∞) ≤ S from le_of_lt hr)
        hw0 hs)
      (Eventually.of_forall fun y => QuantumZipper.F1.fwdMapInv_mem_Hbar _ _ _)
  rcases ht.lt_or_eq with ht' | ht'
  · exact hlt t ht'
  · rcases eq_zero_or_pos t with h0 | hpos
    · rw [h0, hα.1]
      show (0 : ℝ) ≤ (0 : ℂ).im
      simp
    · have hcont : ContinuousWithinAt α {s | (s : ℝ≥0∞) ≤ S} t := hα.2.1 t ht
      have h1 : Tendsto α (𝓝[<] t) (𝓝 (α t)) :=
        hcont.tendsto.mono_left (nhdsWithin_mono _ fun s (hs : s < t) => by
          show (s : ℝ≥0∞) ≤ S
          rw [← ht']
          exact ENNReal.coe_le_coe.2 hs.le)
      have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
      exact QuantumZipper.isClosed_Hbar.mem_of_tendsto h1
        (eventually_nhdsWithin_of_forall fun s (hs : s < t) => hlt s (by
          rw [← ht']
          exact ENNReal.coe_lt_coe.2 hs))

/-- The stopped driver of a piece, as a real-time driver. -/
abbrev stopR (w : ℝ≥0 → ℝ) (S : ℝ≥0∞) : ℝ → ℝ := fun r : ℝ => w (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal

omit [MeasurableSpace Ω] in
/-- **From containment to the rational-time event**: if the piece read through a chart with boundary limits lies in
`R = closure T`, the distance to `T` along `y_n` tends to `0` at every time up to the stop. -/
theorem tendsto_infEDist_of_tipSet_subset {c : Chart} {f : ℂ → ℂ}
    (hc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {w : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace w S α) (hw : ContinuousOn w {t | (t : ℝ≥0∞) ≤ S}) (hw0 : w 0 = 0) {T R : Set ℂ}
    (hRT : closure T = R) (hsub : c.tipSet (fun r : ℝ≥0 => w (min (r : ℝ≥0∞) S).toNNReal) S ⊆ R) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ S) :
    Tendsto (fun n : ℕ => infEDist (c.2.1 (fwdMapInv (stopR w S) t (yPt n))) T) atTop (𝓝 0) := by
  have htip := tendsto_tip_stopped_of_tendsto hα hw hw0 ht (hc (α t) (trace_mem_Hbar_of_le hα hw hw0 ht))
  have hseq := tendsto_comp_yPt htip
  have hmem : f (α t) ∈ R := hsub ⟨t, ht, htip⟩
  have h0 : infEDist (f (α t)) T = 0 := by
    rw [← mem_closure_iff_infEDist_zero, hRT]
    exact hmem
  rw [← h0]
  exact (continuous_infEDist.tendsto _).comp hseq

omit [MeasurableSpace Ω] in
/-- **From the rational-time event to containment**: if the distance to `T` tends to `0` along `y_n` at every rational
time up to the stop, the piece read through the chart lies in `closure T` (continuity of `f ∘ α`, density). -/
theorem tipSet_subset_of_tendsto_infEDist {c : Chart} {f : ℂ → ℂ}
    (hc : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) {w : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace w S α) (hw : ContinuousOn w {t | (t : ℝ≥0∞) ≤ S}) (hw0 : w 0 = 0) {T R : Set ℂ}
    (hRT : closure T = R)
    (h : ∀ q : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S →
      Tendsto (fun n : ℕ => infEDist (c.2.1 (fwdMapInv (stopR w S) (q : ℝ).toNNReal (yPt n))) T) atTop (𝓝 0)) :
    c.tipSet (fun r : ℝ≥0 => w (min (r : ℝ≥0∞) S).toNNReal) S ⊆ R := by
  have hHb : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht => trace_mem_Hbar_of_le hα hw hw0 ht
  have hRc : IsClosed R := hRT ▸ isClosed_closure
  have hq : ∀ q : ℚ, (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S → f (α (q : ℝ).toNNReal) ∈ R := fun q hqS => by
    have htip := tendsto_tip_stopped_of_tendsto hα hw hw0 hqS (hc _ (hHb _ hqS))
    have hseq := tendsto_comp_yPt htip
    have h1 := (continuous_infEDist (s := T)).tendsto _ |>.comp hseq
    have h2 := tendsto_nhds_unique h1 (h q hqS)
    rw [← hRT, mem_closure_iff_infEDist_zero]
    exact h2
  rw [tipSet_stopped_eq_of_tendsto hα hw hw0 fun t ht => hc (α t) (hHb t ht)]
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  -- continuity of `f ∘ α` within `[0, S]`, and density of rational times below `t`
  have hfc := GW1P.continuousOn_of_tendsto hc
  have hαc : ContinuousOn α {s | (s : ℝ≥0∞) ≤ S} := hα.2.1
  have hg : ContinuousWithinAt (fun s => f (α s)) {s | (s : ℝ≥0∞) ≤ S} t :=
    (hfc.comp hαc fun s hs => hHb s hs) t ht
  set Qs : Set ℝ≥0 := {s | s ≤ t} ∩ range fun q : ℚ => (q : ℝ).toNNReal with hQs
  have hQsub : Qs ⊆ {s | (s : ℝ≥0∞) ≤ S} := fun s hs => le_trans (ENNReal.coe_le_coe.2 hs.1) ht
  have htQ : t ∈ closure Qs := by
    rcases eq_zero_or_pos t with h0 | hpos
    · refine subset_closure ⟨le_refl t, 0, ?_⟩
      simp [h0]
    · have h1 : t ∈ closure (Iio t) := by
        rw [closure_Iio' (show (Iio t).Nonempty from ⟨0, hpos⟩)]
        exact Set.mem_Iic.2 le_rfl
      have h2 : Iio t ⊆ closure (Iio t ∩ range fun q : ℚ => (q : ℝ).toNNReal) :=
        Exist.StagedLaw.denseRange_rat_toNNReal.open_subset_closure_inter isOpen_Iio
      have h3 : closure (Iio t ∩ range fun q : ℚ => (q : ℝ).toNNReal) ⊆ closure Qs :=
        closure_mono fun s hs => ⟨show s ≤ t from le_of_lt (Set.mem_Iio.1 hs.1), hs.2⟩
      exact h3 (closure_minimal h2 isClosed_closure h1)
  have hmem := (hg.mono hQsub).mem_closure_image htQ
  refine (closure_minimal ?_ hRc) hmem
  rintro _ ⟨s, ⟨hst, q, rfl⟩, rfl⟩
  exact hq q (hQsub ⟨hst, q, rfl⟩)

end GW2Later

end Theorem14

end InteractingSLE
