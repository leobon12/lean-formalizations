/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentG
import InteractingSLE.Spec.Exist.FlowField

/-!
# Locality of the continuation threshold: the finite-word calculation

Packet PROVE-L1-LL. The collision group on either side is a prefix of the original
force word. A real cut off the jump candidates identifies its weight with the
boundary height there. Thus two boundary data agreeing at common collision cuts
give the same threshold condition, even when their force words have different sizes.

`HasCommonCollisionCuts` records the remaining geometric input about two concrete
states. This file proves the algebraic implication; it does not assert that traces
with the same hull family satisfy that input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.FlowStopIdentLL

variable {κ θ y : ℝ} {b bR : ℝ → ℝ} {J JR : Finset ℝ}

/-- A left collision prefix has the boundary height at any cut representing it. -/
theorem sum_collisionL_eq_height (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J) {a w : ℝ}
    {vL : Fin (flowLineNL b J y) → ℝ} (ha : a < y) (haJ : a ∉ J)
    (hcut : ∀ i, vL i = w ↔ a - y < flowLineXL b J y i) :
    (∑ i ∈ univ.filter (fun i => vL i = w), flowLineRhoL κ b J y θ i) =
      -(b a + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  have hneg : a - y < 0 := sub_neg.2 ha
  have hJ : a - y + y ∉ J := by rwa [sub_add_cancel]
  have h := Exist.forceBoundaryData_flowLine_seed hκ hb y θ hneg.ne hJ
  have hf : univ.filter (fun i => vL i = w) =
      univ.filter (fun i => a - y < flowLineXL b J y i) :=
    Finset.filter_congr fun i _ => hcut i
  rw [hf]
  simp only [forceBoundaryData, hneg, ↓reduceIte, sub_add_cancel] at h
  have hΛ : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  change -sleLambda κ * (1 + _) = _ at h
  apply (eq_sub_iff_add_eq).2
  apply (eq_div_iff hΛ).2
  nlinarith only [h]

/-- A right collision prefix has the boundary height at any cut representing it. -/
theorem sum_collisionR_eq_height (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J) {a w : ℝ}
    {vR : Fin (flowLineNR b J y) → ℝ} (ha : y < a) (haJ : a ∉ J)
    (hcut : ∀ i, vR i = w ↔ flowLineXR b J y i ≤ a - y) :
    (∑ i ∈ univ.filter (fun i => vR i = w), flowLineRhoR κ b J y θ i) =
      (b a + θ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
  have hpos : 0 < a - y := sub_pos.2 ha
  have hJ : a - y + y ∉ J := by rwa [sub_add_cancel]
  have h := Exist.forceBoundaryData_flowLine_seed hκ hb y θ hpos.ne' hJ
  have hf : univ.filter (fun i => vR i = w) =
      univ.filter (fun i => flowLineXR b J y i ≤ a - y) :=
    Finset.filter_congr fun i _ => hcut i
  rw [hf]
  simp only [forceBoundaryData, not_lt.2 hpos.le, ↓reduceIte, sub_add_cancel] at h
  have hΛ : sleLambda κ ≠ 0 := (Sec4.sleLambda_pos hκ).ne'
  change sleLambda κ * (1 + _) = _ at h
  apply (eq_sub_iff_add_eq).2
  apply (eq_div_iff hΛ).2
  nlinarith only [h]

/-- Two states have common collision cuts in `O`: on each side either neither
state has a collision, or their colliding marks are the prefixes selected by one
real cut in `O`, off both finite sets of jump candidates. This is a geometric
predicate on concrete states, independent of the weights and boundary heights. -/
def HasCommonCollisionCuts (b : ℝ → ℝ) (J : Finset ℝ) (bR : ℝ → ℝ)
    (JR : Finset ℝ) (y : ℝ) (O : Set ℝ) (w : ℝ)
    (vL : Fin (flowLineNL b J y) → ℝ) (vR : Fin (flowLineNR b J y) → ℝ)
    (wR : ℝ) (vLR : Fin (flowLineNL bR JR y) → ℝ)
    (vRR : Fin (flowLineNR bR JR y) → ℝ) : Prop :=
  (((∀ i, vL i ≠ w) ∧ ∀ i, vLR i ≠ wR) ∨
    ∃ a : ℝ, a ∈ O ∧ a < y ∧ a ∉ J ∧ a ∉ JR ∧
      (∀ i, vL i = w ↔ a - y < flowLineXL b J y i) ∧
      (∀ i, vLR i = wR ↔ a - y < flowLineXL bR JR y i)) ∧
  (((∀ i, vR i ≠ w) ∧ ∀ i, vRR i ≠ wR) ∨
    ∃ a : ℝ, a ∈ O ∧ y < a ∧ a ∉ J ∧ a ∉ JR ∧
      (∀ i, vR i = w ↔ flowLineXR b J y i ≤ a - y) ∧
      (∀ i, vRR i = wR ↔ flowLineXR bR JR y i ≤ a - y))

/-- **The finite-word part of (LL).** Common collision cuts where the boundary
data agree identify both colliding weight sums, hence the threshold conditions.
The force words may have different numbers and locations of marks. -/
theorem thresholdCondition_iff_of_commonCollisionCuts (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) {O : Set ℝ}
    (hbbR : ∀ a ∈ O, b a = bR a) {w wR : ℝ}
    {vL : Fin (flowLineNL b J y) → ℝ} {vR : Fin (flowLineNR b J y) → ℝ}
    {vLR : Fin (flowLineNL bR JR y) → ℝ} {vRR : Fin (flowLineNR bR JR y) → ℝ}
    (hcuts : HasCommonCollisionCuts b J bR JR y O w vL vR wR vLR vRR) :
    ForceWord.ThresholdCondition (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ)
        w vL vR ↔
      ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
        (flowLineRhoR κ bR JR y θ) wR vLR vRR := by
  classical
  obtain ⟨hL, hR⟩ := hcuts
  have hsumL :
      (∑ i ∈ univ.filter (fun i => vL i = w), flowLineRhoL κ b J y θ i) =
      ∑ i ∈ univ.filter (fun i => vLR i = wR), flowLineRhoL κ bR JR y θ i := by
    rcases hL with ⟨hL, hLR⟩ | ⟨a, haO, hay, haJ, haJR, hcut, hcutR⟩
    · simp only [Finset.filter_eq_empty_iff.2 (fun i _ => hL i),
        Finset.filter_eq_empty_iff.2 (fun i _ => hLR i), Finset.sum_empty]
    · rw [sum_collisionL_eq_height hκ hb hay haJ hcut,
        sum_collisionL_eq_height hκ hbR hay haJR hcutR, hbbR a haO]
  have hsumR :
      (∑ i ∈ univ.filter (fun i => vR i = w), flowLineRhoR κ b J y θ i) =
      ∑ i ∈ univ.filter (fun i => vRR i = wR), flowLineRhoR κ bR JR y θ i := by
    rcases hR with ⟨hR, hRR⟩ | ⟨a, haO, hay, haJ, haJR, hcut, hcutR⟩
    · simp only [Finset.filter_eq_empty_iff.2 (fun i _ => hR i),
        Finset.filter_eq_empty_iff.2 (fun i _ => hRR i), Finset.sum_empty]
    · rw [sum_collisionR_eq_height hκ hb hay haJ hcut,
        sum_collisionR_eq_height hκ hbR hay haJR hcutR, hbbR a haO]
  unfold ForceWord.ThresholdCondition
  rw [hsumL, hsumR]

/-- If the path is still inside an open buffer at a finite exit stop, that stop
is its available lifetime. Only continuity strictly before the lifetime is used. -/
theorem eq_lifetime_of_mem_exitTime {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} {V : Set ℂ}
    (hV : IsOpen V) (hc : ContinuousOn Γ {t | (t : ℝ≥0∞) < U}) {T : ℝ≥0}
    (he : (T : ℝ≥0∞) = RLC.exitTime V Γ U) (hmem : Γ T ∈ V) :
    (T : ℝ≥0∞) = U := by
  have hle : (T : ℝ≥0∞) ≤ U := he ▸ min_le_left _ _
  by_contra hne
  have hlt : (T : ℝ≥0∞) < U := lt_of_le_of_ne hle hne
  have hnhd : {t : ℝ≥0 | (t : ℝ≥0∞) < U} ∈ 𝓝 T :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hlt
  have hca : ContinuousAt Γ T := hc.continuousAt hnhd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    (Filter.inter_mem (hca.preimage_mem_nhds (hV.mem_nhds hmem)) hnhd)
  let δ : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
  have hδ : (0 : ℝ≥0) < δ := half_pos hε
  have hnear : ∀ s : ℝ≥0, T ≤ s → s < T + δ →
      s ∈ Metric.ball T ε := by
    intro s hs hst
    rw [Metric.mem_ball, NNReal.dist_eq,
      abs_of_nonneg (sub_nonneg.2 (show (T : ℝ) ≤ s from hs))]
    have hst' : (s : ℝ) < T + ε / 2 := hst
    linarith only [hst', hε]
  have hTδ : T + δ / 2 ∈ Metric.ball T ε :=
    hnear _ (le_add_of_nonneg_right zero_le) (by
      simpa only [add_comm] using add_lt_add_left (NNReal.half_lt_self hδ.ne') T)
  have hall : ∀ s : ℝ≥0, s < T + δ / 2 → Γ s ∈ V := by
    intro s hs
    rcases lt_or_ge s T with hsT | hsT
    · exact FlowStopIdentG.mem_of_lt_exitTime
        (he ▸ ENNReal.coe_lt_coe.2 hsT)
    · have hhalf : T + δ / 2 ≤ T + δ := by
        simpa only [add_comm] using add_le_add_left
          (half_le_self (show (0 : ℝ≥0) ≤ δ from zero_le)) T
      exact (hball (hnear s hsT (hs.trans_le hhalf))).1
  have hX : ((T + δ / 2 : ℝ≥0) : ℝ≥0∞) ≤
      ⨅ (s : ℝ≥0) (_ : Γ s ∉ V), (s : ℝ≥0∞) := by
    refine le_iInf₂ fun s hs => ?_
    exact ENNReal.coe_le_coe.2 (le_of_not_gt fun hst => hs (hall s hst))
  have hstop : ((T + δ / 2 : ℝ≥0) : ℝ≥0∞) ≤ RLC.exitTime V Γ U :=
    le_min (hball hTδ).2.le hX
  rw [← he, ENNReal.coe_le_coe] at hstop
  exact (not_le_of_gt (lt_add_of_pos_right T (half_pos hδ))) hstop

/-- **The deterministic lifetime clause, conditional on the geometric cuts.**
At a stop inside `V`, maximality of the original path and common collision cuts
give the replacement word's threshold condition. `hcuts` is the undischarged
geometric input; `hc` concerns the chosen continuous endpoint version. -/
theorem thresholdCondition_at_exit_of_commonCollisionCuts (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) {O : Set ℝ}
    (hbbR : ∀ a ∈ O, b a = bR a) {V : Set ℂ} (hV : IsOpen V)
    {w β : ℝ≥0 → ℝ} {vL : Fin (flowLineNL b J y) → ℝ≥0 → ℝ}
    {vR : Fin (flowLineNR b J y) → ℝ≥0 → ℝ} {U : ℝ≥0∞}
    (hp : IsIntegratedSLEPath κ (flowLineXL b J y) (flowLineXR b J y)
      (flowLineRhoL κ b J y θ) (flowLineRhoR κ b J y θ) w vL vR β U)
    {Γ : ℝ≥0 → ℂ} (hΓ : ContinuousOn Γ {t | (t : ℝ≥0∞) < U})
    {T : ℝ≥0} (he : (T : ℝ≥0∞) = RLC.exitTime V Γ U) (hmem : Γ T ∈ V)
    (hc : ContinuousOn (fun t => (w t, fun i => vL i t, fun j => vR j t)) (Iic T))
    {wR : ℝ} {vLR : Fin (flowLineNL bR JR y) → ℝ}
    {vRR : Fin (flowLineNR bR JR y) → ℝ}
    (hcuts : HasCommonCollisionCuts b J bR JR y O (w T)
      (fun i => vL i T) (fun j => vR j T) wR vLR vRR) :
    ForceWord.ThresholdCondition (flowLineRhoL κ bR JR y θ)
      (flowLineRhoR κ bR JR y θ) wR vLR vRR := by
  have hU := eq_lifetime_of_mem_exitTime hV hΓ he hmem
  have hf := hp.isForcePath
  apply (thresholdCondition_iff_of_commonCollisionCuts hκ hb hbR hbbR hcuts).1
  rcases eq_or_lt_of_le (show (0 : ℝ≥0) ≤ T from zero_le) with hT | hT
  · subst T
    have hthr := hf.threshold_of_eq_zero hU.symm
    simpa only [hf.w_zero, hf.vL_zero, hf.vR_zero] using hthr
  · exact hf.threshold_of_tendsto hT hU
      ((hc T self_mem_Iic).tendsto.mono_left
        (nhdsWithin_mono _ Iio_subset_Iic_self))

end InteractingSLE.Restart.FlowStopIdentLL
