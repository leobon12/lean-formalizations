/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreeWire
import InteractingSLE.Spec.Sec5.CrossCondStagedK2Cand
import InteractingSLE.Spec.Wire.PartAClearanceRestart

/-!
# Proposition 5.13's concrete experiments under the clearance form of Part A: the good sets

Packet PROVE-STRIPMARKS. The concrete root experiment of PROVE-STAGED9 (`CrossCond.StagedK2.rootCandExpK'`) and the
concrete node experiments of PROVE-PROP59-NODETREE (`Prop59NodeTree.nodeCandExpF`) take the old Part A input
`PartAInputsSixteenDiv`, which Theorem 1.2's current wiring no longer supplies (PROVE-WIRE-PARTA uses the clearance
form `PartAInputsSixteenDivOfClearance`). Every use of it reduces to one fact: the Figure 5.1 counterflow has infinite
lifetime and stays in `ℍ` (`Prop513Wire.fig51_trace_mem_H_of_partA`), which the clearance form already gives
(`Prop513Wire.fig51_trace_mem_H_of_partA_of_clearance`, landed). This file restates the chain above it with the
clearance form; every proof is the landed one with that single lemma replaced:

* `ae_cfHistory_mem_goodHitSet_of_clearance` (`Prop59PiecesRoot`), `ae_cfHistory_mem_goodSet49_of_clearance`
  (`Prop59PiecesMarks`);
* `ae_mem_nodeGood_of_clearance` (`Prop59NodeTreeData`), `ae_farGaps_nodeData_of_clearance` (`Prop59NodeTreeExp`),
  `ae_alive_of_nodeActive_of_clearance` (`Prop59NodeTreeActive`).

R48: nothing uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function Metric
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.StripMarks

open Sec5 Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec5.Prop513Target Exist.StagedLaw Exist.Staged LQGMetric
  Sec7.AdmCode Restart Sec4 Theorem14.StagedReg Sec5.GlueCond Sec5.CrossCond.Word49 WangWu LawUnique
  Sec5.Prop59System Sec5.Prop59Stage Sec5.Prop59Pieces Sec5.Prop59Nodes Sec5.Prop59NodeTree
open Sec5.Prop513Wire (StripReverseVisitLaw)

/-! ### The good hitting set and the strict junction gaps -/

/-- **The counterflow history is a good hitting history** almost surely
(`Prop59Pieces.ae_cfHistory_mem_goodHitSet` with the clearance form of Part A). -/
theorem ae_cfHistory_mem_goodHitSet_of_clearance
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω)) :
    ∀ᵐ ω ∂P, Cond44Ref.cfHistory W ζ ω ∈ goodHitSet ∧ ζ ω = ⊤ ∧ Continuous (fun t => W t ω) := by
  have hreg := Prop513Wire.fig51_trace_mem_H_of_partA_of_clearance hA hκ hκ4 hb hG hcf
  have hcont := CrossRestart.ae_continuousOn_of_isStripCounterflowDriver hcf
  filter_upwards [hreg, hcont, htr] with ω hω hc' hγ
  have hζ := hω.1
  rw [hζ] at hγ hc'
  have hw : Continuous fun t => W t ω :=
    continuousOn_univ.1 (by simpa only [ENNReal.coe_lt_top, ofPred_true] using hc'.1)
  refine ⟨cfHistory_mem_goodHitSet hζ hw hc'.2 hγ fun t ht x _ he => ?_, hζ, hw⟩
  have hH := hω.2 _ hγ t ht
  rw [he] at hH
  exact lt_irrefl _ (show (0 : ℝ) < ((x : ℂ)).im from hH) |>.elim

/-- **The counterflow history has strict junction gaps** at every positive time `r`, almost surely
(`Prop59Pieces.ae_cfHistory_mem_goodSet49` with the clearance form of Part A). -/
theorem ae_cfHistory_mem_goodSet49_of_clearance {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsFig51Bounds κ a b a' b') {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {r : ℝ≥0} (hr : 0 < r) :
    ∀ᵐ ω ∂P, Cond44Ref.cfHistory W ζ ω ∈ goodSet49 r := by
  obtain ⟨b₀, J₀, _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  have hreg := Prop513Wire.fig51_trace_mem_H_of_partA_of_clearance hA hκ hκ4 hb hG hcf
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk'
      (Theorem15.isOrderedForceWord_flowLine b₀ J₀ 0) hadm hC.1, hC.1.ae_isIntegratedSLEPath, hreg]
    with ω ⟨hζ, hsep, η, hη⟩ hp hω
  have hw : Continuous fun t => W t ω := by
    have := hp.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  refine cfHistory_mem_goodSet49 hp hζ hw hsep (iL := ⟨0, Nat.zero_lt_succ _⟩) rfl (iR := ⟨0, Nat.zero_lt_succ _⟩) rfl
    hη (fun t ht x _ he => ?_) hr
  have hH := hω.2 η hη t ht
  rw [he] at hH
  exact lt_irrefl _ (show (0 : ℝ) < ((x : ℂ)).im from hH) |>.elim

/-! ### The node experiments' good sets -/

section Node

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
  {E : Schedule → ℕ → Ω → Driver} {s : Schedule} {nL₀ nR₀ : ℕ} {r : ℝ≥0}

/-- **The node good set has full measure** (`Prop59NodeTree.ae_mem_nodeGood` with the clearance form of Part A). -/
theorem ae_mem_nodeGood_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) :
    ∀ᵐ ω ∂P, ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s := by
  have hg := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSchedF (nodeFlag s) j t)
  have hae : ∀ᵐ ω ∂P, NodeGood x₀ h44 hκ hκ4 hb h W ζ s ω := by
    filter_upwards [hg, ae_cfHistory_mem_goodHitSet_of_clearance hκ hκ4 hb hA hG hcf htr] with ω hgω hcω
    exact ⟨hcω, fun j t hv => (isProperArc_qPathF_of h44 hκ hκ4 _ _ (hgω j t hv)).1⟩
  rw [ae_iff]
  have e : {ω | ¬ ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s} =
      toMeasurable P {ω | ¬ NodeGood x₀ h44 hκ hκ4 hb h W ζ s ω} := by
    ext ω; simp [nodeGood]
  rw [e, measure_toMeasurable]
  exact ae_iff.1 hae

omit [StandardBorelSpace Ω] in
/-- **The far gaps at the node tip are strictly positive** (`Prop59NodeTree.ae_farGaps_nodeData` with the clearance
    form of
Part A). -/
theorem ae_farGaps_nodeData_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (hr : 0 < r)
    (noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ω ∈ (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r (fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
        (fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) noise).alive (nodeLen s) (nodePre s) →
      ((nodeData x₀ h44 hκ hκ4 hb P h W ζ s r (fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
        (fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) noise).marks (nodeLen s) (nodePre s) ω).1
          (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ _))) < 0 ∧
      0 < ((nodeData x₀ h44 hκ hκ4 hb P h W ζ s r (fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
        (fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) noise).marks (nodeLen s) (nodePre s) ω).2
          (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ _))) := by
  have hhm : Measurable h := hG.1
  have hD := isReg_nodeData x₀ h44 hκ hκ4 hb (s := s) (r := r) (noise := noise)
    (xL0 := fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
    (xR0 := fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) hhm hcf
    ((measurable_rootXL (x₀ := x₀) hκ hb r).comp (measurable_cfHistory_of_strip hcf))
    ((measurable_rootXR (x₀ := x₀) hκ hb r).comp (measurable_cfHistory_of_strip hcf))
  have hT := isTree_nodeData x₀ h44 hκ hκ4 hb (P := P) (h := h) (W := W) (ζ := ζ) (s := s) (r := r)
    (xL0 := fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
    (xR0 := fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) (noise := noise)
  filter_upwards [ae_cfHistory_mem_goodSet49_of_clearance hκ hκ4 hb hA hG hcf hr] with ω hω hAl
  have hS := isSpine_nodeData x₀ h44 hκ hκ4 hb hAl
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, -⟩ :=
    ((hD.isKilledFamily (nodeLen s) (nodePre s)).arc ω).exists_kPath_trace (TreeData.startCap_lt_kLife hD hAl)
  have hj := rootXL_farL_neg x₀ hκ hb hω
  have hq0 : 0 < qLast (nodeLen s) (nodePre s) := by
    rw [← lastO_eq isValid_nodePre, lastO_nodePre]
    exact_mod_cast terminalRat_pos s
  exact TreeData.farGaps_spine hD hT hS hw hEq htS.le hw0 (rootNL_pos _) (rootNR_pos _) hj.1.le hj.2.le hq0

/-- **On the event `r < T_z` the node prefix is pre-contact at `r`** (`Prop59NodeTree.ae_alive_of_nodeActive` with
the clearance form of Part A). -/
theorem ae_alive_of_nodeActive_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ) (n : ℕ) (r : ℚ) {nL₀ nR₀ : ℕ}
    (xL0 : Ω → Fin nL₀ → ℝ) (xR0 : Ω → Fin nR₀ → ℝ) (noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ω ∈ nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n) r →
      ω ∈ (nodeData x₀ h44 hκ hκ4 hb P h W ζ (scheduleAt n) (r : ℝ).toNNReal xL0 xR0 noise).alive
        (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) := by
  set s := scheduleAt n with hsdef
  let c := sourceWord (x₀ := x₀) hκ hb
  have hc : ExtremeHeights κ c := sourceWord_extreme hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  have hreg := Prop513Wire.fig51_trace_mem_H_of_partA_of_clearance hA hκ hκ4 hb hG hcf
  have hζ := hreg.mono fun _ hω => hω.1
  have htrTop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [htr, hζ] with ω hω hζω
    rwa [hζω] at hω
  have hH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H := by
    filter_upwards [hreg, htrTop] with ω hω hγω
    exact hω.2 _ hγω
  have hi := Prop513Wire.ae_driverTree_interior h44 hκ hκ4 c hc hhQ hE hR
  have h57 := Prop513Wire.targetLemma57_of_stripReverseVisit (Real.exp_pos _) (htrTop.mono fun _ hω => hω.1) hH
    hi hVisit
  have hg := ae_codeGood h44 hκ hκ4 hb hG hE hR (candSchedF (nodeFlag s) (nodeLen s) (nodePre s))
  obtain ⟨b₀, J₀, _, _, hfl, _⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hW0 : ∀ᵐ ω ∂P, W 0 ω = 0 := hC.1.ae_isIntegratedSLEPath.mono fun _ hp => hp.1
  filter_upwards [ae_mem_nodeGood_of_clearance x₀ h44 hκ hκ4 hb (s := s) hA hG hcf htr hE hR, h57, hi, hg,
    ae_prefixDriver_eq_joined h44 hκ hκ4 hb hG hE hR, htrTop, hW0] with ω hgood h57ω hiω hgω hpω hγω hw0 hact
  obtain ⟨⟨hy, hζω, hw⟩, -⟩ := nodeGood_spec x₀ h44 hκ hκ4 hb hgood
  have hcg := cfGood_of_mem_goodHitSet hy (r : ℝ).toNNReal
  obtain ⟨-, hK⟩ := revChart_eq_ownComponentChart (r := r) hy hζω hw 0
  have hGc : ω ∈ (nodeData x₀ h44 hκ hκ4 hb P h W ζ s (r : ℝ).toNNReal xL0 xR0 noise).Gc (nodeLen s) (nodePre s) :=
    ⟨nodeValid_nodePre, hgood⟩
  have hτ : qLast (nodeLen s) (nodePre s) = (treeTime n : ℝ) := by
    rw [← lastO_eq isValid_nodePre, lastO_nodePre, treeTime_eq]
  refine ⟨hGc, ?_⟩
  show qLast (nodeLen s) (nodePre s) ∈ tPre _ _ _ _ ω
  rw [tPre_of_mem hGc]
  refine ⟨by rw [hτ]; exact (treeTime_pos n).le, fun u hu => ?_⟩
  show nodeAlpha x₀ h44 hκ hκ4 hb h s (nodeLen s) (nodePre s) ω u ∉ _
  rw [nodeAlpha_of_le _ _ _ _ _ le_rfl, hτ] at *
  have hu' : u ∈ Icc 0 (terminal s : ℝ) := hu
  rw [← prefixTrace_node_eq_qPathF h44 hκ hκ4 c (qField x₀ κ h) hgω (hpω s) hu']
  change driverTree E n ω u ∉ cfHullQ (r : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω)
  rw [hcg.2]
  rintro ⟨p, hpK, hpe⟩
  rw [hK] at hpK
  have hpH : p ∈ H := hpK.1
  have hzH : negInv p ∈ H := negInv_mem_H hpH
  rw [hpe] at hzH
  rcases hu.1.eq_or_lt with hu0 | hu0
  · rw [← hu0, (hiω n).1] at hzH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
  · have hp : capacityTree (driverTree E) n ω u = p := by
      show -(driverTree E n ω u)⁻¹ = p
      rw [← hpe]
      simp [negInv]
    obtain ⟨v', -, hv', -⟩ := h57ω n (u / 2) u (by linarith) (by linarith) hu.2
    rw [hp] at hv'
    have hno : ∀ w ≤ (r : ℝ).toNNReal, γ ω w ≠ p := by
      intro w hw'
      rcases (zero_le : (0 : ℝ≥0) ≤ w).eq_or_lt with hw0' | hwpos
      · rw [← hw0', hγω.1]
        intro h0
        rw [← h0] at hpH
        exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hpH)
      have hwr : (w : ℝ) ≤ r := by
        have h1 := NNReal.coe_le_coe.2 hw'
        rw [Real.coe_toNNReal'] at h1
        have h2 : (0 : ℝ) < w := NNReal.coe_pos.2 hwpos
        rcases le_total (r : ℝ) 0 with hr0 | hr0
        · rw [max_eq_right hr0] at h1; linarith
        · rwa [max_eq_left hr0] at h1
      rcases hu.2.lt_or_eq with hlt | heq
      · obtain ⟨v, -, hvz, hvne⟩ := h57ω n u (treeTime n) hu0 hlt le_rfl
        have hTv := traceFirstVisit_le hvz
        have hwv : w ≤ v := by
          have h1 : (r : ℝ) < traceFirstVisit (γ ω) _ := hact
          have h2 : (w : ℝ) < traceFirstVisit (γ ω) (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω) :=
            lt_of_le_of_lt hwr h1
          exact (NNReal.coe_lt_coe.1 (lt_of_lt_of_le h2 (NNReal.coe_le_coe.2 hTv))).le
        rw [← hp]
        exact hvne w hwv
      · have h1 : (r : ℝ) < traceFirstVisit (γ ω) _ := hact
        have h2 : w < traceFirstVisit (γ ω) (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω) :=
          NNReal.coe_lt_coe.1 (lt_of_le_of_lt hwr h1)
        rw [← hp, heq]
        exact apply_ne_of_lt_traceFirstVisit h2
    exact false_of_visit_mem_fwdHull hw hw0 hγω hpH hpK hv' hno

end Node

end InteractingSLE.Sec7.StripMarks
