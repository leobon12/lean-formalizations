/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513WireCounterflow
import InteractingSLE.Spec.Sec5.Prop513WireReverse
import InteractingSLE.Spec.Sec5.Prop513TargetRecovery

/-! # Proposition 5.13 with Part A and the physical reverse-visit law

The barrier-seed route supplies no-return and interiority. Finite-schedule
regularity and the deterministic E/Q chart conversion supply the geometric
part of Lemma 5.7. Only its physical reverse-visit law and Proposition 5.9's
two tip assertions remain alongside the restricted Section 4.2 input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal
universe u

namespace InteractingSLE.Sec5.Prop513Wire
open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- Proposition 5.13 from the restricted Section 4.2 result, Part A,
the physical reverse-visit law, and the two Proposition 5.9 tip assertions.
Taking `𝒢 = σ(h)` gives determination by the original field. -/
theorem prop513_path_of_partA_reverseVisit
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    (htip : ∀ n, Prop59Tips.TipUnboundedStatement P W γ
      (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)
      (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
    (htip0 : Prop59Tips.Tip0UnboundedStatement P W
      (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  let c := sourceWord (x₀ := x₀) hκ hb
  have hc : ExtremeHeights κ c := sourceWord_extreme hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  have hmQ := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hh𝒢
  obtain ⟨ξ, hξm, hξc, hroot, he⟩ := exists_measurable_extreme_tree_of_stagedPiecesRegular
    h44 hκ hκ4 c hc hhQ hE hR hmQ
  have hreg := fig51_trace_mem_H_of_partA hA hκ hκ4 hb hG hcf
  have hζ := hreg.mono fun _ hω => hω.1
  have htrTop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [htr, hζ] with ω hω hζω
    rwa [hζω] at hω
  have hH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H := by
    filter_upwards [hreg, htrTop] with ω hω hγω
    exact hω.2 _ hγω
  have heRaw := ae_driverTree_eq
    (prefixTraceRegularity_of_stagedPiecesRegular h44 hκ hκ4 c hc hhQ hE hR) he
  have h57 := targetLemma57_of_stripReverseVisit (Real.exp_pos _)
    (htrTop.mono fun _ hω => hω.1) hH
    (ae_driverTree_interior h44 hκ hκ4 c hc hhQ hE hR) hVisit
  have hgeom := geometry_of_targetLemma57 h57 hH heRaw hroot
  obtain ⟨L, hLm, hLe⟩ := @exists_measurable_capacity_cones Ω mΩ P 𝒢 ξ hξm hξc
    treeTime descendantIndex treeTime_pos treeTime_mono hroot (hgeom.mono fun _ hω => hω.1)
  obtain ⟨b₀, J₀, _, _, hfl, _⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hdriver : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hC.1.ae_isIntegratedSLEPath, hζ, htrTop] with ω hp hζω hγω
    have hw := hp.2.2.2.1
    rw [hζω] at hw
    exact ⟨continuousOn_univ.1 (by simpa only [ENNReal.coe_lt_top, ofPred_true] using hw), hp.1, hγω⟩
  have hTip := fun n => Prop59Tips.ae_tip_of_unbounded hdriver
    (fun _ => rfl : ∀ ω, extremeAngleTreeCone (capacityTree (driverTree E)) treeTime descendantIndex n ω =
      closure (insert (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω)
        (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n ω))) (htip n)
  have hTip0 := Prop59Tips.ae_tip0_of_unbounded hdriver htip0
  have hk : 4 < 16 / κ := (lt_div_iff₀ hκ).2 (by linarith only [hκ4])
  refine @path_of_tips_ae_cones (16 / κ) _ _ _ _ _ _ Ω mΩ P _ 𝓕 W VL VR B ζ
    hk hC.1 hζ 𝒢 γ (extremeAngleTreeNode (capacityTree ξ) treeTime)
    (extremeAngleTreeDescendants (capacityTree ξ) treeTime descendantIndex) L
    (measurable_extremeAngleTreeNode (measurable_capacityTree hξm) treeTime) hLm
    hLe htrTop hH (hgeom.mono fun _ hω => hω.2.1) (hgeom.mono fun _ hω => hω.2.2) ?_ ?_
  · intro n q hq
    filter_upwards [hTip n q hq, heRaw, hLe] with ω ht heω hlω hqT
    have hn := node_cone_eq heω
    rw [hlω n, hn.2 n]
    apply ht
    rwa [← hn.1 n]
  · intro q hq
    filter_upwards [hTip0 q hq, heRaw] with ω ht heω
    have hn := (node_cone_eq heω).1
    have hr : (fun n => extremeAngleTreeNode (capacityTree ξ) treeTime n ω) =
        fun n => extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω := funext hn
    rwa [hr]

end InteractingSLE.Sec5.Prop513Wire
