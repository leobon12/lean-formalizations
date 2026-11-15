/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.FrameQFirstHit
import InteractingSLE.Spec.Sec5.Prop513AsmWire

/-!
# The Q restart law in the Figure 5.1 consumers

The remaining multi-piece restart theorem is stated in the centered Q frame
as `QScheduleFirstHitStatement`. The E-to-Q covariance, counterflow identity,
and return to physical first contacts are proved, so this input supplies
`StripRevVisit.StagedPrefixFirstHitStatement` and Proposition 5.13's `hFH`.
It is an explicit unproved input, not a proof of the multi-piece law.

R48: only the restricted Section 4.2 input is used, derived from Lemma 4.7
and Part A in the final assembly. No full Theorem 1.2/1.3 input is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real NNReal ENNReal

universe u v

namespace InteractingSLE.Sec5.FrameQ

open QuantumZipper LQGMetric Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire
open Restart Exist Exist.Staged Exist.StagedLaw StripRevVisit Prop513Asm Prop59Stage

/-- The remaining general restart law, restricted to the source's finite
extreme-angle schedules, in the centered Q frame. In particular this includes
prefixes after several switches; the one-angle Lemma 4.7 does not supply it. -/
def QScheduleFirstHitStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ c : BoundaryWord, ExtremeHeights κ c →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
    IsGFFWithBoundaryData P h c.fn c.jumps →
  ∀ (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (γ : Ω → ℝ≥0 → ℂ),
    IsCenteredCounterflowDriver κ P h W ζ →
    (∀ᵐ ω ∂P, ζ ω = ⊤) →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω)) →
  ∀ E : Schedule → ℕ → Ω → Driver,
    (∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s)) →
    (∀ s, StagedPiecesRegular κ c.fn c.jumps P (scheduleSpec s) (E s)) →
    PrefixRegular P E →
  ∀ (n : ℕ) (σ : ℚ), 0 < (σ : ℝ) → (σ : ℝ) < treeTime n →
    ∀ᵐ ω ∂P, Prop411Q.IsFirstHitQ (driverTree E n ω) (fun t => γ ω t.toNNReal) σ

/-- The centered Q schedule law supplies the exact physical first-exit input.
All changes of frame, field covariance and original counterflow interiority
are discharged; the general multi-piece Q law remains explicit. -/
theorem stagedPrefixFirstHitStatement_of_qScheduleFirstHit
    (hA : PartAInputsSixteenDivOfClearance) (hQ : QScheduleFirstHitStatement.{u}) :
    StagedPrefixFirstHitStatement.{u} := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω mΩ hB P hP h hG W ζ γ hcf htr E hE hR
    _hAvail hreg _hdet n σ hσ hσT
  have hq : 0 < Real.exp (π * x₀) := Real.exp_pos _
  have hcfQ := (isStripCounterflowDriver_iff_centered hκ hq).1 hcf
  have hζ := fig51_counterflow_lifetime hκ hb hG hcf
  have htrTop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [htr, hζ] with ω hω hζω
    rwa [hζω] at hω
  have hfirst := hQ κ hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (sourceWord_extreme hκ hb)
    P _ (sourceWord_gff hκ hb hG) W ζ γ hcfQ hζ htrTop E hE hR hreg n σ hσ hσT
  have hH := fig51_trace_mem_H_of_partA_of_clearance hA hκ hκ4 hb hG hcf
  filter_upwards [hfirst, hreg, htrTop, hH] with ω hf hr hγ hHω
  exact firstHitPoint_of_isFirstHitQ hq hσ hσT.le (hr n).2.2.1 (hr n).2.2.2
    hγ.1 (hHω.2 _ hγ) hf

/-- The same input in the A.2 form used by Proposition 5.13's current wiring. -/
theorem stagedPrefixFirstHitStatement_of_qScheduleFirstHit_A2
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hQ : QScheduleFirstHitStatement.{u}) : StagedPrefixFirstHitStatement.{u} :=
  stagedPrefixFirstHitStatement_of_qScheduleFirstHit
    (partAInputsSixteenDivOfClearance_of_A2 hA2 hA2') hQ

/-- Proposition 5.13 with its physical `hFH` discharged by the centered Q law.
The candidate experiments and their stage laws are the existing independent
Proposition 5.9 inputs; their statements are unchanged. -/
theorem prop513_comap_of_histExp_qSchedule
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hQ : QScheduleFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
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
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa)
      (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ,
      (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_comap_of_histExp_current h47 hA2 hA2'
    (stagedPrefixFirstHitStatement_of_qScheduleFirstHit_A2 hA2 hA2' hQ)
    hκ hκ4 hb hG hcf htr hE hR X₀ hL₀ X hL

end InteractingSLE.Sec5.FrameQ
