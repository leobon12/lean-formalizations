/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59SchedHist
import InteractingSLE.Spec.Sec5.Prop513AsmWire

/-!
# Proposition 5.13's input (B) discharged: the canonical extreme-angle schedules of the chart-Q field

Packet PROVE-PROP59-SCHED. PROVE-PROP513-ASM's strongest form of Proposition 5.13
(`Prop513Asm.prop513_comap_of_histExp_current`) took, as input (B), a family `E` of staged histories of the target field
`targetField (h)` (chart Q) indexed by the fixed extreme-angle schedules, with the R51 regularity (`hE`, `hR`). The
earlier constructions of such families used Theorems 1.2–1.3 (R48-forbidden here). This file supplies it R48-safely:

* **`targetSched`**: the canonical family — the Borel schedule recursion (`Prop59Sched.schedDrivers`) of the target
  field for the source word `sourceWord` (the chart-Q word of the Figure 5.1 data, extreme heights by R56);
* **`isStagedHistory_targetSched`**, **`stagedPiecesRegular_targetSched`**, **`exists_target_stagedHistories`**:
  input (B) from the strip GFF hypothesis alone (and `h44`);
* **`prop513_comap_of_sched`**: Proposition 5.13 (`comap h`-measurable version) with input (B) eliminated: its only
  inputs besides the setting and the three binders of the Theorem 1.2 wiring (`h47`, `hA2`, `hA2'`) are Lemma 5.7's
  first exit `hFH` and Proposition 5.9's experiments with their stage laws ((C), (D) of PROVE-PROP513-ASM §3), now
  stated for the canonical family.

R48: `h44` is `theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2'` (R74); nothing takes Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

universe u v

namespace InteractingSLE.Sec5.Prop59Sched

open QuantumZipper LQGMetric Sec4 Prop59Stage Prop59System Prop513Schedule Prop513TreeExtract Prop513Target
  Prop513Wire Prop513Asm Restart Exist Exist.Staged Exist.StagedLaw StripRevVisit

/-- **The canonical extreme-angle staged histories of the chart-Q target field** (Proposition 5.13, input (B)). -/
def targetSched (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b') {Ω : Type*} (h : Ω → DistOn upperHalfPlaneOpens) :
    Schedule → ℕ → Ω → Driver :=
  fun s => schedDrivers h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) s
    (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω))

section Target

variable (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

theorem isStagedHistory_targetSched (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (s : Schedule) :
    IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s)
      (targetSched h44 (x₀ := x₀) hκ hκ4 hb h s) :=
  isStagedHistory_schedDrivers h44 hκ hκ4 _ (sourceWord_extreme hκ hb) (sourceWord_gff hκ hb hG) s

theorem stagedPiecesRegular_targetSched (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (s : Schedule) :
    StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (targetSched h44 (x₀ := x₀) hκ hκ4 hb h s) :=
  stagedPiecesRegular_schedDrivers h44 hκ hκ4 _ (sourceWord_extreme hκ hb) (sourceWord_gff hκ hb hG) s

include h44 hκ4 in
/-- **Input (B) of Proposition 5.13** (PROVE-PROP513-ASM §3): the extreme-angle schedules of the target field realized
on `Ω` as staged histories with the R51 regularity, from the strip GFF hypothesis and `h44` alone. -/
theorem exists_target_stagedHistories (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀}) :
    ∃ E : Schedule → ℕ → Ω → Driver,
      (∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
        (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s)) ∧
      ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
        (scheduleSpec s) (E s) :=
  ⟨targetSched h44 (x₀ := x₀) hκ hκ4 hb h, isStagedHistory_targetSched h44 hκ hκ4 hb hG,
    stagedPiecesRegular_targetSched h44 hκ hκ4 hb hG⟩

end Target

/-- **Proposition 5.13 (`comap h`-measurable version) with input (B) eliminated.** PROVE-PROP513-ASM's
`prop513_comap_of_histExp_current` with the staged histories taken to be the canonical family `targetSched`
(`h44 = theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2'`, R74). Remaining inputs: `hFH` (Lemma 5.7's first
exit) and Proposition 5.9's experiments `X₀`, `X` with their stage laws `hL₀`, `hL`. -/
theorem prop513_comap_of_sched
    (h47 : Prop411Q.Lemma47QHitStatement.{u})
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (hFH : StagedPrefixFirstHitStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {Ωa : Type v} [MeasurableSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : HistExp κ P Pa (rootTgt W (extremeAngleTreeNode (capacityTree (driverTree
      (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb h))) treeTime))
      fun _ => univ)
    (hL₀ : ∀ r : ℚ, 0 < r → Prop59StageLawStatement κ (P.prod Pa) (X₀.rhoL r) (X₀.rhoR r) (X₀.system r))
    (X : ∀ n, HistExp κ P Pa
      (nodeTgt W (extremeAngleTreeDescendants (capacityTree (driverTree
        (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb h))) treeTime
        descendantIndex n))
      (nodeAct γ (extremeAngleTreeNode (capacityTree (driverTree
        (targetSched (theorem12ParamCond44Statement_of_lemma47Q_of_A2 h47 hA2 hA2') (x₀ := x₀) hκ hκ4 hb h)))
        treeTime n)))
    (hL : ∀ n, ∀ r : ℚ, 0 < r →
      Prop59StageLawStatement κ (P.prod Pa) ((X n).rhoL r) ((X n).rhoR r) ((X n).system r)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap h inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_comap_of_histExp_current h47 hA2 hA2' hFH hκ hκ4 hb hG hcf htr
    (isStagedHistory_targetSched _ hκ hκ4 hb hG) (stagedPiecesRegular_targetSched _ hκ hκ4 hb hG) X₀ hL₀ X hL

end InteractingSLE.Sec5.Prop59Sched
