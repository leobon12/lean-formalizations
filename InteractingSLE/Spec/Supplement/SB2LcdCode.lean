/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkSplit
import InteractingSLE.Spec.Supplement.SB2KcChart
import InteractingSLE.Spec.Supplement.SB2CondCode
import InteractingSLE.Spec.Supplement.SBLvStage

/-!
# SB2(2)'s conditional half: the staged induction under the retained kernel, and the pathwise identification

Packet PROVE-T14-SB2LCOND. The conditional half `Lk.SB2LowerRelStageCondStatement` asks, at a later upper launch `k`
and for every measurable, everywhere regular family `EL` whose relative lower walk carries the actual tail's lift,
that every stage of `EL` is a conditional flow line of the conditional field `X = affField m h'` under
`Q = condExpKernel P 𝒢 ω₀` given its own relative past (`StageOK` under `Q`).

The family `EL` is chosen after `ω₀`, so its relative past cannot be handled by the tower identity for nested kernels
(PROVE-T14-SB2LIFT round 4). This file works under `Q` itself:

* `Q` is a probability measure on the same standard Borel space and `X` is under `Q` the GFF of the affine data
  (SB2(2)'s launch clause, `IsGFFWithBoundaryData.affine_finset`), so the generic staged induction
  `Exist.StagedLaw.stageLaw` applies under `Q`: once the stages before `j` are conditional flow lines, the field read in
  the chart of stage `j` is, given the relative past, the GFF of a past-measurable word (`IsStageWitness`);
* given that witness, the stage is a conditional flow line exactly when its driver matches, `Q`-almost surely on its
  launch event, the canonical driver code of (stage word, stage chart field) (Theorem 1.2's field-determining graph;
  `Cond.isFlowLineDriver_of_driverCodeMatch_univ` under each conditional law): **`stageOK_of_codeMatch`**;
* hence **`stageOK_all_of_codeMatch`** (strong induction over the stages) and the reduction
  **`sb2LowerRelStageCondStatement_of_code`**: the conditional half follows from Theorems 1.2–1.3 and the named
  pathwise identification **`SB2LowerRelCodeStatement`** (supplement p. 633: "Integrated uniqueness and the
  field-determining graphs identify the actual relative ordinary flows").

The identification is a `Q`-almost-sure PATHWISE statement. A pathwise `P`-almost-sure statement about the actual walks
transfers to `Q` for `P`-almost every `ω₀` with no tower identity (`Aux122Disint.ae_ae_condExpKernel`), which is why the
reduction removes the obstruction recorded by PROVE-T14-SB2LIFT.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lcd

open Restart Exist Exist.Staged Exist.StagedLaw

/-! ### A stage is a conditional flow line once its driver matches the canonical code -/

section Generic

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **One stage from its code match.** Let `(β, Y)` witness the conditional law at the launch of stage `k` (the field
read in the run chart is, given the retained past, the GFF of the past-measurable word `β`). If almost surely on the
launch event the driver of stage `k` matches the canonical driver code of `(β, Y)` at the stage's angle `θ₀`, then
stage `k` is a conditional flow line given its retained past (`StageOK`). -/
theorem stageOK_of_codeMatch (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) (hκ : 0 < κ)
    (θ₀ : ℝ) {k : ℕ}
    (hθ : ∀ ω (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) → θ = θ₀)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ) (hhm : Measurable h)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ b jumps P h spec E k β Y)
    (hmatch : ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2) :
    StageOK κ b jumps P h spec E k := by
  have hβm : Measurable[pastSigma κ b jumps spec E k] β := hW.1
  filter_upwards [Lv.ae_condChartField_of_stageWitness k hreg h𝒢 hW hhm, hW.2.2.1,
    Cond.ae_ae_runChart_eq (P := P) k (fun j _ => hreg j) h𝒢,
    CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps) spec (fun j _ => hreg j) h𝒢
      le_rfl,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hW.2.2.1,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hmatch,
    Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢 hβm]
    with ω₀ hG₀ hp₀ hc₀ hrun₀ hpk₀ hmk₀ hβ₀
  intro c θ hcθ
  have hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k ≠ none := by
    rw [hcθ]; exact Option.some_ne_none _
  obtain rfl := hθ ω₀ c θ hcθ
  have hc : c = Cond.runChart κ b jumps spec E k ω₀ := (eq_launch_of_launches spec _ hcθ).2.2
  subst hc
  obtain ⟨h', hT, hgff⟩ := hG₀ hl
  obtain ⟨hconf, -, -⟩ := hp₀ hl
  refine ⟨(β ω₀).fn, (β ω₀).jumps, h', (β ω₀).isPiecewiseConstantBoundaryData, hT, ?_⟩
  refine Cond.isFlowLineDriver_of_driverCodeMatch_univ h12p hκ θ h13 (β ω₀) hgff
    (fun t => (measurable_pi_apply t).comp (measurable_fst.comp (hEm k))) (measurable_snd.comp (hEm k))
    (fun ω => (hreg k ω).1) ?_
  filter_upwards [hc₀, hrun₀, hpk₀, hmk₀, hβ₀] with ω hcω hrunω hpω hmω hβω
  have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none := by
    rw [launches_run_succ_of_run_eq spec hrunω]
    exact hl
  obtain ⟨-, -, hYω⟩ := hpω hlω
  have hYω' : IsChartTransport (Cond.runChart κ b jumps spec E k ω₀) 1 0 (chiC κ) (h ω) (Y ω) := by
    rw [← hcω]
    exact hYω
  have hY : Y ω = h' ω := IsChartTransport.unique hconf hYω' (hT ω)
  have hm := hmω hlω
  rw [hβω, hY] at hm
  exact hm

/-- **Every stage from the code matches** (strong induction with the generic staged law
`Exist.StagedLaw.stageLaw`): if the drivers are measurable and regular at every sample, every launch of instruction
`k` has the angle `θ₀`, and at every stage the driver matches the canonical code of EVERY witness of the stage's
conditional law, then every stage is a conditional flow line given its retained past. -/
theorem stageOK_all_of_codeMatch (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) (hκ : 0 < κ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps) (θ₀ : ℝ)
    (hθ : ∀ k ω (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) → θ = θ₀)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (hmatch : ∀ k (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ b jumps P h spec E k β Y →
      ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        IsDriverCodeMatch (driverCode h12p hκ θ₀ (β ω, Y ω)) (fun t => (E k ω).1 t) (E k ω).2) :
    ∀ k, StageOK κ b jumps P h spec E k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨β, Y, hW⟩ := stageLaw (GW1W.isStopLaw_stopWord.{u} hκ) runMeasStatement hκ hb hh k
      (fun j _ => hEm j) (fun j _ => hreg j) ih
    have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := by
      rw [pastSigma_eq_comap]
      exact (measurable_pastMap runMeasStatement hb spec (fun j _ => hEm j) (fun j _ => hreg j) k
        le_rfl).comap_le
    exact stageOK_of_codeMatch h12p h13 hκ θ₀ (hθ k) hEm hreg h𝒢 hh.1 hW (hmatch k β Y hW)

end Generic

/-! ### SB2(2): the conditional half from the pathwise identification -/

section SB2

open Supp9B Lx Lu Leaf FlowDilate Sec4

/-- **The pathwise identification at one launch** (supplement p. 633: "Integrated uniqueness and the field-determining
graphs identify the actual relative ordinary flows"): for `m = −e_R` and every measurable family `EL` of drivers,
regular at every sample, whose relative walk carries the actual tail's lift almost surely under the retained kernel
`Q`, at every stage `j` and for every witness `(β, Y)` of the stage's conditional law (the field read in the run chart
of stage `j` is, given the relative past, the GFF of the past-measurable word `β`): `Q`-almost surely on the launch
event of stage `j`, the driver of stage `j` matches the canonical angle-`(−π/2)` driver code of `(β, Y)`. -/
def RelStageCode (h12p : Theorem12ParamStatement.{u}) (κ : ℝ) (hκ : 0 < κ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)) →
    ∀ (j : ℕ) (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
        (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
        (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL j β Y →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
          (j + 1)).2.2.2.1 j ≠ none →
        IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL j ω).1 t) (EL j ω).2

/-- **Named input: SB2(2)'s pathwise identification at the later launches** (per stage). -/
def SB2LowerRelCodeStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → ∀ hκ : 0 < κ, RelStageCode h12p κ hκ b jumps P E u l k ω₀ c b' J' h'

/-- **SB2(2)'s conditional half from the pathwise identification** (and Theorems 1.2–1.3): under the retained kernel
the conditional field is the GFF of the affine data, so the staged induction runs under that kernel. -/
theorem sb2LowerRelStageCondStatement_of_code (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hcode : SB2LowerRelCodeStatement.{u} h12p) :
    Lk.SB2LowerRelStageCondStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hcode κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hlift j
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hG'' := hG'.affine_finset (m := m) one_pos
  exact stageOK_all_of_codeMatch h12p h13 hκ hb'' hG'' (-(Real.pi / 2))
    (fun _ _ _ _ hl => Lv.launch_angle_boundaryWalk hl) hELm hELr
    (fun j β Y hW => h₀ c θ hlaunch b' J' h' hb' hT' hG' hk hκ m hm EL hELm hELr hlift j β Y hW) j

/-- **SB2(2)'s combined target (R104a)** from the geometric half and the pathwise identification. -/
theorem sb2LowerLaunchLiftStatement_of_code (h12 : Theorem12Statement.{u}) (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hgeo : Lk.SB2LowerRelWalkStatement.{u}) (hcode : SB2LowerRelCodeStatement.{u} h12p) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  Lk.sb2LowerLaunchLiftStatement_of_split h12 h13 h12₀ h13₀ hgeo
    (sb2LowerRelStageCondStatement_of_code h12p h13 hcode)

end SB2

end InteractingSLE.Theorem14.SB.Lcd
