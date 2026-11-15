/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MqIface
import InteractingSLE.Spec.Supplement.SB2XzTW
import InteractingSLE.Spec.Supplement.SB2XzArcs
import InteractingSLE.Spec.Supplement.SB2YbTop

/-!
# SB2(2)'s conditional half and combined target over the bundle without `tail` (decision D36)

Packet PROVE-T14-SB2LIFT (round 31; decision D36, PROVE-T14-ASSEMBLE7's mismatch M1). LCMEAN's conditional half
`Mq.SB2LowerRelStageCond3Statement` and combined theorem `Mq.sb2LowerTailLiftExStatement_of_relDriverT_cond3` range
over the bundle `ClauseT`, whose field `tail` is false (SB2LIFT §R29.1). This file restates them over the corrected
bundle `Mn.ClauseTW ∧ Mn.StageFactsAS` (`Lk.RelDriverAtTW`, `SB2XzTW`):

* the conditional half `RelStageCondW` / **`SB2LowerRelStageCondWStatement`** (CONDFIN's target, D36 (3)) and its
  kernel form `RelStageKernelW` / **`SB2LowerRelKernelWStatement`**;
* **`sb2LowerRelStageCondWStatement_of_kernelW`** (Theorems 1.2–1.3): the kernel form gives the conditional half;
* **`sb2LowerTailLiftExStatement_of_relDriverTW_condW`**: the hypothesis `hTL` of `Wire.theorem14Statement_assembled7`
  from `Lk.SB2LowerRelDriverStatementTW` and the conditional half (and Theorems 1.2–1.3), the connector form of
  `tail` coming from the start data (`Mn.tailArc_of_bundle`, `Lk.sb2LowerArcsIci`) and the range identity from the
  connector-form copies `range_eq_physSet_of_bundlesW` / `range_eq_physSet_of_topVW` (`SB2YbAE`, `SB2YbTop`);
* **`sb2LowerLaunchLiftStatement_of_relDriverTW_condW`**: the same for `Lh.SB2LowerLaunchLiftStatement`.

The proofs are LCMEAN's, with the bundle replaced. R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mq

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn
open LuM (trOf)

section Cond

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ)
  (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens)

/-- **The conditional half at one launch, over families carrying the corrected bundle** (`RelStageCond3` with
`Mn.ClauseTW ∧ Mn.StageFactsAS` in place of `RelDataClause3`; decision D36). -/
def RelStageCondW : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    Mn.ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL → Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
    ∀ j, ∀ᵐ ω₁ ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ (c₁ : Chart) (θ : ℝ),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω₁)
          (j + 1)).2.2.2.1 j = some (c₁, θ) →
        ∃ (b'' : ℝ → ℝ) (J'' : Finset ℝ) (h'' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b'' J'' ∧
          (∀ ω, IsChartTransport c₁ 1 0 (chiC κ) (affField m one_pos (h' ω)) (h'' ω)) ∧
          IsFlowLineDriver κ b'' J'' θ
            (condExpKernel (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
              (pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) ω₁)
            h'' (fun t ω => (EL j ω).1 t) (fun ω => (EL j ω).2)

/-- **The kernel form at one launch, over families carrying the corrected bundle** (`RelStageKernel3` with
`Mn.ClauseTW ∧ Mn.StageFactsAS`): per stage, a conditional flow line given a σ-algebra containing the relative
past. -/
def RelStageKernelW : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    Mn.ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL → Mn.StageFactsAS κ b jumps P E u l k ω₀ c b' J' m EL →
    ∀ j : ℕ, ∃ (𝒢' : {m' : MeasurableSpace Ω // m' ≤ mΩ}) (F' : Set Ω) (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ),
      pastSigma κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j ≤
        LocalSets.aeSigma 𝒢'.1 (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) ∧
      (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
          (j + 1)).2.2.2.1 j ≠ none → ω ∈ F') ∧
      SB.IsCondFlowLineDriverOn κ (-(Real.pi / 2)) 𝒢'.1
        (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀) F'
        (fun ω => affField m one_pos (h' ω))
        (Cond.runChart κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) bc jc
        (fun t ω => (EL j ω).1 t) (fun ω => (EL j ω).2)

end Cond

/-- **PROVE-SB2-CONDFIN's target (D36 (3)): SB2(2)'s conditional half over families carrying the corrected bundle
`Mn.ClauseTW ∧ Mn.StageFactsAS`.** -/
def SB2LowerRelStageCondWStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageCondW κ b jumps P E u l k ω₀ c b' J' h'

/-- **The kernel form of the conditional half over the corrected bundle.** -/
def SB2LowerRelKernelWStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageKernelW κ b jumps P E u l k ω₀ c b' J' h'

/-- **The kernel form gives the conditional half** (Theorems 1.2–1.3; LCOND's generic code match
`Lcd.ae_codeMatch_of_condFlowLine_data` and staged induction `Lcd.stageOK_all_of_codeMatch`). -/
theorem sb2LowerRelStageCondWStatement_of_kernelW (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hker : SB2LowerRelKernelWStatement.{u}) :
    SB2LowerRelStageCondWStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hker κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl hsf j
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hG'' := hG'.affine_finset (m := m) one_pos
  refine Lcd.stageOK_all_of_codeMatch h12p h13 hκ hb'' hG'' (-(Real.pi / 2))
    (fun _ _ _ _ hl => Lv.launch_angle_boundaryWalk hl) hELm hELr (fun j β Y hW => ?_) j
  obtain ⟨𝒢', F', bc, jc, hpast, hcov, hcfl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl hsf j
  exact Lcd.ae_codeMatch_of_condFlowLine_data h12p h13 hκ (-(Real.pi / 2)) hb'' hELm hELr 𝒢' hpast hcov hW hcfl

/-- **The hypothesis `hTL` of `Wire.theorem14Statement_assembled7`** (D36): SB2(2)'s erasure identity for one
relative walk from the corrected data `Lk.SB2LowerRelDriverStatementTW` and the conditional half over the corrected
bundle (`sb2LowerTailLiftExStatement_of_relDriverT_cond3` with `ClauseTW`; the connector form of `tail` from the start
data, `Mn.tailArc_of_bundle`). -/
theorem sb2LowerTailLiftExStatement_of_relDriverTW_condW (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hD : SB2LowerRelDriverStatementTW.{u}) (hcond : SB2LowerRelStageCondWStatement.{u}) :
    SB2LowerTailLiftExStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hcond κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    Lk.sb2LowerArcsIci h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ h₀ hH₀ hA₀ hX₀ hI₀ hC₀ hcond₀ hZ₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hELm, hELr, hae, hSF⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  have hst := hcond₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hae hSF
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hpast : ∀ j, Measurable (pastMap κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) :=
    fun j => measurable_pastMap runMeasStatement hb'' (relLowerSpec b' J' m) (k := j) (fun i _ => hELm i)
      (fun i _ => hELr i) j le_rfl
  have hS : IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL := by
    refine ⟨hELm, fun j => ?_, fun j => Eventually.of_forall fun ω hne hpos c₀ hc₀ =>
      (hELr j ω).2.2.2 hne hpos c₀ hc₀, hst⟩
    rw [pastSigma_eq_comap]
    exact (hpast j).comap_le
  refine ⟨EL, hS, stagedPiecesRegular_of_regular h13 hκ hb'' hS hELr, ?_⟩
  filter_upwards [hae, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hA₀ c θ hlaunch b' J' h' hb' hT' hG',
    hX₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm, hZ₀ c θ hlaunch b' J' h' hb' hT' hG']
    with ω hω hHω hAω hXω hIω hCω hZω
  intro β₀ hβ hβ0 hβr
  obtain ⟨tL, γ, hγ⟩ := hCω β₀ hβ hβ0 hβr
  obtain ⟨ι, hι, hlim, hray, hS'⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have htail := Mn.tailArc_of_bundle hβ hβr hγ.1 hhead hZω hP₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hS'
  have hC : CurveInputsW κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) β₀ γ tL :=
    ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hhead, htail, hray⟩
  refine isTailLiftOf_iff.2 ⟨tL, γ, hγ, ?_⟩
  rcases hS' with ⟨N, hR, hS'⟩ | ⟨hP, htop⟩
  · have hDc : LiftCurveData β₀ γ tL (realMax (upperPrefix κ b jumps E u l k ω₀)) ι :=
      ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
        fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
    exact range_eq_physSet_of_bundlesW hι hC hR (fun j => hELr j ω) hP₁ hW₁ (fun j => (hn j).1)
      (fun j => (hn j).2.1) (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hβ hγ.2.1 hβ0 hDc hS'
  · exact range_eq_physSet_of_topVW hι hC hP htop (hn _).2.1

/-- **SB2(2)'s combined target (R104a) from the corrected data and the conditional half over the corrected bundle**
(D36; and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_relDriverTW_condW (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hD : SB2LowerRelDriverStatementTW.{u}) (hcond : SB2LowerRelStageCondWStatement.{u}) :
    Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_liftEx h12 h13 h12₀ h13₀
    (sb2LowerTailLiftExStatement_of_relDriverTW_condW h12 h13 h12₀ h13₀ hD hcond)

end InteractingSLE.Theorem14.SB.Mq
