/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JiData2
import InteractingSLE.Spec.Supplement.SB2LcdKernel
import InteractingSLE.Spec.Supplement.SB2LcdCode
import InteractingSLE.Spec.Supplement.SB2LjRule
import InteractingSLE.Spec.Supplement.SB2FinConfig
import InteractingSLE.Spec.Supplement.SB2LkEx
import InteractingSLE.Spec.Supplement.SB2LqRange

/-!
# SB2(2)'s conditional half over pathwise-linked relative families (ruling R116)

Packet PROVE-SB2-LCMEAN, round 10. Ruling R116 (option A): the conditional half ranges over relative driver families
carrying LIFTSET's v2 bundle `Lk.RelDataClause2` instead of the set-level tail lift; the per-stage correspondence is
PROVE-T14-SB2LIFT's to prove, and this packet does the probabilistic assembly against it.

* **The per-stage correspondence (PROVE-T14-SB2LIFT's named statement)**:
  - `walkStageChart`: B's run chart before instruction `ℓ` (the actual lower walk);
  - `stageRelChart cℓ c c₁ m`: the relative chart read in B's stage coordinates — B's inverse stage chart, then the
    upper launch chart `c` shifted by `m` (the relative frame), then the relative run chart `c₁` (lift: chain rule);
  - `stageRetained cℓ X`: the retained set in B's stage coordinates (the inverse stage chart lands in `fill X`);
  - **`StageChainAt`**: at one sample, for every relative stage `j` that launches with chart `c₁`, the matched actual
    stage `ℓ = j + relOff …` launches; `stageRelChart` is a domain chart of the complement of the retained set
    (upper prefix with B's prefix before `ℓ`); and there are a head time `tL` and a lift `γ` of B's piece `ℓ` after
    `tL` through it whose relative chain (`SB2FinConfig.IsSB2RelChain`, at every `S₀` before the actual lifetime)
    has as driver and trace the relative driver and trace of `EL`'s stage `j`, with the relative lifetime the
    supremum of the relative capacities;
  - **`SB2LowerStageChainStatement`**: almost surely under the retained kernel, `StageChainAt` for every relative
    family carrying the v2 bundle.
* **The re-typed conditional half (this packet's target)**: `RelStageCond2` / **`SB2LowerRelStageCond2Statement`**
  (`Lk.RelStageCond` with the v2 bundle `Lk.RelDataClause2` in place of the set-level tail lift), its kernel form
  `RelStageKernel2` / **`SB2LowerRelKernel2Statement`**, and:
  - **`sb2LowerRelStageCond2Statement_of_kernel2`** (Theorems 1.2–1.3): the kernel form gives the conditional half
    (LCOND's generic code match and staged induction, unchanged);
  - **`sb2LowerLaunchLiftStatement_of_data2_cond2`**: SB2(2)'s combined target (R104a) from LIFTSET's v2 data
    statement and the re-typed conditional half (and Theorems 1.2–1.3).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mn

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk
open LuM (trOf)
open FinRel (IsSB2RelChain)

/-! ### The per-stage correspondence -/

section Corr

/-- B's run chart before instruction `ℓ` (the actual lower walk at one sample). -/
def walkStageChart (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → Drv) (ℓ : ℕ)
    (ω : Ω) : Chart :=
  stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)

/-- **The relative chart read in B's stage coordinates**: B's inverse stage chart `cℓ`, the upper launch chart `c`
shifted by `m` (the relative frame), and the relative run chart `c₁`; its lift is the chain-rule lift. -/
def stageRelChart (cℓ c c₁ : Chart) (m : ℝ) : Chart :=
  (fun w => c₁.1 (c.1 (cℓ.2.1 w) + (m : ℂ)), fun y => cℓ.1 (c.2.1 (c₁.2.1 y - (m : ℂ))),
    fun w => c₁.2.2 (c.1 (cℓ.2.1 w) + (m : ℂ)) + c.2.2 (cℓ.2.1 w) - cℓ.2.2 (cℓ.2.1 w))

/-- **The retained set in B's stage coordinates**: the points of `ℍ` whose image under the inverse stage chart lies
in `fill X` (`X` the physical retained set). -/
def stageRetained (cℓ : Chart) (X : Set ℂ) : Set ℂ := {v | v ∈ H ∧ cℓ.2.1 v ∈ fillH X}

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ) (EL : ℕ → Ω → Drv)

/-- **The per-stage correspondence at one sample** (PROVE-T14-SB2LIFT's, ruling R116): for every relative stage
`j` that launches with chart `c₁`, the matched actual stage `ℓ = j + relOff …` launches, the relative chart read in
B's stage-`ℓ` coordinates is a domain chart of the complement of the retained set (the upper prefix with B's prefix
before `ℓ`), and B's piece `ℓ` after a head time `tL` has a lift `γ` through it whose relative chain at every
`S₀` before the actual lifetime is driven by `EL`'s stage `j` (driver and trace), the relative lifetime being the
supremum of the relative capacities. -/
def StageChainAt (ω : Ω) : Prop :=
  ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ),
    (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
      (j + 1)).2.2.2.1 j = some (c₁, θ') →
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
      (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 1)).2.2.2.1
      (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ≠ none ∧
    IsDomainChart (H \ stageRetained (walkStageChart κ b jumps E
        (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω)
        (upperPrefix κ b jumps E u l k ω₀ ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))))
      (stageRelChart (walkStageChart κ b jumps E
        (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
          (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) c c₁ m) ∧
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
      (∀ s : ℝ≥0, Tendsto (stageRelChart (walkStageChart κ b jumps E
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) c c₁ m).2.1
        (𝓝[H] (γ s)) (𝓝 (trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) (tL + s)))) ∧
      (∀ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω).2 →
        IsSB2RelChain (stageRetained (walkStageChart κ b jumps E
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω)
            (upperPrefix κ b jumps E u l k ω₀ ∪
              SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
                (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
                  (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))))
          (stageRelChart (walkStageChart κ b jumps E
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) c c₁ m)
          (trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω))
          γ tL (S₀ : ℝ) (fun r : ℝ => (EL j ω).1 r.toNNReal) (fun r : ℝ => trOf (EL j ω) r.toNNReal)) ∧
      (EL j ω).2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL + S₀ : ℝ≥0) : ℝ≥0∞) <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω).2),
        ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ))

end Corr

/-- **Named input (PROVE-T14-SB2LIFT, ruling R116): SB2(2)'s per-stage correspondence.** In SB2(2)'s setting, for
every relative driver family carrying LIFTSET's v2 bundle, almost surely under the retained kernel the per-stage
correspondence `StageChainAt` holds. -/
def SB2LowerStageChainStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClause2 κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAt κ b jumps E u l k ω₀ c b' J' m EL ω

/-! ### The re-typed conditional half (R116) -/

section Cond

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ)
  (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens)

/-- **The conditional half at one launch, over families carrying the v2 bundle** (`Lk.RelStageCond` with
`Lk.RelDataClause2` in place of the set-level tail lift; ruling R116). -/
def RelStageCond2 : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClause2 κ b jumps P E u l k ω₀ c b' J' m EL →
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

/-- **The kernel form at one launch, over families carrying the v2 bundle** (`Lcd.RelStageKernel` with
`Lk.RelDataClause2`): per stage, a conditional flow line given a σ-algebra containing the relative past. -/
def RelStageKernel2 : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClause2 κ b jumps P E u l k ω₀ c b' J' m EL →
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

/-- **This packet's target (R116): SB2(2)'s conditional half over families carrying the v2 bundle.** -/
def SB2LowerRelStageCond2Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageCond2 κ b jumps P E u l k ω₀ c b' J' h'

/-- **The kernel form of this packet's target (R116).** -/
def SB2LowerRelKernel2Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageKernel2 κ b jumps P E u l k ω₀ c b' J' h'

/-- **The kernel form gives the conditional half** (Theorems 1.2–1.3; LCOND's generic code match
`Lcd.ae_codeMatch_of_condFlowLine_data` and staged induction `Lcd.stageOK_all_of_codeMatch`). -/
theorem sb2LowerRelStageCond2Statement_of_kernel2 (h12p : Theorem12ParamStatement.{u})
    (h13 : Theorem13Statement.{u}) (hker : SB2LowerRelKernel2Statement.{u}) :
    SB2LowerRelStageCond2Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hker κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl j
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hG'' := hG'.affine_finset (m := m) one_pos
  refine Lcd.stageOK_all_of_codeMatch h12p h13 hκ hb'' hG'' (-(Real.pi / 2))
    (fun _ _ _ _ hl => Lv.launch_angle_boundaryWalk hl) hELm hELr (fun j β Y hW => ?_) j
  obtain ⟨𝒢', F', bc, jc, hpast, hcov, hcfl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl j
  exact Lcd.ae_codeMatch_of_condFlowLine_data h12p h13 hκ (-(Real.pi / 2)) hb'' hELm hELr 𝒢' hpast hcov hW hcfl

/-- **SB2(2)'s erasure identity for one relative walk from the v2 data and the re-typed conditional half.** -/
theorem sb2LowerTailLiftExStatement_of_data2_cond2 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hD : SB2LowerRelDriverData2Statement.{u})
    (hcond : SB2LowerRelStageCond2Statement.{u}) : SB2LowerTailLiftExStatement.{u} := by
  have hW := sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hcond κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hD₀ hW₀ hH₀ hC₀ hcond₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hELm, hELr, hcl⟩ := hD₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  have hst := hcond₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl
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
  filter_upwards [hcl, hW₀ c θ hlaunch b' J' h' hb' hT' hG', hH₀ c θ hlaunch b' J' h' hb' hT' hG',
    hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm] with ω hω hWω hHω hCω
  intro β₀ hβ hβ0 hβr
  obtain ⟨tL, γ, hγ⟩ := hCω β₀ hβ hβ0 hβr
  obtain ⟨ι, o, N, hι, htail, hray, hR, hS'⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  have hrange := range_eq_physSet_of_data2 hι hWω hβ hβ0 hβr hγ.1 hγ.2.2.1 (hHω β₀ hβ hβ0 hβr tL hγ.1) htail
    hray hR hS'
  exact isTailLiftOf_iff.2 ⟨tL, γ, hγ, hrange⟩

/-- **SB2(2)'s combined target (R104a) from LIFTSET's v2 data and the re-typed conditional half** (ruling R116; and
Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_data2_cond2 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hD : SB2LowerRelDriverData2Statement.{u})
    (hcond : SB2LowerRelStageCond2Statement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_liftEx h12 h13 h12₀ h13₀
    (sb2LowerTailLiftExStatement_of_data2_cond2 h12 h13 h12₀ h13₀ hD hcond)

end InteractingSLE.Theorem14.SB.Mn
