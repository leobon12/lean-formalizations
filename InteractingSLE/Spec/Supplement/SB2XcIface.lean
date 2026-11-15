/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MnIface
import InteractingSLE.Spec.Supplement.SB2TwLock
import InteractingSLE.Spec.Supplement.SB2LuStart

/-!
# SB2(2)'s per-stage correspondence (R116): the statement as typed is false at the zero root; the corrected form

Packet PROVE-T14-SB2LIFT (round 24; ruling R116, PROVE-SB2-LCMEAN's `Mn.SB2LowerStageChainStatement`).

* **The relative root always launches** (`relRun_one_launches`), so `StageChainAt` at `j = 0` asks the actual lower
  walk to launch at stage `relOff` (**`StageChainAt.actual_launch_root`**). At an arc start (`R` first added by a
  connector, `ZeroRoot`) the actual stage `relOff` is the flow stage before that connector. There the walk may stand
  at a restart mark whose seed is not admissible: `restartSet` asks only for a high right height. The flow step then
  leaves the state unchanged and nothing is launched. **`not_stageChainAt_of_notAdm`**: at every such sample
  `StageChainAt` fails, for every relative family. The v2 bundle (`ArcStartData`) does not exclude this
  configuration.
* Two further clauses read chosen traces beyond the lifetimes, where `LuM.trOf` is an unconstrained choice (it is
  constrained only on `[0, ζ]`), so they are not implied by any hypothesis:
  - the boundary limits `γ s ↦ trOf (E B ℓ) (tL + s)` for **every** `s`, also after B's lifetime;
  - `IsSB2RelChain`'s global `IsLoewnerTrace` field with the trace `trOf (EL j)`, also after the relative lifetime.
* **The corrected statement** `StageChainAtR` / **`SB2LowerStageChainStatementR`**:
  - only relative stages of positive lifetime (`(EL j ω).2 ≠ 0`; this excludes exactly the zero root);
  - the boundary-limit clause only before B's lifetime;
  - the chain's trace any `ηr` agreeing with `trOf (EL j)` below the relative lifetime.

  It is a weakening: **`StageChainAt.toR`**, **`sb2LowerStageChainStatementR_of`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.SB.Mn

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk
open LuM (trOf)
open FinRel (IsSB2RelChain)
open PiecewiseConstantBoundaryData (rightLim leftLim)

section Corr

variable (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ)
  (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ) (EL : ℕ → Ω → Drv)

/-- **The relative root always launches** (with the root chart and angle `−π/2`). -/
theorem relRun_one_launches (ω : Ω) :
    (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω) (0 + 1)).2.2.2.1 0 =
      some ((ExplState.init 0).2.2.2.2.1, -(Real.pi / 2)) := by
  unfold relLowerSpec
  rw [zero_add, run_one_walk (κ := κ) (θ := -(Real.pi / 2)) (affData 1 m b') (affJumps 1 m J') (fun i => EL i ω),
    launches_launch, Function.update_self]

/-- **`StageChainAt` at the relative root asks the actual walk to launch at stage `relOff`.** -/
theorem StageChainAt.actual_launch_root {ω : Ω} (h : StageChainAt κ b jumps E u l k ω₀ c b' J' m EL ω) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)
      (0 + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) + 1)).2.2.2.1
      (0 + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ≠ none :=
  (h 0 _ _ (relRun_one_launches κ b' J' m EL ω)).1

/-- **The counterexample**: if at the matched stage `o = relOff` the actual walk stands at a restart mark with a seed
that is not admissible, nothing is launched there and `StageChainAt` fails (for every relative family). -/
theorem not_stageChainAt_of_notAdm {ω : Ω} {o : ℕ}
    (hoff : relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) = o)
    (hk : o < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length) (hev : o % 2 = 0)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) o) = GW1W.stArcM true)
    (hadm : ¬ ExplState.IsAdmissibleSeed κ
      (leftLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) o)))
      (rightLim b (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) o))) (-(Real.pi / 2))) :
    ¬ StageChainAt κ b jumps E u l k ω₀ c b' J' m EL ω := by
  intro h
  have hl := StageChainAt.actual_launch_root κ b jumps E u l k ω₀ c b' J' m EL h
  rw [hoff, zero_add, GW1W.run_succ_walk_flow hk hev, flowStep_of_arcM_not_adm hst hadm] at hl
  exact hl (launches_run_of_le _ _ le_rfl)

/-- **The per-stage correspondence, corrected** (relative stages of positive lifetime; boundary limits before B's
lifetime; the chain's trace agrees with `EL`'s below the relative lifetime). -/
def StageChainAtR (ω : Ω) : Prop :=
  ∀ (j : ℕ) (c₁ : Chart) (θ' : ℝ),
    (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
      (j + 1)).2.2.2.1 j = some (c₁, θ') →
    (EL j ω).2 ≠ 0 →
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
      (∀ s : ℝ≥0, ((tL + s : ℝ≥0) : ℝ≥0∞) <
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω).2 →
        Tendsto (stageRelChart (walkStageChart κ b jumps E
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) c c₁ m).2.1
        (𝓝[H] (γ s)) (𝓝 (trOf (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
            (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω) (tL + s)))) ∧
      (∃ ηr : ℝ → ℂ, (∀ r : ℝ, 0 ≤ r → ENNReal.ofReal r < (EL j ω).2 → ηr r = trOf (EL j ω) r.toNNReal) ∧
      ∀ S₀ : ℝ≥0, ((tL + S₀ : ℝ≥0) : ℝ≥0∞) <
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
          γ tL (S₀ : ℝ) (fun r : ℝ => (EL j ω).1 r.toNNReal) ηr) ∧
      (EL j ω).2 = ⨆ (S₀ : ℝ≥0) (_ : ((tL + S₀ : ℝ≥0) : ℝ≥0∞) <
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (j + relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω)) ω).2),
        ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) (S₀ : ℝ))

/-- **The corrected form is a weakening.** -/
theorem StageChainAt.toR {ω : Ω} (h : StageChainAt κ b jumps E u l k ω₀ c b' J' m EL ω) :
    StageChainAtR κ b jumps E u l k ω₀ c b' J' m EL ω := by
  intro j c₁ θ' hl _
  obtain ⟨h1, h2, tL, γ, h3, h4, h5⟩ := h j c₁ θ' hl
  exact ⟨h1, h2, tL, γ, fun s _ => h3 s, ⟨_, fun _ _ _ => rfl, h4⟩, h5⟩

end Corr

/-- **SB2(2)'s per-stage correspondence, corrected** (`SB2LowerStageChainStatement` with `StageChainAtR`). -/
def SB2LowerStageChainStatementR : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → _ → Drv,
      (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
      RelDataClause2 κ b jumps P E u l k ω₀ c b' J' m EL →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        StageChainAtR κ b jumps E u l k ω₀ c b' J' m EL ω

/-- The statement as typed implies the corrected one. -/
theorem sb2LowerStageChainStatementR_of (h : SB2LowerStageChainStatement.{u}) :
    SB2LowerStageChainStatementR.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [h κ hκ hκ4 b jumps hb P h' hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ hω₀
  intro c θ hlaunch b' J' h'' hb' hT' hG' hk m hm EL hEL hreg hD
  filter_upwards [hω₀ c θ hlaunch b' J' h'' hb' hT' hG' hk m hm EL hEL hreg hD] with ω hω
  exact StageChainAt.toR κ b jumps E u l k ω₀ c b' J' m EL hω

end InteractingSLE.Theorem14.SB.Mn
