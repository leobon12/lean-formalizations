/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MrZero
import InteractingSLE.Spec.Supplement.SB2LkCurve
import InteractingSLE.Spec.Supplement.SBLyTop
import InteractingSLE.Spec.Supplement.GW1WalkExitStatement
import InteractingSLE.Spec.Supplement.GW1ParamProof

/-!
# SB2(2)'s conditional half from the code match at stages of positive lifetime (ruling R120, D11)

Packet PROVE-SB2-LCMEAN, round 12. The conditional half `Mq.SB2LowerRelStageCond3Statement` is the staged induction
of LCOND (`Lcd.stageOK_all_of_codeMatch`): at every relative stage, the actual relative driver matches the canonical
driver code of every witness of the stage's conditional law. D11 splits the stages by the lifetime of `EL`:

* **lifetime `0`**: only at the relative root (SB2LIFT's (L1), `Mq.StageChainAtZ`), and there only at an arc start
  (LIFTSET's `PieceStartV` gives positive lifetime); then the root seed is inadmissible (`ArcStart.low`,
  `RayCorr.rightLim_eq`), so the canonical code has lifetime `0` (`Mr.ae_codeMatch_of_seedThreshold`,
  `Mr.ae_seedThreshold_root_iff`). Proved here: **`ae_codeMatch_relRoot_zero`**;
* **positive lifetime**: K2 at the matched actual stage — the remaining named target **`SB2LowerRelPos3Statement`**.

To read LIFTSET's bundle one needs a proper parametrization of the lower walk; it exists almost surely by GW1's
parametrization, which follows from Theorems 1.2–1.3 (**`rightWalkProperRegStatement_of_thms`**, the derivation of
`Ly.gw1PieceSimpleStatement_of_thm12_thm13` continued by GW1's walk-exit geometry).

* **`sb2LowerRelStageCond3Statement_of_pos3`**: the conditional half from the positive-lifetime code match, SB2LIFT's
  per-stage statement `Mq.SB2LowerStageChainStatementRP` (only its zero clause is used here) and Theorems 1.2–1.3.

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

namespace InteractingSLE.Theorem14.SB.Mr

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn Mq Restart

/-- **The lower walk is a proper curve, from Theorems 1.2–1.3** (GW1's parametrization: GB6's restart, BW1's terminal
path, the retarget path, the walk launch clock and the walk-exit geometry). -/
theorem rightWalkProperRegStatement_of_thms (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    WalkCont.RightWalkProperRegStatement.{u} := by
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hGB6 := Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀)
    (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hGR := (GW1WalkExit.paramEveryRegStatements_of_walkClock_and_geometry hGB6 h13 h13₀ hClock hD4).1
  exact GW1X.rightWalkProperRegStatement_of_gw1ParamR51 (GW1X.gw1ParamR51Statement_of_everyReg hGR)

/-- **SB2(2)'s relative root of lifetime `0` matches the canonical code** (D11): almost surely under the retained
kernel, if the relative root has lifetime `0`, LIFTSET's bundle is at an arc start (`PieceStartV` gives positive
lifetime, also at an infinite start piece), the root seed is inadmissible (the root's right height is the actual one
at `R`, `≤ −λ`), and the root driver matches the canonical code of every witness of the root's law. -/
theorem ae_codeMatch_relRoot_zero (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ}
    {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J')
    {h' : Ω → DistOn upperHalfPlaneOpens}
    (hG' : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      h' b' J') {m : ℝ} {EL : ℕ → Ω → Drv} (hELm : ∀ j, Measurable (EL j)) (hELr : ∀ j ω, IsRegularDriver (EL j ω))
    (hcl : RelDataClause3 κ b jumps P E u l k ω₀ c b' J' m EL)
    (hβ₀ : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∃ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ ∧ β₀ 0 = 0 ∧ range β₀ = lowerWalkSet κ b jumps E ω)
    (htl : ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hW : IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL 0 β Y) :
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      (EL 0 ω).2 = 0 →
      IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL 0 ω).1 t) (EL 0 ω).2 := by
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hG'' := hG'.affine_finset (m := m) one_pos
  filter_upwards [hcl, hβ₀, htl, ae_seedThreshold_root_iff hκ hb'' hG'' (-(Real.pi / 2)) hW,
    ae_codeMatch_of_seedThreshold h12p h13 hκ (-(Real.pi / 2)) hb'' hELm hELr hW]
    with ω hc hb0 htlω hthr hmatch hz
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hb0
  obtain ⟨tL, γ, hγ⟩ := htlω β₀ hβ hβ0 hβr
  obtain ⟨ι, o, hι, -, -, -, hS⟩ := hc β₀ hβ hβ0 hβr tL γ hγ
  replace hS : ArcStart κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ tL o ∨
    PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
      (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o := by
    rcases hS with ⟨-, -, hS⟩ | ⟨hP, -⟩
    · exact hS
    · exact Or.inr hP
  have hl0 : (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
      (0 + 1)).2.2.2.1 0 ≠ none := by
    rw [relRun_one_launches κ b' J' m EL ω]
    exact Option.some_ne_none _
  rcases hS with hA | hP
  · refine hmatch hl0 (hthr.2 fun hadm => ?_) hz
    have h1 := hι.rightLim_eq _ le_rfl
    rw [hι.map_base] at h1
    have h2 := hA.low
    have h3 := hadm.2
    rw [h1] at h3
    linarith
  · exfalso
    have hlo : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (o + 1)).2.2.2.1 o ≠ none := by
      rw [hP.launch, launches_launch, Function.update_self]
      exact Option.some_ne_none _
    exact hP.nz₁ o le_rfl hlo (hP.zero.1 hz)

/-! ### The positive-lifetime code match (the remaining target) and the assembly -/

section Pos

variable (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
  [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (E : ExplSpec → ℕ → Ω → Drv) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ)
  (J' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens)

/-- **The code match at relative stages of positive lifetime** (K2 at the matched actual stage): for every family
carrying LIFTSET's bundle and every witness of a relative stage's conditional law, almost surely under the retained
kernel, a launched relative stage of positive lifetime matches the canonical driver code. -/
def RelStagePos3 : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → Drv,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    RelDataClause3 κ b jumps P E u l k ω₀ c b' J' m EL →
    ∀ (j : ℕ) (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      IsStageWitness κ (affData 1 m b') (affJumps 1 m J')
        (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
        (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL j β Y →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        (ExplState.run κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) (fun i => EL i ω)
          (j + 1)).2.2.2.1 j ≠ none → (EL j ω).2 ≠ 0 →
        IsDriverCodeMatch (driverCode h12p hκ (-(Real.pi / 2)) (β ω, Y ω)) (fun t => (EL j ω).1 t) (EL j ω).2

end Pos

/-- **Named target (this packet, R120): SB2(2)'s code match at relative stages of positive lifetime.** -/
def SB2LowerRelPos3Statement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → ∀ hκ : 0 < κ, RelStagePos3 h12p hκ b jumps P E u l k ω₀ c b' J' h'

/-- **SB2(2)'s conditional half from the positive-lifetime code match** (ruling R120): the zero-lifetime stages are
the root at an arc start (`ae_codeMatch_relRoot_zero`) and nothing else (SB2LIFT's zero clause); LCOND's staged
induction concludes. -/
theorem sb2LowerRelStageCond3Statement_of_pos3 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerStageChainStatementRP.{u})
    (hpos : SB2LowerRelPos3Statement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    SB2LowerRelStageCond3Statement.{u} := by
  set h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13 with hh12p
  have hPR := rightWalkProperRegStatement_of_thms h12 h13 h12₀ h13₀
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβP := hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER
  filter_upwards [hZ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hpos κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hβP] with ω₀ hZ₀ hP₀ hC₀ hβ₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl j
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hG'' := hG'.affine_finset (m := m) one_pos
  refine Lcd.stageOK_all_of_codeMatch h12p h13 hκ hb'' hG'' (-(Real.pi / 2))
    (fun _ _ _ _ hl => Lv.launch_angle_boundaryWalk hl) hELm hELr (fun j β Y hW => ?_) j
  have hpos' := hP₀ c θ hlaunch b' J' h' hb' hT' hG' hk hκ m hm EL hELm hELr hcl j β Y hW
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · filter_upwards [hpos', ae_codeMatch_relRoot_zero h12p h13 hκ hb' hG' hELm hELr hcl hβ₀
      (hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm) hW] with ω h1 h2 hl
    by_cases hz : (EL 0 ω).2 = 0
    · exact h2 hz
    · exact h1 hl hz
  · filter_upwards [hpos', hZ₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl] with ω h1 h2 hl
    by_cases hz : (EL j ω).2 = 0
    · obtain ⟨⟨c₁, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
      exact absurd hz (h2.2.2 j c₁ θ' hj hcθ)
    · exact h1 hl hz

end InteractingSLE.Theorem14.SB.Mr
