/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CfTail

/-!
# SB2(2)'s conditional half over the corrected bundle, and the hypothesis `hTL` of Theorem 1.4's top

Packet PROVE-SB2-CONDFIN (Target 2, D36). Over the corrected bundle `RelDataClauseW` (`ClauseTW ∧ StageFactsAS ∧
RootFactsAS`):

* `ae_codeMatch_relRoot_zeroW`: the zero-lifetime root (LCMEAN's `Mr.ae_codeMatch_relRoot_zero`, which reads the
  bundle only through the ray correspondence and the start disjunction, both kept by `ClauseTW`);
* `sb2LowerRelPosWStatement_of_tail_root`: the positive-lifetime code match from the tail stages and the root;
* **`sb2LowerRelStageCondWStatement_of_posW`**: the conditional half `CondW` from the positive-lifetime code match and
  the zero clause (LCOND's staged induction `Lcd.stageOK_all_of_codeMatch`), Theorems 1.2–1.3;
* **`sb2LowerRelStageCondWStatement`**: `CondW` from the named inputs `SB2LowerZeroClauseWStatement` (SB2LIFT),
  `Mz.SB2LowerStageCanonStatement` (LIFTSET) and `SB2LowerRelPosWRootStatement` (the root law), Theorems 1.2–1.3;
* **`sb2LowerTailLiftExStatement_of_condW`**: `Lk.SB2LowerTailLiftExStatement` — the hypothesis `hTL` of
  `Wire.theorem14Statement_assembled7` — from the data `SB2LowerRelDriverStatementTWR`, the range identity
  `SB2LowerRangeTWStatement` and `CondW` (Theorem 1.3); **`sb2LowerTailLiftExStatement_of_inputs`**: `hTL` from all
  the named inputs.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cf

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw Lk Mn Mq Mr Restart

/-- **The zero-lifetime relative root matches the canonical code** (over the corrected bundle). -/
theorem ae_codeMatch_relRoot_zeroW (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → Drv} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ}
    {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J')
    {h' : Ω → DistOn upperHalfPlaneOpens}
    (hG' : IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      h' b' J') {m : ℝ} {EL : ℕ → Ω → Drv} (hELm : ∀ j, Measurable (EL j)) (hELr : ∀ j ω, IsRegularDriver (EL j ω))
    (hcl : ClauseTW κ b jumps P E u l k ω₀ c b' J' m EL)
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
  obtain ⟨ι, hι, -, -, hS⟩ := hc β₀ hβ hβ0 hβr tL γ hγ
  set o := relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) with ho
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

/-- **The positive-lifetime code match from the tail stages and the root** (over the corrected bundle). -/
theorem sb2LowerRelPosWStatement_of_tail_root {h12p : Theorem12ParamStatement.{u}}
    (htail : SB2LowerRelPosWTailStatement.{u} h12p) (hroot : SB2LowerRelPosWRootStatement.{u} h12p) :
    SB2LowerRelPosWStatement.{u} h12p := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [htail κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hroot κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ ht₀ hr₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk hκ' m hm EL hELm hELr hcl j β Y hW
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · filter_upwards [hr₀ c θ hlaunch b' J' h' hb' hT' hG' hk hκ' m hm EL hELm hELr hcl β Y hW] with ω h1 _ hz
    exact h1 hz
  · exact ht₀ c θ hlaunch b' J' h' hb' hT' hG' hk hκ' m hm EL hELm hELr hcl j hj β Y hW

/-- **SB2(2)'s conditional half over the corrected bundle from the positive-lifetime code match and the zero clause**
(LCMEAN's `Mv.sb2LowerRelStageCond4Statement_of_pos4` over `RelDataClauseW`). -/
theorem sb2LowerRelStageCondWStatement_of_posW (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroClauseWStatement.{u})
    (hpos : SB2LowerRelPosWStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    SB2LowerRelStageCondWStatement.{u} := by
  set h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13 with hh12p
  have hPR := Mr.rightWalkProperRegStatement_of_thms h12 h13 h12₀ h13₀
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
  · filter_upwards [hpos', ae_codeMatch_relRoot_zeroW h12p h13 hκ hb' hG' hELm hELr hcl.1 hβ₀
      (hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm) hW] with ω h1 h2 hl
    by_cases hz : (EL 0 ω).2 = 0
    · exact h2 hz
    · exact h1 hl hz
  · filter_upwards [hpos', hZ₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl.1 hcl.2.1] with ω h1 h2 hl
    by_cases hz : (EL j ω).2 = 0
    · obtain ⟨⟨c₁, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
      exact absurd hz (h2 j c₁ θ' hj hcθ)
    · exact h1 hl hz

/-- **SB2(2)'s conditional half over the corrected bundle (Target 2, D36's `CondW`)**, from the zero clause
(SB2LIFT), the canonical tail objects (LIFTSET's joint induction), the root's positive-lifetime code match (the root
law) and Theorems 1.2–1.3. -/
theorem sb2LowerRelStageCondWStatement (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hZ : SB2LowerZeroClauseWStatement.{u})
    (hcan : Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))
    (hroot : SB2LowerRelPosWRootStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    SB2LowerRelStageCondWStatement.{u} :=
  sb2LowerRelStageCondWStatement_of_posW h12 h13 h12₀ h13₀ hZ
    (sb2LowerRelPosWStatement_of_tail_root (sb2LowerRelPosWTailStatement_of_canon h12 h13 h12₀ h13₀ hZ hcan) hroot)

/-- **`hTL` from the data, the range identity and the conditional half** (over the corrected bundle). -/
theorem sb2LowerTailLiftExStatement_of_condW (h13 : Theorem13Statement.{u})
    (hD : SB2LowerRelDriverStatementTWR.{u}) (hrange : SB2LowerRangeTWStatement.{u})
    (hcond : SB2LowerRelStageCondWStatement.{u}) : SB2LowerTailLiftExStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hrange κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hcond κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ hD₀ hr₀ hcond₀
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
  exact ⟨EL, hS, stagedPiecesRegular_of_regular h13 hκ hb'' hS hELr,
    hr₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hcl.1 hcl.2.1⟩

/-- **`hTL` (the SB2(2) hypothesis of `Wire.theorem14Statement_assembled7`) from the named inputs**: the data with
root facts (LIFTSET/SB2LIFT), the range identity (SB2LIFT, D36 (1)), the zero clause (SB2LIFT), the canonical tail
objects (LIFTSET) and the root law (NOJUMP / REVIEW-FABLE-T14), with Theorems 1.2–1.3. -/
theorem sb2LowerTailLiftExStatement_of_inputs (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hD : SB2LowerRelDriverStatementTWR.{u})
    (hrange : SB2LowerRangeTWStatement.{u}) (hZ : SB2LowerZeroClauseWStatement.{u})
    (hcan : Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13))
    (hroot : SB2LowerRelPosWRootStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    SB2LowerTailLiftExStatement.{u} :=
  sb2LowerTailLiftExStatement_of_condW h13 hD hrange
    (sb2LowerRelStageCondWStatement h12 h13 h12₀ h13₀ hZ hcan hroot)

end InteractingSLE.Theorem14.SB.Cf
