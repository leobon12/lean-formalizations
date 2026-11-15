/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LbPiece
import InteractingSLE.Spec.Supplement.StagedRegularize

/-!
# SB2(2): the construction of the relative drivers `EL` from the relative stage curves

Packet PROVE-SB2-LIFTSET (round 9). The relative walk's drivers are built from its stage curves (the lifted actual
pieces read in the relative run charts) with SB2LIFT's measurable-driver core and the regularization of staged drivers:

* **`exists_EL_of_stageCurves`**: curves `ρ j ω : ℝ → ℂ`, measurable in `ω` at every time, driven
  (`IsDrivenCurve`) on measurable events `G j`, have drivers `EL j ω` that are **measurable, regular at every sample**,
  and on `G j` have the capacity lifetime of `ρ j ω` and generate its capacity reparametrization
  (`exists_measurable_driver_of_drivenCurves`, then `StagedReg.regularize ⊤`, which is measurable, everywhere regular
  and unchanged before the lifetime);
* **`exists_EL_of_stageCurves_zero`**: the same with `zeroDrv` on measurable events `Z j` (the relative zero root of an
  arc start);
* `RelDataClause`, `relDriverDataAt_of_clause`: `RelDriverDataAt` is "some measurable everywhere regular `EL` satisfies
  the data clause";
* **`RelStageCurvesAt`**, **`SB2LowerRelStageCurvesStatement`** (named input): stage curves and events such that
  every everywhere regular family that is `zeroDrv` on `Z j` and generates `ρ j ω` on `G j ∖ Z j` satisfies the data
  clause; **`sb2LowerRelDriverDataStatement_of_stageCurves`**, `sb2LowerLaunchLiftStatement_of_stageCurves`: SB2(2)'s
  combined target (R104a) from the stage curves, the conditional half and Theorems 1.2–1.3.

So `EL` is built; the remaining content is the stage curves themselves (the lifted actual pieces in the relative run
charts, `SB2LpLift.liftRel_of_closure` for the lift relation) — see the handoff.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C

/-- **The relative drivers of a family of stage curves** (the construction of `EL` from its stage curves): curves
`ρ j ω : ℝ → ℂ`, measurable in `ω` at every time `t ≥ 0`, driven (`IsDrivenCurve`) on measurable events `G j`, have a
family of drivers `EL j ω` that is measurable, regular at every sample, and on `G j` has the capacity lifetime of
`ρ j ω` and generates its capacity reparametrization on every shorter horizon. -/
theorem exists_EL_of_stageCurves {Ω : Type*} [MeasurableSpace Ω] {ρ : ℕ → Ω → ℝ → ℂ}
    (hm : ∀ j t, 0 ≤ t → Measurable fun ω => ρ j ω t) {G : ℕ → Set Ω} (hG : ∀ j, MeasurableSet (G j))
    (hρ : ∀ j, ∀ ω ∈ G j, IsDrivenCurve (ρ j ω)) :
    ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      ∀ j, ∀ ω ∈ G j, (EL j ω).2 = capLife (ρ j ω) ∧
        ∀ T < capLife (ρ j ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j ω)) := by
  choose W U hW hU hW0 hWc hG' using fun j => exists_measurable_driver_of_drivenCurves (hm j) (hG j) (hρ j)
  refine ⟨fun j ω => StagedReg.regularize ⊤ (fun t => W j t ω, U j ω), fun j => ?_,
    fun j ω => StagedReg.isRegularDriver_regularize ⊤ _, fun j ω hω => ?_⟩
  · refine (StagedReg.measurable_regularize ⊤).comp (Measurable.prodMk ?_ (hU j))
    exact measurable_pi_iff.2 fun t => hW j t
  · obtain ⟨hlife, hgen⟩ := hG' j ω hω
    refine ⟨by rw [StagedReg.regularize_snd, hlife], fun T hT => ?_⟩
    have hT' : T < U j ω := hlife ▸ hT
    refine Restart.StoppedK2.isGeneratingTrace_congr (fun t ht => ?_) (hgen T hT')
    exact (StagedReg.regularize_eq_of_lt ⊤ (e := (fun t => W j t ω, U j ω)) (hW0 j ω) (hWc j ω)
      (lt_trans ht hT')).symm

universe u

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The per-sample data clause of `RelDriverDataAt` for one relative driver family `EL`** (the part after
measurability and regularity). -/
def RelDataClause (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) (m : ℝ)
    (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
    ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
      ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ →
        ∃ (ι : ℝ → ℝ) (o N : ℕ),
          RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (realMax (upperPrefix κ b jumps E u l k ω₀)) ι ∧
          (∀ s, ∀ x : ℝ, β₀ (tL + s) = x → realMax (upperPrefix κ b jumps E u l k ω₀) ≤ x) ∧
          (∀ s, ∀ x : ℝ, realMax (upperPrefix κ b jumps E u l k ω₀) < x → β₀ (tL + s) = x → γ s = ι x) ∧
          RunInputs κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
            (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o N ∧
          (ArcStartData κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) o ∨
            PieceStartData κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- `RelDriverDataAt` is "some measurable, everywhere regular `EL` satisfies the data clause". -/
theorem relDriverDataAt_of_clause {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ}
    (h : ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
        RelDataClause κ b jumps P E u l k ω₀ c b' J' m EL) :
    RelDriverDataAt κ b jumps P E u l k ω₀ c b' J' := h


/-- **The relative drivers with zero roots**: as `exists_EL_of_stageCurves`, and on measurable events `Z j` the
driver is the zero root `zeroDrv` (the relative zero-lifetime first piece of an arc start). -/
theorem exists_EL_of_stageCurves_zero {Ω : Type*} [MeasurableSpace Ω] {ρ : ℕ → Ω → ℝ → ℂ}
    (hm : ∀ j t, 0 ≤ t → Measurable fun ω => ρ j ω t) {G Z : ℕ → Set Ω} (hG : ∀ j, MeasurableSet (G j))
    (hZ : ∀ j, MeasurableSet (Z j)) (hρ : ∀ j, ∀ ω ∈ G j, IsDrivenCurve (ρ j ω)) :
    ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      (∀ j, ∀ ω ∈ Z j, EL j ω = zeroDrv) ∧
      ∀ j, ∀ ω ∈ G j, ω ∉ Z j → (EL j ω).2 = capLife (ρ j ω) ∧
        ∀ T < capLife (ρ j ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j ω)) := by
  classical
  obtain ⟨EL₀, hm₀, hr₀, hg₀⟩ := exists_EL_of_stageCurves hm hG hρ
  refine ⟨fun j ω => if ω ∈ Z j then zeroDrv else EL₀ j ω, fun j => ?_, fun j ω => ?_, fun j ω hω => ?_,
    fun j ω hω hnZ => ?_⟩
  · exact Measurable.ite (hZ j) measurable_const (hm₀ j)
  · dsimp only
    split_ifs
    · exact isRegularDriver_zeroDrv
    · exact hr₀ j ω
  · simp only [hω, ↓reduceIte]
  · simp only [hnZ, ↓reduceIte]
    exact hg₀ j ω hω


open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The stage curves of the relative walk at one launch** (the geometric content left after the measurable
construction of `EL`): curves `ρ j ω`, measurable at every time, driven on measurable events `G j`, zero events `Z j`,
such that **every** everywhere regular driver family that is `zeroDrv` on `Z j` and generates `ρ j ω` (with its capacity
lifetime) on `G j ∖ Z j` satisfies the data clause. -/
def RelStageCurvesAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ (ρ : ℕ → Ω → ℝ → ℂ) (G Z : ℕ → Set Ω),
    (∀ j t, 0 ≤ t → Measurable fun ω => ρ j ω t) ∧ (∀ j, MeasurableSet (G j)) ∧ (∀ j, MeasurableSet (Z j)) ∧
    (∀ j, ∀ ω ∈ G j, IsDrivenCurve (ρ j ω)) ∧
    ∀ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, (∀ j ω, IsRegularDriver (EL j ω)) →
      (∀ j, ∀ ω ∈ Z j, EL j ω = zeroDrv) →
      (∀ j, ∀ ω ∈ G j, ω ∉ Z j → (EL j ω).2 = capLife (ρ j ω) ∧
        ∀ T < capLife (ρ j ω), IsGeneratingTrace (EL j ω).1 T (capTrace (ρ j ω))) →
      RelDataClause κ b jumps P E u l k ω₀ c b' J' m EL

/-- **Named input: SB2(2)'s relative stage curves at the later launches.** -/
def SB2LowerRelStageCurvesStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelStageCurvesAt κ b jumps P E u l k ω₀ c b' J'

/-- **`EL` is built from the stage curves**: the head-free relative-driver data follow
(`exists_EL_of_stageCurves_zero`). -/
theorem sb2LowerRelDriverDataStatement_of_stageCurves (hS : SB2LowerRelStageCurvesStatement.{u}) :
    SB2LowerRelDriverDataStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk
  refine relDriverDataAt_of_clause fun m hm => ?_
  obtain ⟨ρ, G, Z, hm', hG, hZ, hρ, hcl⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, h1, h2, h3, h4⟩ := exists_EL_of_stageCurves_zero hm' hG hZ hρ
  exact ⟨EL, h1, h2, hcl EL h2 h3 h4⟩

/-- **SB2(2)'s combined target (R104a) from the stage curves and the conditional half** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_stageCurves (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hS : SB2LowerRelStageCurvesStatement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_data h12 h13 h12₀ h13₀ (sb2LowerRelDriverDataStatement_of_stageCurves hS) hcond

end InteractingSLE.Theorem14.SB.Lk
