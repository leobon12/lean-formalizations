/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkCurve
import InteractingSLE.Spec.Supplement.SB2LkRelMeas

/-!
# SB2(2)'s erasure identity split into its geometric and its conditional half

Packet PROVE-T14-SB2LIFT (round 3). `Lk.SB2LowerTailLiftExStatement` (some regular staged relative walk of the
conditional field carries the actual lower tail's lift) is split along the source's proof (pp. 631–633) into:

* **`SB2LowerRelWalkStatement`** (the geometric and measurable half; "lift the remaining tail into `D_A`. The result
  is again a finite simple proper lower walk"): at the later launches, conditionally on the upper past, there is a
  measurable family of drivers `EL`, regular at every sample, whose run of the relative lower program carries the
  actual tail's lift (`Lf.IsTailLiftOf`) — the relative drivers of the lifted stages (built from the lift curve
  `Lk.sb2LowerTailLiftCurve` with the measurable-driver core `SB2LkRelMeas`);
* **`SB2LowerRelStageCondStatement`** (the conditional half, per stage; "Integrated uniqueness and the field-determining
  graphs identify the actual relative ordinary flows"): every such family is, stage by stage, a conditional flow line
  of the conditional field under the retained kernel — the last clause of `IsStagedHistory` (K2 in the relative staged
  filtration, PROVE-T14-SB2DRV's `SB2EntranceK2Statement` per stage);
* **`sb2LowerTailLiftExStatement_of_split`**: the two halves give `SB2LowerTailLiftExStatement` (the remaining clauses
  of `IsStagedHistory`: measurability, the retained past as an event — `runMeasStatement` for regular drivers — and the
  value at the lifetime; `StagedPiecesRegular` from Theorem 1.3), hence `sb2LowerLaunchLiftStatement_of_split`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw

/-- **The geometric half at one launch**: for `m = −e_R` there is a measurable family of drivers, regular at every
sample, whose relative walk carries the actual tail's lift almost surely under the retained kernel. -/
def RelWalk (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)

/-- **Named input: SB2(2)'s geometric half at the later launches.** -/
def SB2LowerRelWalkStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelWalk κ b jumps P E u l k ω₀ c b' J'

/-- **The conditional half at one launch**: every measurable family of drivers regular at every sample whose relative
walk carries the actual tail's lift is, at every stage, a conditional flow line of the conditional field (frame
`affField m h'`) under the retained kernel given its own relative past (the last clause of `IsStagedHistory`). -/
def RelStageCond (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ)
    (h' : Ω → DistOn upperHalfPlaneOpens) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∀ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) → (∀ j ω, IsRegularDriver (EL j ω)) →
    (∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        Lf.IsTailLiftOf c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀
          (relWalkSet κ (affData 1 m b') (affJumps 1 m J') EL ω)) →
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

/-- **Named input: SB2(2)'s conditional half at the later launches** (per stage). -/
def SB2LowerRelStageCondStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' h' =>
    0 < k → RelStageCond κ b jumps P E u l k ω₀ c b' J' h'

/-- **The two halves give SB2(2)'s erasure identity for one relative walk.** -/
theorem sb2LowerTailLiftExStatement_of_split (h13 : Exist.Theorem13Statement.{u})
    (hgeo : SB2LowerRelWalkStatement.{u}) (hcond : SB2LowerRelStageCondStatement.{u}) :
    SB2LowerTailLiftExStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hgeo κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hcond κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ hgeo₀ hcond₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hELm, hELr, hlift⟩ := hgeo₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  have hst := hcond₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm EL hELm hELr hlift
  have hb'' := isPiecewiseConstantBoundaryData_affData (m := m) one_pos hb'
  have hpast : ∀ j, Measurable (pastMap κ (affData 1 m b') (affJumps 1 m J') (relLowerSpec b' J' m) EL j) :=
    fun j => measurable_pastMap runMeasStatement hb'' (relLowerSpec b' J' m) (k := j) (fun i _ => hELm i)
      (fun i _ => hELr i) j le_rfl
  have hS : IsStagedHistory κ (affData 1 m b') (affJumps 1 m J')
      (condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀)
      (fun ω => affField m one_pos (h' ω)) (relLowerSpec b' J' m) EL := by
    refine ⟨hELm, fun j => ?_, fun j => Eventually.of_forall fun ω hne hpos c₀ hc₀ => (hELr j ω).2.2.2 hne hpos c₀ hc₀,
      hst⟩
    rw [pastSigma_eq_comap]
    exact (hpast j).comap_le
  exact ⟨EL, hS, stagedPiecesRegular_of_regular h13 hκ hb'' hS hELr, hlift⟩

/-- **SB2(2)'s combined target (R104a) from the two halves** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_split (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hgeo : SB2LowerRelWalkStatement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_liftEx h12 h13 h12₀ h13₀ (sb2LowerTailLiftExStatement_of_split h13 hgeo hcond)

end InteractingSLE.Theorem14.SB.Lk
