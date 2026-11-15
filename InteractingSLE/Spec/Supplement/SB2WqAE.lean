/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WqRange
import InteractingSLE.Spec.Supplement.SB2LpAE

/-!
# SB2(2)'s range statement from a reduced relative-driver input

Packet PROVE-T14-SB2LIFT (round 22). PROVE-SB2-LIFTSET's named input `SB2LowerRelDriverStatement` (`RelDriverAt`)
asks, besides the construction of `EL`, for the relative walk's finite lifetimes, `NoLeftMove` and `NoLeftHit` at
every step (`RunInputs.fin₂`, `lm₂`, `lh₂`). These are no longer needed:

* `RunInputs'`: `RunInputs` without `fin₂`, `lm₂`, `lh₂`;
* **`range_eq_physSet_of_bundles'`**: the range identity at one sample from `CurveInputs`, `RunInputs'`, the starts,
  regular relative drivers and the two actual-walk facts. It goes through `range_eq_physSet_of_inputs_arc'` and
  `range_eq_physSet_of_inputs_piece'`;
* `RelDriverAt'`, `SB2LowerRelDriverStatement'`: the named input with `RunInputs'`, and `EL` regular at every sample,
  as in `RelDriverAt`;
* **`sb2LowerRelWalkRangeStatement_of_relDriver'`**: `SB2LowerRelWalkRangeStatement` from it (Theorem 1.3 at universe
  `0`, for `sb2LowerAllowed` and `sb2LowerRightHits`);
* **`sb2LowerLaunchLiftStatement_of_relDriver'`**: SB2(2)'s combined target (R104a), with the conditional half and
  Theorems 1.2–1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The run inputs without the relative walk's GW1-type facts** (LIFTSET's `RunInputs` without `fin₂`, `lm₂`,
`lh₂`). -/
structure RunInputs' (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o N : ℕ) : Prop where
  cont : ContinuousOn ι (Ici R)
  reg₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
  reg₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂
  fin₁ : ∀ j, j + 1 < N + o →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤
  lm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j
  lh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j
  L1 : ∀ i, 2 ≤ i → i < N →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
    (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
    ((D₂ i).2 = ⊤ ↔ (D₁ (i + o)).2 = ⊤) ∧ ((D₂ i).2 = 0 ↔ (D₁ (i + o)).2 = 0)
  fill : ∀ i, 2 ≤ i → i < N →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠ none →
    (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
    (D₁ (i + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (i + o) b₂ J₂ D₂ i ι
  piece : ∀ i, 2 ≤ i → i < N →
    StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
      (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i)
  two_le : 2 ≤ N
  len : ∀ i, 2 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
    i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length
  len₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length
  len₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length
  done : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o N : ℕ}

/-- **The range identity at one sample from the reduced bundles.** -/
theorem range_eq_physSet_of_bundles' (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputs κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ ⊤ →
      (D₁ k).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStart κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  rcases hS with hA | hP
  · exact range_eq_physSet_of_inputs_arc' hι hR.cont hA.even hA.len hA.move hA.angle hA.pt hA.recLe hA.gap hA.low
      hreg₂ hA.zero₀ hR.reg₁ hR.reg₂ hR.fin₁ hR.lm₁ hR.lh₁ hallow hexit₁ hA.nz₁ hR.L1 hR.fill hR.piece hR.two_le
      hR.len hR.len₁ hR.len₂ hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hA.head
  · refine range_eq_physSet_of_inputs_piece' hι hR.cont hP.even hP.launch hP.tip hP.pt hP.recLe hP.top hP.zero
      hP.hitR hP.hitL₂ hP.recR hP.lift₀ hP.memR hP.recAfter hreg₂ hR.reg₁ hR.reg₂ hR.fin₁ hR.lm₁ hR.lh₁ hallow hexit₁
      hP.nz₁ hR.L1 hR.fill hR.piece hR.two_le ?_ hR.len₁ hR.len₂ hR.done hC.range_eq hC.inj hC.visit hC.lift_zero
      hC.head hC.tail hC.ray hP.head
    intro i hi hiN
    rcases eq_or_lt_of_le hi with h1 | h2
    · subst h1
      exact ⟨by have := hP.len.1; omega, hP.len.2⟩
    · exact hR.len i h2 hiN

/-- **The reduced relative-driver data at one launch** (`RelDriverAt` with `RunInputs'`). -/
def RelDriverAt' (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ →
          ∃ (ι : ℝ → ℝ) (o N : ℕ),
            RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (realMax (upperPrefix κ b jumps E u l k ω₀)) ι ∧
            (∀ s, ∀ x : ℝ, β₀ (tL + s) = x → realMax (upperPrefix κ b jumps E u l k ω₀) ≤ x) ∧
            (∀ s, ∀ x : ℝ, realMax (upperPrefix κ b jumps E u l k ω₀) < x → β₀ (tL + s) = x → γ s = ι x) ∧
            RunInputs' κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o N ∧
            (ArcStart κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ tL o ∨
              PieceStart κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)

/-- **Reduced named input: SB2(2)'s relative-driver data at the later launches** (`SB2LowerRelDriverStatement`
without the relative walk's finite lifetimes, `NoLeftMove` and `NoLeftHit`). -/
def SB2LowerRelDriverStatement' : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverAt' κ b jumps P E u l k ω₀ c b' J'

/-- **SB2(2)'s range statement from the reduced relative-driver data** (Theorem 1.3 at universe `0`). -/
theorem sb2LowerRelWalkRangeStatement_of_relDriver' (h13₀ : Exist.Theorem13Statement.{0})
    (hD : SB2LowerRelDriverStatement'.{u}) : SB2LowerRelWalkRangeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ h₀ hH₀ hA₀ hX₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hm1, hm2, hae⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  refine ⟨EL, hm1, hm2, ?_⟩
  filter_upwards [hae, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hA₀ c θ hlaunch b' J' h' hb' hT' hG',
    hX₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hHω hAω hXω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, o, N, hι, htail, hray, hR, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  exact range_eq_physSet_of_bundles' hι ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hHω β₀ hβ hβ0 hβr tL hγ.1, htail, hray⟩ hR
    (fun j => hm2 j ω) (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hS

/-- **SB2(2)'s combined target (R104a) from the reduced relative-driver data and the conditional half** (and
Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_relDriver' (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverStatement'.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_range h12 h13 h12₀ h13₀ (sb2LowerRelWalkRangeStatement_of_relDriver' h13₀ hD) hcond

end InteractingSLE.Theorem14.SB.Lk
