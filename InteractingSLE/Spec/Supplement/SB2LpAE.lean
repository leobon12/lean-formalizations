/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LpRange

/-!
# SB2(2)'s range identity: the almost-sure assembly

Packet PROVE-SB2-LIFTSET (round 2). The one-sample theorems of `SB2LpRange` are packaged and lifted to the
almost-sure statement `Lk.SB2LowerRelWalkRangeStatement` (PROVE-T14-SB2LIFT §R7.2):

* the per-sample bundles **`CurveInputs`** (the parametrization `β₀` and the lift curve `γ`), **`RunInputs`** (the
  named inputs of the lockstep run from relative stage `2`: both walks' GW1-type facts, (L1), `FillCorr`, and the lift
  relation at every launch), **`ArcStart`**, **`PieceStart`** (the two starts), and
  **`range_eq_physSet_of_bundles`**: the relative physical set is `range γ`;
* **`RelDriverAt`**, **`SB2LowerRelDriverStatement`** (named input): a measurable `EL`, regular at every sample, with
  almost surely, for every `β₀` and every lift curve `γ`, a ray correspondence, a start offset and a final stage
  satisfying the bundles (the fields of `CurveInputs` that are automatic — `range β₀`, injectivity, `β₀ t_L = R`,
  `γ 0 = 0` — and the head clause, proved almost surely by **`sb2LowerHead`** (Lemma S2), are not asked);
* **`sb2LowerRelWalkRangeStatement_of_relDriver`**, `sb2LowerLaunchLiftStatement_of_relDriver` (with the conditional
  half `SB2LowerRelStageCondStatement` and Theorems 1.2–1.3: SB2(2)'s combined target, R104a).

What the named input still contains: the construction of `EL` (the relative pieces as intrinsic lifts of the actual
ones, `SB2LpLift.liftRel_of_closure`), SB2LIFT's GW1-type and fill inputs, and the deterministic facts on the actual
walk (`tail`, the head inclusion of the start bundles, the ray injectivity — see the handoff).
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

/-! ### The per-sample bundles -/

section Bundles

/-- The hypotheses on the parametrization `β₀` of the actual walk and on the lift curve `γ`. -/
structure CurveInputs (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) : Prop where
  range_eq : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
  inj : Function.Injective β₀
  visit : β₀ tL = R
  lift_zero : γ 0 = 0
  head : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R
  tail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x
  ray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x

/-- The run inputs from relative stage `2` (actual stage `2 + o`) to `N` (`stepData_of_inputs`, with the lift
relation as the piece datum). -/
structure RunInputs (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o N : ℕ) : Prop where
  cont : ContinuousOn ι (Ici R)
  reg₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
  reg₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂
  fin₁ : ∀ j, j + 1 < N + o →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤
  fin₂ : ∀ j, j + 1 < N →
    (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂ j).2 ≠ ⊤
  lm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j
  lh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j
  lm₂ : ∀ j, NoLeftMove κ b₂ J₂ θ D₂ j
  lh₂ : ∀ j, NoLeftHit κ b₂ J₂ θ D₂ j
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

/-- The start on an actual connector (`range_eq_physSet_of_inputs_arc`). -/
structure ArcStart (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (β₀ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o : ℕ) : Prop where
  even : o % 2 = 0
  len : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length
  move : ExplState.contStep κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) none
      true =
    if hC : (restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).Nonempty then
      ExplState.moveAlong (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true
        ((restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).min' hC) true
    else ExplState.moveToEnd (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) true
  angle : stAngle (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) = θ
  pt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≤ R
  recLe : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≤ R
  gap : ∀ x ∈ restartSet κ b₁ J₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)), R < x
  low : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ
  reg₀ : IsRegularDriver (D₂ 0)
  zero₀ : (D₂ 0).2 = 0
  nz₁ : ∀ k, 2 + o ≤ k →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0
  head : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ⊆ β₀ '' Iic tL

/-- The start on an actual piece (`range_eq_physSet_of_inputs_piece`). -/
structure PieceStart (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o : ℕ) : Prop where
  even : o % 2 = 0
  launch : ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1) =
    ExplState.launch (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) o (D₁ o) θ ⊤
  tip : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≠ .inr (.inl ())
  pt : stPt (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R
  recLe : stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ≤ R
  top : (D₂ 0).2 = ⊤ ↔ (D₁ o).2 = ⊤
  zero : (D₂ 0).2 = 0 ↔ (D₁ o).2 = 0
  hitR : (∃ x : ℝ, 0 < x ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x) ↔
    ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) < x ∧
      lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o)) ⊤ (D₁ o) x
  hitL₂ : ¬ ∃ x : ℝ, x < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D₂ 0) x
  recR : (D₁ o).2 ≠ ⊤ → lRecR (ExplState.init 0) ⊤ (D₂ 0) =
    ι (max (lRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊤ (D₁ o)) R)
  lift₀ : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o))
    (newPc (ExplState.init 0) (D₂ 0))
  memR : (R : ℂ) ∈ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).1.tipSet
    (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.1
    (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) (D₁ o)).2.2
  recAfter : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))
  nz₁ : ∀ k, o ≤ k →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0
  len : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧ 1 < (boundaryWalkSpec b₂ J₂ θ true).2.2.length
  head : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊆ β₀ '' Iic tL

end Bundles

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o N : ℕ}

/-- **The range identity at one sample from the bundles.** -/
theorem range_eq_physSet_of_bundles (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputs κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStart κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  rcases hS with hA | hP
  · exact range_eq_physSet_of_inputs_arc hι hR.cont hA.even hA.len hA.move hA.angle hA.pt hA.recLe hA.gap hA.low
      hA.reg₀ hA.zero₀ hR.reg₁ hR.reg₂ hR.fin₁ hR.fin₂ hR.lm₁ hR.lh₁ hR.lm₂ hR.lh₂ hA.nz₁ hR.L1 hR.fill hR.piece
      hR.two_le hR.len hR.len₁ hR.len₂ hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hA.head
  · refine range_eq_physSet_of_inputs_piece hι hR.cont hP.even hP.launch hP.tip hP.pt hP.recLe hP.top hP.zero hP.hitR
      hP.hitL₂ hP.recR hP.lift₀ hP.memR hP.recAfter hR.reg₁ hR.reg₂ hR.fin₁ hR.fin₂ hR.lm₁ hR.lh₁ hR.lm₂ hR.lh₂
      hP.nz₁ hR.L1 hR.fill hR.piece hR.two_le ?_ hR.len₁ hR.len₂ hR.done hC.range_eq hC.inj hC.visit hC.lift_zero
      hC.head hC.tail hC.ray hP.head
    intro i hi hiN
    rcases eq_or_lt_of_le hi with h1 | h2
    · subst h1
      exact ⟨by have := hP.len.1; omega, hP.len.2⟩
    · exact hR.len i h2 hiN


/-! ### The almost-sure assembly -/

/-- **The head of the actual walk has real points `≤ R`, almost surely under the retained kernel** (Lemma S2
reflected, `head_real_le_of_s2`, with the path of the upper prefix and its avoidance of the lower walk's right side, as
in `sb2LowerTailLiftCurve`). -/
theorem sb2LowerHead :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
          ∀ tL : ℝ≥0, β₀ tL = realMax (upperPrefix κ b jumps E u l k ω₀) →
            ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ realMax (upperPrefix κ b jumps E u l k ω₀) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hEu := hE _ hsp
  have hRu := hER _ hsp
  have hm𝒢 := hEu.2.1 k
  have hleftQ := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢 hleft
  have hrunQ := Retain.ae_ae_run_eq (upperSpec u l) hRu hm𝒢 le_rfl
  filter_upwards [hleftQ, hrunQ, hRu] with ω₀ hleft₀ hrun₀ hR₀
  intro c θ hlaunch b' J' h' hb' hT' hG'
  have hreg₀ : ∀ (j : ℕ) (c' : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (upperSpec u l) (fun i => E (upperSpec u l) i ω₀) (j + 1)).2.2.2.1 j =
        some (c', θ') →
      GW1P.PieceRegular (E (upperSpec u l) j ω₀).1 (min (instrTime (upperSpec u l) j) (E (upperSpec u l) j ω₀).2) :=
    fun j c' θ' hl' => hR₀ j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl'
  obtain ⟨pA, hp, hp0, hpH, hpA, hcl⟩ :=
    Lf.exists_path_upperPrefix (κ := κ) (b := b) (jumps := jumps) hu l (fun j => E (upperSpec u l) j ω₀) hreg₀ k
  have hpA' : pA '' Icc 0 1 = upperPrefix κ b jumps E u l k ω₀ := hpA
  filter_upwards [hrun₀, hleft₀] with ω hω hleftω
  intro β₀ hβ hβ0 hβr tL hβL
  have hlaunchω : ω ∈ upperLaunchSet κ b jumps E u l k := by
    show (ExplState.run κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none
    rw [launches_run_succ_of_run_eq (upperSpec u l) hω, hlaunch]
    exact Option.some_ne_none _
  have hAω : upperPrefix κ b jumps E u l k ω = upperPrefix κ b jumps E u l k ω₀ := by
    show prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0 =
      prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∪ ((↑) : ℝ → ℂ) '' Icc u 0
    unfold prefixPhysSet; rw [hω]
  have hav := hleftω hlaunchω
  rw [hAω] at hav
  have hav' : prefixPhysSet κ b jumps (upperSpec u l) (fun j => E (upperSpec u l) j ω₀) k ∩
      rightSideOf (range β₀) = ∅ := by
    rw [hβr]
    exact eq_empty_of_subset_empty ((inter_subset_inter_left _ subset_union_left).trans hav.subset)
  have hAL : upperPrefix κ b jumps E u l k ω₀ ⊆ closedLeftSide β₀ :=
    Lf.subset_closedLeftSide_of_avoid hβ hβ0 hcl hav'
  rw [← hpA'] at hAL hβL ⊢
  exact head_real_le_of_s2 hp hp0 hpH hβ hβ0 hAL hβL

/-- **The relative-driver data at one launch** (`RelWalkRange`'s quantifiers, with the per-sample bundles in place of
the range identity): a measurable family `EL`, regular at every sample, such that almost surely under the retained
kernel, for every proper parametrization `β₀` of the actual lower walk and every lift curve `γ` of its tail, there are
a ray correspondence `ι`, a start offset `o` and a final stage `N` with the head/tail/ray facts, the run inputs and one
of the two starts. -/
def RelDriverAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
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
            RunInputs κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o N ∧
            (ArcStart κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ tL o ∨
              PieceStart κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)

/-- **Named input: SB2(2)'s relative-driver data at the later launches** (the construction of `EL` with the per-sample
facts of both walks). -/
def SB2LowerRelDriverStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverAt κ b jumps P E u l k ω₀ c b' J'

/-- **The range identity of SB2(2)'s lifted walk from the relative-driver data** (`SB2LowerRelWalkRangeStatement`,
SB2LIFT §R7.2): at every sample the one-sample theorem `range_eq_physSet_of_bundles` applies. -/
theorem sb2LowerRelWalkRangeStatement_of_relDriver (hD : SB2LowerRelDriverStatement.{u}) :
    SB2LowerRelWalkRangeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀ hH₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hm1, hm2, hae⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  refine ⟨EL, hm1, hm2, ?_⟩
  filter_upwards [hae, hH₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hHω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, o, N, hι, htail, hray, hR, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  exact range_eq_physSet_of_bundles hι ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hHω β₀ hβ hβ0 hβr tL hγ.1, htail, hray⟩ hR hS

/-- **SB2(2)'s combined target (R104a) from the relative-driver data and the conditional half** (and Theorems
1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_relDriver (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverStatement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_range h12 h13 h12₀ h13₀ (sb2LowerRelWalkRangeStatement_of_relDriver hD) hcond

end InteractingSLE.Theorem14.SB.Lk
