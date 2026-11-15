/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XbRange
import InteractingSLE.Spec.Supplement.SB2WqAE
import InteractingSLE.Spec.Supplement.SB2LbPiece

/-!
# SB2(2)'s range statement from the lifts alone, almost surely

Packet PROVE-T14-SB2LIFT (round 23). The named input of round 22, `SB2LowerRelDriverStatement'`, still carried the
launch observables (L1) and `FillCorr` and the actual walk's GW1-type facts in its run bundle `RunInputs'`. Here:

* **`RunInputs''`**: `RunInputs'` without `reg₁`, `lm₁`, `lh₁` (almost sure, `sb2LowerActualInputs`), without `L1`
  and `fill` (derived along the lockstep, `l1_fillCorr_of_lifts`), and with the per-time lift `trLift` of the finite
  pieces (for PROVE-SB2-LIFTSET's concrete rule: `trLift_concrete`);
* **`PieceStartV`**: `PieceStart` with `recAfter` only at a finite start piece (PROVE-SB2-LIFTSET's finding §R13.1);
  an infinite start piece goes to LIFTSET's `range_eq_physSet_of_piece_top`;
* **`range_eq_physSet_of_bundles''`**, **`RelDriverAt''`**, **`SB2LowerRelDriverStatement''`**. Next to `RayCorr`,
  the ray correspondence `ι` now also satisfies `RayChartLim` (the upper chart reads the untouched ray through `ι`,
  as PROVE-SB2-LIFTSET's `rayChartInj_of_continuousWithinAt` already asks through `hĝx`). With it the curve data
  `LiftCurveData` of the fill correspondence (rounds 16–19) are built from the lift curve (`back_of_rayChartLim`);
* **`sb2LowerRelWalkRangeStatement_of_relDriver''`** and **`sb2LowerLaunchLiftStatement_of_relDriver''`**
  (Theorems 1.2–1.3, the reduced input and the conditional half give SB2(2)'s combined target, R104a).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The run inputs from the lifts**: `RunInputs'` without the actual walk's almost-sure GW1-type facts and the
launch observables, with the per-time lift of the finite pieces. -/
structure RunInputs'' (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
    (D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (β₀ γ : ℝ≥0 → ℂ) (tL : ℝ≥0) (o N : ℕ) : Prop where
  cont : ContinuousOn ι (Ici R)
  reg₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂
  fin₁ : ∀ j, j + 1 < N + o → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none →
      (D₁ j).2 ≠ ⊤
  piece : ∀ i, 2 ≤ i → i < N →
    StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i)
  trLift : ∀ i, 2 ≤ i → i < N → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o)
      ≠ none → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
    (D₁ (i + o)).2 ≠ ⊤ →
    (∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ (i + o)) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ i) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) '' (trOf (D₂ i) '' Icc 0
          r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))) '' (trOf
            (D₁ (i + o)) '' Icc 0 r.toNNReal))) ∧
    (∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ i) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ (i + o)) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) '' (trOf (D₂ i) '' Icc 0
          r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))) '' (trOf
            (D₁ (i + o)) '' Icc 0 r.toNNReal)))
  two_le : 2 ≤ N
  len : ∀ i, 2 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
    i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length
  len₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length
  len₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length
  done : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (N + o)) = stDone

/-- **The start on an actual piece, v2**: `PieceStart` with the record clause `recAfter` asked only at a finite
start piece (at an infinite one the walk is done after it; PROVE-SB2-LIFTSET's finding §R13.1). -/
structure PieceStartV (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
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
  recAfter : (D₁ o).2 ≠ ⊤ → R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))
  nz₁ : ∀ k, o ≤ k →
    (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0
  len : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧ 1 < (boundaryWalkSpec b₂ J₂ θ true).2.2.length
  head : statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊆ β₀ '' Iic tL

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o N : ℕ}

/-- A v2 piece start at a finite start piece is a piece start. -/
theorem PieceStartV.toPieceStart (hP : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) (hfin : (D₁ o).2 ≠ ⊤) :
    PieceStart κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o :=
  ⟨hP.even, hP.launch, hP.tip, hP.pt, hP.recLe, hP.top, hP.zero, hP.hitR, hP.hitL₂, hP.recR, hP.lift₀, hP.memR,
    hP.recAfter hfin, hP.nz₁, hP.len, hP.head⟩

/-- **The range identity at one sample from the lifts.** -/
theorem range_eq_physSet_of_bundles'' (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputs κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ ⊤ → (D₁ k).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧ lHit (stChart (ExplState.run
          κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hβp : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ) (hβ0 : β₀ 0 = 0)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨ PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  rcases hS with hA | hPV
  · exact range_eq_physSet_of_lifts_arc hι hR.cont hA.even hA.len hA.move hA.angle hA.pt hA.recLe hA.gap hA.low
      hreg₂ hA.zero₀ hP₁ hR.reg₂ hR.fin₁ hlm₁ hlh₁ hallow hexit₁ hA.nz₁ hR.piece hR.two_le hR.len hR.len₁ hR.len₂
      hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hA.head hW₁ hβp hγp hD hβ0 hR.trLift
  · have hlne : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
      rw [hPV.launch, launches_launch, Function.update_self]; simp
    have hlen' : ∀ i, 1 ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
        i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length := by
      intro i hi hiN
      rcases eq_or_lt_of_le hi with h1 | h2
      · subst h1
        exact ⟨by have := hPV.len.1; omega, hPV.len.2⟩
      · exact hR.len i h2 hiN
    by_cases htop : (D₁ o).2 = ⊤
    · exact range_eq_physSet_of_piece_top hι hPV.even hPV.launch htop hPV.tip hPV.pt hPV.recLe hPV.top hPV.zero
        hPV.hitR (hlh₁ o hlne) hPV.hitL₂ hPV.lift₀ hPV.memR (by have := hR.two_le; omega) hlen' hR.len₁ hR.len₂
        hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hPV.head
    have hP := hPV.toPieceStart htop
    refine range_eq_physSet_of_lifts_piece hι hR.cont hP.even hP.launch hP.tip hP.pt hP.recLe hP.top hP.zero
      hP.hitR hP.hitL₂ hP.recR hP.lift₀ hP.memR hP.recAfter hreg₂ hP₁ hR.reg₂ hR.fin₁ hlm₁ hlh₁ hallow hexit₁
      hP.nz₁ hR.piece hR.two_le ?_ hR.len₁ hR.len₂ hR.done hC.range_eq hC.inj hC.visit hC.lift_zero hC.head hC.tail
      hC.ray hP.head hW₁ hβp hγp hD hβ0 hR.trLift
    exact hlen'

/-- **The relative-driver data at one launch from the lifts** (`RelDriverAt'` with `RunInputs''`). -/
def RelDriverAt'' (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ →
          ∃ (ι : ℝ → ℝ) (o N : ℕ),
            RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (realMax (upperPrefix κ b jumps E u l k ω₀)) ι ∧
            RayChartLim c (realMax (upperPrefix κ b jumps E u l k ω₀)) m ι ∧
            (∀ s, ∀ x : ℝ, β₀ (tL + s) = x → realMax (upperPrefix κ b jumps E u l k ω₀) ≤ x) ∧
            (∀ s, ∀ x : ℝ, realMax (upperPrefix κ b jumps E u l k ω₀) < x → β₀ (tL + s) = x → γ s = ι x) ∧
            RunInputs'' κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o N ∧
            (ArcStart κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ tL o ∨
              PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)

/-- **Named input: SB2(2)'s relative-driver data at the later launches, from the lifts**
(`SB2LowerRelDriverStatement'` with `RunInputs''`). -/
def SB2LowerRelDriverStatement'' : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverAt'' κ b jumps P E u l k ω₀ c b' J'

/-- **SB2(2)'s range statement from the relative-driver data with lifts** (Theorems 1.2–1.3). -/
theorem sb2LowerRelWalkRangeStatement_of_relDriver'' (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverStatement''.{u}) :
    SB2LowerRelWalkRangeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRightHits h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft]
    with ω₀ h₀ hH₀ hA₀ hX₀ hI₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hm1, hm2, hae⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  refine ⟨EL, hm1, hm2, ?_⟩
  filter_upwards [hae, hH₀ c θ hlaunch b' J' h' hb' hT' hG', hA₀ c θ hlaunch b' J' h' hb' hT' hG',
    hX₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hHω hAω hXω hIω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, o, N, hι, hlim, htail, hray, hR, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have hD : LiftCurveData β₀ γ tL (realMax (upperPrefix κ b jumps E u l k ω₀)) ι :=
    ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
      fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
  exact range_eq_physSet_of_bundles'' hι ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hhead, htail, hray⟩ hR
    (fun j => hm2 j ω) hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1) (fun j hj => hAω j (by omega))
    (fun j _ => hXω j) hβ hγ.2.1 hβ0 hD hS

/-- **SB2(2)'s combined target (R104a) from the relative-driver data with lifts and the conditional half** (and
Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_relDriver'' (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverStatement''.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_range h12 h13 h12₀ h13₀
    (sb2LowerRelWalkRangeStatement_of_relDriver'' h12 h13 h12₀ h13₀ hD) hcond

end InteractingSLE.Theorem14.SB.Lk
