/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LaEL

/-!
# SB2(2): the relative-driver data, v2 — the record clause only at a finite start piece

Packet PROVE-SB2-LIFTSET (round 13). **Correction of the landed data statements** (finding of §R7.2/§R8.2):
`PieceStartData` (`SB2LoAE`) asks for `recAfter : R ≤ stRecR (run (o + 1))` unconditionally, which can fail when the
start piece has infinite lifetime (the walk is then done after it and its record need not reach `R`). Then
`SB2LowerRelDriverDataStatement` — and every named input concluding `RelDataClause` — can be false on that event. The
v2 statements ask for `recAfter` only at finite lifetime and dispatch the infinite case to
`range_eq_physSet_of_piece_top` (`SB2LbPiece`), which needs no record clause:

* **`PieceStartData2`** (`recAfter` only when `(D₁ o).2 ≠ ⊤`), `pieceStartData2_of_data` (v1 gives v2);
* **`range_eq_physSet_of_data2`**: the range identity at one sample from the head-free data (arc start, or piece start
  v2), GW1's chain facts, the head/tail/ray facts and the run inputs;
* **`RelDataClause2`**, `relDataClause2_of_clause`, **`RelDriverData2At`**, **`SB2LowerRelDriverData2Statement`**
  (named input, implied by the v1 statement: `sb2LowerRelDriverData2Statement_of_data`);
* **`sb2LowerRelWalkRangeStatement_of_data2`**, `sb2LowerLaunchLiftStatement_of_data2` (and Theorems 1.2–1.3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

/-- **The start on an actual piece, v2**: `PieceStartData` with the record clause `recAfter` only at finite lifetime
of the start piece. -/
structure PieceStartData2 (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
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



variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o N : ℕ}

/-- The v1 piece-start data give the v2 ones. -/
theorem pieceStartData2_of_data (h : PieceStartData κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    PieceStartData2 κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o :=
  { h with recAfter := fun _ => h.recAfter }

/-- **The range identity at one sample from the head-free data, v2**: an arc start, a piece start of finite lifetime
(`range_eq_physSet_of_bundles` with the head inclusion `head_of_pieceStart`), or a piece start of infinite lifetime
(`range_eq_physSet_of_piece_top`: no record clause, no later step data). -/
theorem range_eq_physSet_of_data2 (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hW : WalkChainFacts κ b₁ J₁ θ D₁)
    (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβL : β₀ tL = R)
    (hγ0 : γ 0 = 0) (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R)
    (htail : ∀ s, ∀ x : ℝ, β₀ (tL + s) = x → R ≤ x) (hray : ∀ s, ∀ x : ℝ, R < x → β₀ (tL + s) = x → γ s = ι x)
    (hR : RunInputs κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N)
    (hS : ArcStartData κ θ b₁ J₁ R D₁ D₂ o ∨ PieceStartData2 κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  have hC : CurveInputs κ θ b₁ J₁ R ι D₁ β₀ γ tL := ⟨hβr, hβ.2.1, hβL, hγ0, hhead, htail, hray⟩
  rcases hS with hA | hP
  · exact range_eq_physSet_of_bundles hι hC hR (Or.inl (arcStart_of_data hW hA hR hβ hβ0 hβr hβL))
  · have hhd := head_of_pieceStart hW.1 hW.2 hR.len₁ hR.done hβ hβ0 hβr hβL (by omega) hP.launch hP.memR
    by_cases htop : (D₁ o).2 = ⊤
    · have hl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
        rw [hP.launch, launches_launch, Function.update_self]
        exact Option.some_ne_none _
      refine range_eq_physSet_of_piece_top hι hP.even hP.launch htop hP.tip hP.pt hP.recLe hP.top hP.zero hP.hitR
        (hR.lh₁ o hl) hP.hitL₂ hP.lift₀ hP.memR (by have := hR.two_le; omega) ?_ hR.len₁ hR.len₂ hβr hβ.2.1 hβL
        hγ0 hhead htail hray hhd
      intro i hi hiN
      rcases eq_or_lt_of_le hi with h1 | h2
      · subst h1
        exact ⟨by have := hP.len.1; omega, hP.len.2⟩
      · exact hR.len i h2 hiN
    · exact range_eq_physSet_of_bundles hι hC hR (Or.inr { hP with recAfter := hP.recAfter htop, head := hhd })

universe u

open Supp9B Lx Lu Leaf FlowDilate Sec4 LuM GW1W GW1Bookkeep in
/-- **The per-sample data clause, v2**: `RelDataClause` with `PieceStartData2` (the record clause `recAfter` only at
finite lifetime of the start piece). -/
def RelDataClause2 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
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
            PieceStartData2 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)


/-- The v1 clause gives the v2 clause. -/
theorem relDataClause2_of_clause {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k : ℕ} {ω₀ : Ω} {c : Chart} {b' : ℝ → ℝ} {J' : Finset ℝ} {m : ℝ}
    {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (h : RelDataClause κ b jumps P E u l k ω₀ c b' J' m EL) :
    RelDataClause2 κ b jumps P E u l k ω₀ c b' J' m EL := by
  filter_upwards [h] with ω hω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, o, N, hι, htail, hray, hR, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  exact ⟨ι, o, N, hι, htail, hray, hR, hS.imp id pieceStartData2_of_data⟩

/-- **The relative-driver data at one launch, v2.** -/
def RelDriverData2At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      RelDataClause2 κ b jumps P E u l k ω₀ c b' J' m EL

/-- **Named input: SB2(2)'s relative-driver data without the head inclusion, v2** (the record clause only at a finite
start piece). -/
def SB2LowerRelDriverData2Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverData2At κ b jumps P E u l k ω₀ c b' J'

/-- The v1 statement gives the v2 statement. -/
theorem sb2LowerRelDriverData2Statement_of_data (hD : SB2LowerRelDriverDataStatement.{u}) :
    SB2LowerRelDriverData2Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, h1, h2, h3⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  exact ⟨EL, h1, h2, relDataClause2_of_clause h3⟩

/-- **The range identity of SB2(2)'s lifted walk from the v2 data and GW1's chain facts.** -/
theorem sb2LowerRelWalkRangeStatement_of_data2 (hD : SB2LowerRelDriverData2Statement.{u})
    (hW : SB2LowerChainStatement.{u}) : SB2LowerRelWalkRangeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHead κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀ hW₀ hH₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hm1, hm2, hae⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  refine ⟨EL, hm1, hm2, ?_⟩
  filter_upwards [hae, hW₀ c θ hlaunch b' J' h' hb' hT' hG', hH₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hWω hHω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, o, N, hι, htail, hray, hR, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  exact range_eq_physSet_of_data2 hι hWω hβ hβ0 hβr hγ.1 hγ.2.2.1 (hHω β₀ hβ hβ0 hβr tL hγ.1) htail hray hR hS

/-- **SB2(2)'s combined target (R104a) from the v2 data and the conditional half** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_data2 (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hD : SB2LowerRelDriverData2Statement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_range h12 h13 h12₀ h13₀
    (sb2LowerRelWalkRangeStatement_of_data2 hD (sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀)) hcond

end InteractingSLE.Theorem14.SB.Lk
