/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WqAE
import InteractingSLE.Spec.Supplement.SB2JiData2

/-!
# SB2(2): the reduced relative-driver input, v2 (the record clause only at a finite start piece)

Packet PROVE-SB2-LIFTSET (round 14). SB2LIFT's reduced input `SB2LowerRelDriverStatement'` (`SB2WqAE`: `RunInputs'`,
without the relative `fin₂`, `lm₂`, `lh₂`) still uses `PieceStart` with the unconditional `recAfter`, which can fail
at an infinite start piece (finding §R13.1). The v2 form:

* **`range_eq_physSet_of_bundlesV2`**: the range identity at one sample from `CurveInputs`, `RunInputs'`, the two
  actual-walk facts and an arc start or a v2 piece start with its head inclusion — finite start piece by SB2LIFT's
  `range_eq_physSet_of_bundles'`, infinite start piece by `range_eq_physSet_of_piece_top`;
* `RelDriverV2At`, **`SB2LowerRelDriverV2Statement`** (named input), `sb2LowerRelDriverV2Statement_of_relDriver'`
  (SB2LIFT's statement gives it); **`sb2LowerRelWalkRangeStatement_of_relDriverV2`**,
  **`sb2LowerLaunchLiftStatement_of_relDriverV2`** (via `sb2LowerLaunchLiftStatement_of_range`);
* head-free: `RelDataClauseV2`, `RelDriverDataV2At`, **`SB2LowerRelDriverDataV2Statement`**,
  `sb2LowerRelDriverV2Statement_of_dataV2` (heads by `head_of_arcStart`, `head_of_pieceStart` from GW1's chain
  facts), **`sb2LowerRelWalkRangeStatement_of_dataV2`**, **`sb2LowerLaunchLiftStatement_of_dataV2`** (Theorems
  1.2–1.3 for the chain facts and SB2LIFT's a.s. actual-walk facts).
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

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o N : ℕ}

/-- **The range identity at one sample, v2** (reduced run inputs; the record clause only at a finite start piece). -/
theorem range_eq_physSet_of_bundlesV2 (hι : RayCorr b₁ J₁ b₂ J₂ R ι)
    (hC : CurveInputs κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hR : RunInputs' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hallow : ∀ k, 2 + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ ⊤ →
      (D₁ k).2 ≠ 0 → ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧
        lHit (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨
      (PieceStartData2 κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧
        statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ o) ⊆ β₀ '' Iic tL)) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  rcases hS with hA | ⟨hP, hhd⟩
  · exact range_eq_physSet_of_bundles' hι hC hR hreg₂ hallow hexit₁ (Or.inl hA)
  · by_cases htop : (D₁ o).2 = ⊤
    · have hl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
        rw [hP.launch, launches_launch, Function.update_self]
        exact Option.some_ne_none _
      refine range_eq_physSet_of_piece_top hι hP.even hP.launch htop hP.tip hP.pt hP.recLe hP.top hP.zero hP.hitR
        (hR.lh₁ o hl) hP.hitL₂ hP.lift₀ hP.memR (by have := hR.two_le; omega) ?_ hR.len₁ hR.len₂ hC.range_eq
        hC.inj hC.visit hC.lift_zero hC.head hC.tail hC.ray hhd
      intro i hi hiN
      rcases eq_or_lt_of_le hi with h1 | h2
      · subst h1
        exact ⟨by have := hP.len.1; omega, hP.len.2⟩
      · exact hR.len i h2 hiN
    · exact range_eq_physSet_of_bundles' hι hC hR hreg₂ hallow hexit₁
        (Or.inr { hP with recAfter := hP.recAfter htop, head := hhd })

/-- **The reduced relative-driver data at one launch, v2** (`RelDriverAt'` with the v2 piece start). -/
def RelDriverV2At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
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
              (PieceStartData2 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o ∧
                statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
                  (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) o) ⊆ β₀ '' Iic tL))

/-- **Named input: SB2(2)'s reduced relative-driver data, v2.** -/
def SB2LowerRelDriverV2Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverV2At κ b jumps P E u l k ω₀ c b' J'

/-- SB2LIFT's reduced statement gives the v2 one. -/
theorem sb2LowerRelDriverV2Statement_of_relDriver' (hD : SB2LowerRelDriverStatement'.{u}) :
    SB2LowerRelDriverV2Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hm1, hm2, hae⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  refine ⟨EL, hm1, hm2, ?_⟩
  filter_upwards [hae] with ω hω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, o, N, hι, htail, hray, hR, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  exact ⟨ι, o, N, hι, htail, hray, hR, hS.imp id fun hP => ⟨pieceStartData2_of_data
    { hP with }, hP.head⟩⟩

/-- **SB2(2)'s range statement from the reduced v2 data** (Theorem 1.3 at universe `0`). -/
theorem sb2LowerRelWalkRangeStatement_of_relDriverV2 (h13₀ : Exist.Theorem13Statement.{0})
    (hD : SB2LowerRelDriverV2Statement.{u}) : SB2LowerRelWalkRangeStatement.{u} := by
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
  exact range_eq_physSet_of_bundlesV2 hι ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hHω β₀ hβ hβ0 hβr tL hγ.1, htail, hray⟩ hR
    (fun j => hm2 j ω) (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hS

/-- **SB2(2)'s combined target (R104a) from the reduced v2 data** (and Theorems 1.2–1.3). -/
theorem sb2LowerLaunchLiftStatement_of_relDriverV2 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverV2Statement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_range h12 h13 h12₀ h13₀ (sb2LowerRelWalkRangeStatement_of_relDriverV2 h13₀ hD) hcond

/-! ### Head-free -/

/-- **The per-sample data clause, reduced v2** (`RunInputs'`, `ArcStartData ∨ PieceStartData2`). -/
def RelDataClauseV2 (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
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
          RunInputs' κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
            (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o N ∧
          (ArcStartData κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) o ∨
            PieceStartData2 κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)

/-- **The head-free reduced relative-driver data at one launch, v2.** -/
def RelDriverDataV2At (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
      RelDataClauseV2 κ b jumps P E u l k ω₀ c b' J' m EL

/-- **Named input: SB2(2)'s head-free reduced relative-driver data, v2.** -/
def SB2LowerRelDriverDataV2Statement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverDataV2At κ b jumps P E u l k ω₀ c b' J'

/-- **The head inclusions from GW1's chain facts**: the head-free v2 data give the v2 data. -/
theorem sb2LowerRelDriverV2Statement_of_dataV2 (hD : SB2LowerRelDriverDataV2Statement.{u})
    (hW : SB2LowerChainStatement.{u}) : SB2LowerRelDriverV2Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    hW κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀ hW₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hm1, hm2, hae⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  refine ⟨EL, hm1, hm2, ?_⟩
  filter_upwards [hae, hW₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hω hWω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, o, N, hι, htail, hray, hR, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  refine ⟨ι, o, N, hι, htail, hray, hR, ?_⟩
  rcases hS with hA | hP
  · exact Or.inl { hA with
      head := head_of_arcStart hWω.1 hWω.2 hR.len₁ hR.done hβ hβ0 hβr hγ.1 (by have := hR.two_le; omega) hA.len
        (by have := hA.even; omega) hA.move hA.pt hA.gap }
  · exact Or.inr ⟨hP, head_of_pieceStart hWω.1 hWω.2 hR.len₁ hR.done hβ hβ0 hβr hγ.1 (by omega) hP.launch hP.memR⟩

/-- **SB2(2)'s range statement from the head-free reduced v2 data** (Theorems 1.2–1.3 for GW1's chain facts and
SB2LIFT's actual-walk facts). -/
theorem sb2LowerRelWalkRangeStatement_of_dataV2 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverDataV2Statement.{u}) :
    SB2LowerRelWalkRangeStatement.{u} :=
  sb2LowerRelWalkRangeStatement_of_relDriverV2 h13₀
    (sb2LowerRelDriverV2Statement_of_dataV2 hD (sb2LowerChainStatement_of_thm12_thm13 h12 h13 h12₀ h13₀))

/-- **SB2(2)'s combined target (R104a) from the head-free reduced v2 data and the conditional half.** -/
theorem sb2LowerLaunchLiftStatement_of_dataV2 (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverDataV2Statement.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_range h12 h13 h12₀ h13₀ (sb2LowerRelWalkRangeStatement_of_dataV2 h12 h13 h12₀ h13₀ hD)
    hcond

end InteractingSLE.Theorem14.SB.Lk
