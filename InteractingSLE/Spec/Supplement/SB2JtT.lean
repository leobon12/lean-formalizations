/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XbAE
import InteractingSLE.Spec.Supplement.SB2MaSet

/-!
# SB2(2): D7's target corrected at an infinite start piece

Packet PROVE-SB2-LIFTSET (round 16). **Finding (rule 1a) on D7's target `SB2LowerRelDriverStatement''`
(`SB2XbAE`).** Its run bundle `RunInputs'' … o N` has `two_le : 2 ≤ N` and
`fin₁ : ∀ j, j + 1 < N + o → launched j → (D₁ j).2 ≠ ⊤`; at a piece start (`PieceStartV`, launched at `o`) with an
infinite start piece, `j = o` gives `(D₁ o).2 ≠ ⊤`, a contradiction — no `N` works, although `PieceStartV` itself allows
the infinite case and `range_eq_physSet_of_bundles''` handles it. Pure piece entries have positive probability (D6),
and their start piece can be the last, infinite piece; so the statement is false on that event unless it is null.
**Corrected statement:** the bundle is asked only off that event; there only `PieceStartV` with `(D₁ o).2 = ⊤`:

* `RelDriverAtT`, **`SB2LowerRelDriverStatementT`**, `sb2LowerRelDriverStatementT_of_relDriver''` (`''` gives `T`);
* **`range_eq_physSet_of_topV`** (one sample: `range_eq_physSet_of_piece_top` with `N = 1`, `NoLeftHit` almost sure);
* **`sb2LowerRelWalkRangeStatement_of_relDriverT`**, **`sb2LowerLaunchLiftStatement_of_relDriverT`** (Theorems
  1.2–1.3, as for `''`).
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
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o : ℕ}

/-- **The range identity at one sample at an infinite start piece** (`PieceStartV`, `N = 1`). -/
theorem range_eq_physSet_of_topV (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hC : CurveInputs κ θ b₁ J₁ R ι D₁ β₀ γ tL)
    (hP : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) (htop : (D₁ o).2 = ⊤)
    (hlh : NoLeftHit κ b₁ J₁ θ D₁ o) :
    range γ = ExplState.physSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  have hl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
    rw [hP.launch, launches_launch, Function.update_self]; simp
  exact range_eq_physSet_of_piece_top hι (N := 1) hP.even hP.launch htop hP.tip hP.pt hP.recLe hP.top hP.zero
    hP.hitR (hlh hl) hP.hitL₂ hP.lift₀ hP.memR le_rfl (fun i hi hiN => absurd hiN (by omega))
    (by have := hP.len.1; omega) (by have := hP.len.2; omega) hC.range_eq hC.inj hC.visit hC.lift_zero hC.head
    hC.tail hC.ray hP.head

/-- **The relative-driver data at one launch from the lifts, corrected at an infinite start piece**: `RelDriverAt''`
with the run bundle asked only off the infinite-start-piece event. -/
def RelDriverAtT (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ)
    (l : List (ℝ × ℝ≥0)) (k : ℕ) (ω₀ : Ω) (c : Chart) (b' : ℝ → ℝ) (J' : Finset ℝ) : Prop :=
  ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ → ∃ EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
    (∀ j, Measurable (EL j)) ∧ (∀ j ω, IsRegularDriver (EL j ω)) ∧
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      ∀ β₀ : ℝ≥0 → ℂ, IsProperCurve β₀ → β₀ 0 = 0 → range β₀ = lowerWalkSet κ b jumps E ω →
        ∀ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ), IsTailLiftCurve c (realMax (upperPrefix κ b jumps E u l k ω₀)) m β₀ tL γ →
          ∃ (ι : ℝ → ℝ) (o : ℕ),
            RayCorr b jumps (affData 1 m b') (affJumps 1 m J') (realMax (upperPrefix κ b jumps E u l k ω₀)) ι ∧
            RayChartLim c (realMax (upperPrefix κ b jumps E u l k ω₀)) m ι ∧
            (∀ s, ∀ x : ℝ, β₀ (tL + s) = x → realMax (upperPrefix κ b jumps E u l k ω₀) ≤ x) ∧
            (∀ s, ∀ x : ℝ, realMax (upperPrefix κ b jumps E u l k ω₀) < x → β₀ (tL + s) = x → γ s = ι x) ∧
            ((∃ N : ℕ, RunInputs'' κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
              (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
              (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o N ∧
            (ArcStart κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ tL o ∨
              PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)) ∨
            (PieceStartV κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o ∧
              (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) o ω).2 = ⊤))

/-- **Named input: SB2(2)'s relative-driver data from the lifts, corrected at an infinite start piece.** -/
def SB2LowerRelDriverStatementT : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverAtT κ b jumps P E u l k ω₀ c b' J'

/-- D7's statement gives the corrected one. -/
theorem sb2LowerRelDriverStatementT_of_relDriver'' (hD : SB2LowerRelDriverStatement''.{u}) :
    SB2LowerRelDriverStatementT.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [hD κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft] with ω₀ h₀
  intro c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  obtain ⟨EL, hm1, hm2, hae⟩ := h₀ c θ hlaunch b' J' h' hb' hT' hG' hk m hm
  refine ⟨EL, hm1, hm2, ?_⟩
  filter_upwards [hae] with ω hω
  intro β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨ι, o, N, hι, hlim, htail, hray, hR, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  exact ⟨ι, o, hι, hlim, htail, hray, Or.inl ⟨N, hR, hS⟩⟩

/-- **SB2(2)'s range statement from the corrected relative-driver data** (Theorems 1.2–1.3). -/
theorem sb2LowerRelWalkRangeStatement_of_relDriverT (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverStatementT.{u}) :
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
  obtain ⟨ι, o, hι, hlim, htail, hray, hS⟩ := hω β₀ hβ hβ0 hβr tL γ hγ
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  have hhead := hHω β₀ hβ hβ0 hβr tL hγ.1
  have hC : CurveInputs κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) β₀ γ tL :=
    ⟨hβr, hβ.2.1, hγ.1, hγ.2.2.1, hhead, htail, hray⟩
  rcases hS with ⟨N, hR, hS⟩ | ⟨hP, htop⟩
  · have hD : LiftCurveData β₀ γ tL (realMax (upperPrefix κ b jumps E u l k ω₀)) ι :=
      ⟨hβ.1, hβ.2.2.1, hγ.2.1.1, hγ.2.1.2.2.1, hγ.1, hγ.2.2.1,
        fun t ht him => hhead t ht _ (Complex.ext (by simp) (by simp [him])), hray, back_of_rayChartLim hγ hlim⟩
    exact range_eq_physSet_of_bundles'' hι hC hR (fun j => hm2 j ω) hP₁ hW₁ (fun j => (hn j).1)
      (fun j => (hn j).2.1) (fun j hj => hAω j (by omega)) (fun j _ => hXω j) hβ hγ.2.1 hβ0 hD hS
  · exact range_eq_physSet_of_topV hι hC hP htop (hn o).2.1

/-- **SB2(2)'s combined target (R104a) from the corrected relative-driver data and the conditional half.** -/
theorem sb2LowerLaunchLiftStatement_of_relDriverT (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hD : SB2LowerRelDriverStatementT.{u})
    (hcond : SB2LowerRelStageCondStatement.{u}) : Lh.SB2LowerLaunchLiftStatement.{u} :=
  sb2LowerLaunchLiftStatement_of_range h12 h13 h12₀ h13₀
    (sb2LowerRelWalkRangeStatement_of_relDriverT h12 h13 h12₀ h13₀ hD) hcond

end InteractingSLE.Theorem14.SB.Lk
