/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LoHead

/-!
# SB2(2)'s almost-sure assembly without the head inclusion

Packet PROVE-SB2-LIFTSET (round 3). The start bundles `ArcStart`, `PieceStart` of `SB2LpAE` contain the head inclusion
(the actual prefix before the start lies on `β₀ '' [0, t_L]`). `SB2LoHead` proves it from GW1's per-step facts. Here:

* `ArcStartData`, `PieceStartData`: the start bundles without `head`; **`WalkChainFacts`**: GW1's per-step facts for a
  right walk (piece simplicity at launches, connector clearance — the hypotheses of `GW1WalkChain.walkChain
  Representation_of_pieceSimpleAt`); **`arcStart_of_data`**, **`pieceStart_of_data`**: the full bundles;
* **`SB2LowerChainStatement`** (named input): `WalkChainFacts` for the lower walk almost surely under the retained
  kernel (a consequence of GW1's landed `GW1Z.GW1PieceSimpleStatement`, `WalkTipCoordinatesStatement`,
  `WalkConnectorClearanceStatement` for everywhere regular families, transported to staged families and to the
  kernel — see the handoff);
* **`SB2LowerRelDriverDataStatement`** (named input, `RelDriverAt` without the head inclusion);
  **`sb2LowerRelDriverStatement_of_data`**, **`sb2LowerRelWalkRangeStatement_of_data`**.
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

/-- The start on an actual connector without the head inclusion (`ArcStart` minus `head`). -/
structure ArcStartData (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (R : ℝ) (D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (o : ℕ) :
    Prop where
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

/-- The start on an actual piece without the head inclusion (`PieceStart` minus `head`). -/
structure PieceStartData (κ θ : ℝ) (b₁ : ℝ → ℝ) (J₁ : Finset ℝ) (b₂ : ℝ → ℝ) (J₂ : Finset ℝ) (R : ℝ) (ι : ℝ → ℝ)
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


/-- **GW1's per-step facts for a right walk** (the hypotheses of `GW1WalkChain.walkChainRepresentation_of_
pieceSimpleAt`): every launched piece meets the retained physical part only at its seed, every connector clears it. -/
def WalkChainFacts (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  (∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k = some (c, θ') →
      (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) : ℂ) ∈
        statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) →
      PieceSimpleAt c (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ true) k) (D k).2)
        (statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k))
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)))) ∧
    GW1WalkChain.WalkConnectorClearance (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ true) D

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
  {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {o N : ℕ}

/-- **The arc start with its head inclusion** from GW1's per-step facts (`head_of_arcStart`). -/
theorem arcStart_of_data (hW : WalkChainFacts κ b₁ J₁ θ D₁) (hA : ArcStartData κ θ b₁ J₁ R D₁ D₂ o)
    (hR : RunInputs κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβL : β₀ tL = R) :
    ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o :=
  { hA with
    head := head_of_arcStart hW.1 hW.2 hR.len₁ hR.done hβ hβ0 hβr hβL (by have := hR.two_le; omega) hA.len
      (by have := hA.even; omega) hA.move hA.pt hA.gap }

/-- **The piece start with its head inclusion** from GW1's per-step facts (`head_of_pieceStart`). -/
theorem pieceStart_of_data (hW : WalkChainFacts κ b₁ J₁ θ D₁)
    (hP : PieceStartData κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o)
    (hR : RunInputs κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o N) (hβ : IsProperCurve β₀) (hβ0 : β₀ 0 = 0)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβL : β₀ tL = R) :
    PieceStart κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o :=
  { hP with
    head := head_of_pieceStart hW.1 hW.2 hR.len₁ hR.done hβ hβ0 hβr hβL (by omega) hP.launch hP.memR }


/-! ### The almost-sure assembly without the head inclusion -/

/-- **Named input: GW1's per-step facts for the lower walk, almost surely under the retained kernel.** -/
def SB2LowerChainStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ _ _ _ _ =>
    ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
      WalkChainFacts κ b jumps (-(Real.pi / 2)) (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)

/-- **The relative-driver data at one launch, without the head inclusion** (`RelDriverAt` with `ArcStartData`,
`PieceStartData`). -/
def RelDriverDataAt (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
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
            (ArcStartData κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω₀))
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) o ∨
              PieceStartData κ (-(Real.pi / 2)) b jumps (affData 1 m b') (affJumps 1 m J')
                (realMax (upperPrefix κ b jumps E u l k ω₀)) ι
                (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (fun j => EL j ω) β₀ γ tL o)

/-- **Named input: SB2(2)'s relative-driver data without the head inclusion.** -/
def SB2LowerRelDriverDataStatement : Prop :=
  Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c b' J' _ =>
    0 < k → RelDriverDataAt κ b jumps P E u l k ω₀ c b' J'

/-- **The head-free data and GW1's chain facts give the relative-driver data** (the head inclusions by
`arcStart_of_data`, `pieceStart_of_data`). -/
theorem sb2LowerRelDriverStatement_of_data (hD : SB2LowerRelDriverDataStatement.{u})
    (hW : SB2LowerChainStatement.{u}) : SB2LowerRelDriverStatement.{u} := by
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
  · exact Or.inl (arcStart_of_data hWω hA hR hβ hβ0 hβr hγ.1)
  · exact Or.inr (pieceStart_of_data hWω hP hR hβ hβ0 hβr hγ.1)

/-- **The range identity of SB2(2)'s lifted walk from the head-free data and GW1's chain facts.** -/
theorem sb2LowerRelWalkRangeStatement_of_data (hD : SB2LowerRelDriverDataStatement.{u})
    (hW : SB2LowerChainStatement.{u}) : SB2LowerRelWalkRangeStatement.{u} :=
  sb2LowerRelWalkRangeStatement_of_relDriver (sb2LowerRelDriverStatement_of_data hD hW)

end InteractingSLE.Theorem14.SB.Lk
