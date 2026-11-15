/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallCore
import InteractingSLE.Spec.Sec7.R5RefAmbientCover

/-!
# R.5's split clause-5 cover (ruling R86): the cover on a set of coordinates and its three pieces

Packet PROVE-R5-WALL. Clause 5 of `R5Phase.R5Clauses` (the cover) is stated here on a **selected set of coordinates**
(`R5Cover`, a predicate `S ω ξ`; the full clause is `S = ⊤`, `r5Cover_true_iff`), so that the split of ruling R86 is
the union lemma `R5Cover.of_split`. The three pieces, all with the reference charts' **own** lifts
`liftB i ω = (old i ω).2.2` (the ambient lifts `arg f′_s` of R5-SAMETIME have no limit at the pocket walls, where
the walls are fractal flow lines; the own lifts do):

* **Hull landings** (`r5Cover_hull`): coordinates whose landing lies in the open pocket. From the hull cover
  `R5Ref.R7AmbientCoverHull` (PROVE-R5-REFCHART, reduced to PROVE-R5-LIFT's `R7AmbientLiftWord`) and R5-SAMETIME's
  ambient reference heights, converted to the own lift of the selected reference (`R5Wall.tendsto_refLift_of_lift_sub`:
  `b_own = b_amb + χ d_amb`, `d_own = 0`).
* **Wall coordinates** (`r5Cover_wall`): coordinates outside the open exposed interval `(v_L(q), v_R(q))`. From the
  **initial heights** `R7InitialHeights` (the pocket exterior's mean read in the base chart, at time `0`) through the
  **zero reference** (the base chart itself; `R5Wall.wall_cover_pathwise`): such a coordinate is the image of a
  surviving real point of the incoming walls, whose height and word are transported unchanged.
* **Exposed coordinates landing outside the pocket**: the remaining coordinates (`ξ` in the exposed interval with its
  landing on `∂C`, e.g. boundary pinch points of the relative hull). These are not covered by either half of R86; the
  piece is kept as the explicit premise of the assembly (`R5Cover` on `exposedOuterSel`), and
  `r5Cover_exposedOuter_of_landing` derives it from the pathwise statement `R7ExposedLanding` (non-exceptional exposed
  coordinates land in the pocket).

Conditional helpers with distinct names; no source theorem is replaced. Ruling R48: nothing here uses
Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull chiC)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Wall

open LocalSets WholeField PocketTraversal PocketAdapt Lemma71C PocketStop PocketUnionPt PocketCoupling PocketStopSide
  PhaseSel Aux119Heights PocketWordAssembly PocketSeedOpen PocketCoord PocketJordan R5Phase R5Same PocketStopField
  PocketStopWalls PocketStopWallsFin PocketWordPerQ

variable {Ω : Type*}

/-! ### The cover on a set of coordinates -/

section Defs

variable [MeasurableSpace Ω]

/-- **Clause 5 of `R5Phase.R5Clauses` on the coordinates selected by `S`**: for every version of the reference
means, almost surely on the live test, every real current coordinate `ξ` off the force jumps whose landing avoids `X`
and with `S ω ξ` has a reference `i` with its pair event, an unfilled collar, the transition limit, the reference
height `b`, the lift difference `d` and `b + χ d` equal to the phase-shifted word minus `a`. -/
def R5Cover (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (a : ℝ)
    (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) (C : Ω → Set ℂ) (F : ℕ → Ω → Set ℂ) (δ : Ω → ℝ)
    (X : Ω → Set ℂ) (liftB : ℕ → Ω → ℂ → ℝ) (M : ℕ → Set Ω) (old : ℕ → Ω → Chart) (q : ℝ≥0)
    (S : Ω → ℝ → Prop) : Prop :=
  ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
    (∀ i, IsLocalSetMean (liveExt A γ C (F i) 0) h₀ P (gB i)) →
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
        (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
        (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
      extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω → S ω ξ →
      ∃ (i : ℕ) (x r b d : ℝ), ω ∈ M i ∧ 0 < r ∧
        (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
        Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ C (F i) 0 ω) ((relChart c γ q ω).2.1 y) +
            u ((relChart c γ q ω).2.1 y) + chiC κ * liftB i ω ((relChart c γ q ω).2.1 y))
          (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
        Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
            liftB i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
        b + chiC κ * d = phaseData κ ρL ρR
          (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
          (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
          (δ ω) ξ - a

/-- **The initial heights in the base chart** (named field-level input; Aux. 119–121 at time `0`): for every version
`g₀` of the local-set mean of the pocket exterior `liveExt A γ C ∅ 0`, almost surely on the test, at every real base
coordinate `x` off the initial force jumps whose physical landing avoids `X₀`, the base-chart reading
`harmRep g₀ + u + χ ℓ_c` along `c⁻¹` tends to the initial word at `x` minus the offset `a`. -/
def R7InitialHeights (κ : ℝ) {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (P : Measure Ω)
    (A : Set Ω) (γ : Ω → ℝ → ℂ) (C : Ω → Set ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ)
    (c : Ω → Chart) (a : ℝ) (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) (X₀ : Ω → Set ℂ) : Prop :=
  ∀ g₀ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (liveExt A γ C (fun _ => ∅) 0) h₀ P g₀ →
    ∀ᵐ ω ∂P, ω ∈ A → ∀ x : ℝ, x ∉ forceJumpSet (xL ω) (xR ω) → extendFrom H (c ω).2.1 x ∉ X₀ ω →
      Tendsto (fun y => harmRep (g₀ ω) (H \ liveExt A γ C (fun _ => ∅) 0 ω) ((c ω).2.1 y) +
          u ((c ω).2.1 y) + chiC κ * (c ω).2.2 ((c ω).2.1 y))
        (𝓝[H] (x : ℂ)) (𝓝 (forceBoundaryData κ ρL ρR (xL ω) (xR ω) x - a))

/-- **Non-exceptional exposed coordinates land in the pocket** (named pathwise input): almost surely on the live
test, every real current coordinate off the jumps, inside the open exposed interval, whose landing avoids `X`, lands
in `C`. -/
def R7ExposedLanding (P : Measure Ω) (A : Set Ω) (γ : Ω → ℝ → ℂ) {nL nR : ℕ} (xL : Ω → Fin (nL + 1) → ℝ)
    (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (C : Ω → Set ℂ) (X : Ω → Set ℂ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
    extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
    ξ ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q) →
    extendFrom H (relChart c γ q ω).2.1 ξ ∈ C ω

end Defs

/-- The selector of **hull landings**: the landing lies in the open pocket. -/
def hullSel (c : Ω → Chart) (γ : Ω → ℝ → ℂ) (C : Ω → Set ℂ) (q : ℝ≥0) (ω : Ω) (ξ : ℝ) : Prop :=
  extendFrom H (relChart c γ q ω).2.1 ξ ∈ C ω

/-- The selector of **wall coordinates**: outside the open exposed interval `(v_L(q), v_R(q))`. -/
def wallSel (γ : Ω → ℝ → ℂ) {nL nR : ℕ} (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (q : ℝ≥0)
    (ω : Ω) (ξ : ℝ) : Prop :=
  ξ ∉ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
    (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q)

/-- The selector of **exposed coordinates landing outside the pocket**. -/
def exposedOuterSel (c : Ω → Chart) (γ : Ω → ℝ → ℂ) (C : Ω → Set ℂ) {nL nR : ℕ} (xL : Ω → Fin (nL + 1) → ℝ)
    (xR : Ω → Fin (nR + 1) → ℝ) (q : ℝ≥0) (ω : Ω) (ξ : ℝ) : Prop :=
  ¬ wallSel γ xL xR q ω ξ ∧ ¬ hullSel c γ C q ω ξ

/-! ### Generic facts -/

section Generic

variable [MeasurableSpace Ω] {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {P : Measure Ω}
  {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
  {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {C : Ω → Set ℂ} {F : ℕ → Ω → Set ℂ} {δ : Ω → ℝ}
  {X : Ω → Set ℂ} {liftB : ℕ → Ω → ℂ → ℝ} {M : ℕ → Set Ω} {old : ℕ → Ω → Chart} {q : ℝ≥0}

/-- **The split**: covers on three sets of coordinates whose union contains `S` give the cover on `S`. -/
theorem R5Cover.of_split {S S₁ S₂ S₃ : Ω → ℝ → Prop}
    (h₁ : R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q S₁)
    (h₂ : R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q S₂)
    (h₃ : R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q S₃)
    (hS : ∀ ω ξ, S ω ξ → S₁ ω ξ ∨ S₂ ω ξ ∨ S₃ ω ξ) :
    R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q S := by
  intro gB hgB
  filter_upwards [h₁ gB hgB, h₂ gB hgB, h₃ gB hgB] with ω hω₁ hω₂ hω₃ hωA hq ξ hξ hX hSξ
  rcases hS ω ξ hSξ with h | h | h
  · exact hω₁ hωA hq ξ hξ hX h
  · exact hω₂ hωA hq ξ hξ hX h
  · exact hω₃ hωA hq ξ hξ hX h

omit [MeasurableSpace Ω] in
/-- The three selectors cover every coordinate. -/
theorem sel_cover (ω : Ω) (ξ : ℝ) :
    hullSel c γ C q ω ξ ∨ wallSel γ xL xR q ω ξ ∨ exposedOuterSel c γ C xL xR q ω ξ := by
  by_cases hw : wallSel γ xL xR q ω ξ
  · exact Or.inr (Or.inl hw)
  · by_cases hh : hullSel c γ C q ω ξ
    · exact Or.inl hh
    · exact Or.inr (Or.inr ⟨hw, hh⟩)

/-- **The full clause 5 from the split cover**: the hull, wall and exposed-outer pieces give `R5Cover` on every
coordinate. -/
theorem R5Cover.of_three
    (hHull : R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q (hullSel c γ C q))
    (hWall : R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q (wallSel γ xL xR q))
    (hOuter : R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q (exposedOuterSel c γ C xL xR q)) :
    R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q (fun _ _ => True) :=
  R5Cover.of_split hHull hWall hOuter fun ω ξ _ => sel_cover ω ξ

/-- `R5Cover` on every coordinate is clause 5 of `R5Clauses`. -/
theorem r5Cover_true_iff [IsProbabilityMeasure P] :
    R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q (fun _ _ => True) ↔
      ∀ gB : ℕ → Ω → DistOn upperHalfPlaneOpens,
        (∀ i, IsLocalSetMean (liveExt A γ C (F i) 0) h₀ P (gB i)) →
        ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
            (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
            (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
          extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
          ∃ (i : ℕ) (x r b d : ℝ), ω ∈ M i ∧ 0 < r ∧
            (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
            Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
            Tendsto (fun y => harmRep (gB i ω) (H \ liveExt A γ C (F i) 0 ω) ((relChart c γ q ω).2.1 y) +
                u ((relChart c γ q ω).2.1 y) + chiC κ * liftB i ω ((relChart c γ q ω).2.1 y))
              (𝓝[H] (ξ : ℂ)) (𝓝 b) ∧
            Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
                liftB i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 d) ∧
            b + chiC κ * d = phaseData κ ρL ρR
              (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
              (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q)
              (δ ω) ξ - a := by
  constructor
  · intro h gB hgB
    filter_upwards [h gB hgB] with ω hω hωA hq ξ hξ hX
    exact hω hωA hq ξ hξ hX trivial
  · intro h gB hgB
    filter_upwards [h gB hgB] with ω hω hωA hq ξ hξ hX _
    exact hω hωA hq ξ hξ hX

/-- **The exposed-outer piece from the landing statement**: if non-exceptional exposed coordinates land in the
pocket, the cover on the exposed coordinates landing outside it is vacuous. -/
theorem r5Cover_exposedOuter_of_landing (hLand : R7ExposedLanding P A γ xL xR c C X q) :
    R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X liftB M old q (exposedOuterSel c γ C xL xR q) := by
  intro gB hgB
  filter_upwards [hLand] with ω hω hωA hq ξ hξ hX hS
  exact absurd (hω hωA hq ξ hξ hX (not_not.1 hS.1)) hS.2

end Generic

/-! ### The hull piece: ambient heights converted to the own lifts -/

section Hull

variable {κ : ℝ} {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ}
  [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h h' h'' : Ω → DistOn upperHalfPlaneOpens} {a' k c' : ℝ} {u₀ : ℂ → ℝ} {𝓕₀ : Filtration ℝ≥0 mΩ}
  {W' : ℝ≥0 → Ω → ℝ} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ' : Ω → ℝ≥0∞} {u₀' : ℂ → ℝ} {R L : Ω → ℝ≥0 → ℂ}

/-- **The hull piece of the split cover** (coordinates landing in the pocket): R5-REFCHART's hull cover
`R7AmbientCoverHull` for references that are relative charts at earlier capacities `p i ω ≤ q` gives the cover with
the references' own lifts. The heights are R5-SAMETIME's `ae_tendsto_harmRep_refHull` (walls' data of
`R5Phase.pocketStopUnionLaw_ref`), converted by `tendsto_refLift_of_lift_sub` (`b = β_s(x′) + χ d`, `d = 0`). -/
theorem r5Cover_hull
    (hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) a' k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c' (h' ω) (h'' ω))
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    (hC : IsOptionalHullCoupling κ xL' xR' ρL' ρR' P 𝓕₀ W' VL VR B ζ' h'')
    (hκ : 0 < κ)
    (hu₀' : IsBoundedHarmonicExtension (forceBoundaryData κ ρL' ρR' xL' xR') (forceJumpSet xL' xR') u₀')
    (hX : IsMeasurableKilledDriving W' VL VR ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω)) (hR0 : ∀ ω, R ω 0 = 0)
    (hL0 : ∀ ω, L ω 0 = 0) (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hdetR : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => R ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hdetL : ∀ t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => L ω t) =ᵐ[P] fun ω => f (centredField h u₀ ω))
    (hlocR : Sec6.IsEntranceHistoryLocal R (centredField h u₀) P)
    (hlocL : Sec6.IsEntranceHistoryLocal L (centredField h u₀) P)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} (hc : ∀ ω ∈ A, (c ω).IsConformal) {a : ℝ} {δ : Ω → ℝ}
    {X : Ω → Set ℂ} {M : ℕ → Set Ω} {p : ℕ → Ω → ℝ≥0} {q : ℝ≥0}
    (hMp : ∀ i, ∀ ω ∈ M i, p i ω ≤ q)
    (hCov : R5Ref.R7AmbientCoverHull κ ρL ρR ρL' ρR' P A γ xL xR c a (fun ω => cfPocket (R ω) (L ω) r) W' ζ' VL VR
      δ X M (fun i ω => relChart c γ (p i ω) ω) q) :
    R5Cover κ ρL ρR P A γ xL xR c a (centredField h'' u₀') u₀' (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ')
      δ X (fun i ω => (relChart c γ (p i ω) ω).2.2) M (fun i ω => relChart c γ (p i ω) ω) q
      (hullSel c γ (fun ω => cfPocket (R ω) (L ω) r) q) := by
  intro gB hgB
  have hH := ae_tendsto_harmRep_refHull hT' hTr hu₀ hh hC hκ hu₀' hX hζ hRc hLc hR0 hL0 hRm hLm hdetR hdetL
    hlocR hlocL hGm hG hA hAG hγ hgB
  filter_upwards [hH, hCov] with ω hHω hcovω hωA hlive ξ hξ hXξ hS
  obtain ⟨i, x, r', x', d, z₀, hM, hr, hcol, htr, hz₀, hinv, hev, hx', hfx, hd, hword⟩ :=
    hcovω hωA hlive ξ hξ hXξ hS
  have hb := hHω hωA i z₀ hz₀ _ (ξ : ℂ) x' hx' hinv hev hfx
  obtain ⟨hb', hd'⟩ := tendsto_refLift_of_lift_sub (c := c) (γ := γ) (p := p i ω) (q := q) (hc ω hωA)
    (hγ ω hωA) hlive (hMp i ω hM) hr hcol htr
    (f := harmRep (gB i ω) (H \ liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (refHull W' ζ' i) 0 ω))
    (g := u₀') (ℓ := ambLift W' i ω) hb hd
  exact ⟨i, x, r', _, 0, hM, hr, hcol, htr, hb', hd', by rw [mul_zero, add_zero, hword]⟩

end Hull

/-! ### The wall piece: the zero reference and the initial heights -/

section Wall

variable [MeasurableSpace Ω] {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {P : Measure Ω}
  {A : Set Ω} {γ : Ω → ℝ → ℂ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {c : Ω → Chart} {a : ℝ}
  {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ} {C : Ω → Set ℂ} {F : ℕ → Ω → Set ℂ} {δ : Ω → ℝ}
  {X X₀ : Ω → Set ℂ} {M : ℕ → Set Ω} {old : ℕ → Ω → Chart} {q : ℝ≥0}

/-- **The wall piece of the split cover** (coordinates outside the open exposed interval): if the family has a zero
reference `i₀` (reference set empty, chart the relative chart at capacity `0`, pair event containing the live test),
the initial heights (exceptional set `X₀ ⊆ X`) give the cover on the wall coordinates, with the references' own
lifts. All marks are at `0`. -/
theorem r5Cover_wall (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hcExt : ∀ ω ∈ A, ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hxL : ∀ ω i, xL ω i = 0) (hxR : ∀ ω j, xR ω j = 0) {i₀ : ℕ} (hF₀ : F i₀ = fun _ => ∅)
    (hold₀ : ∀ ω ∈ A, old i₀ ω = relChart c γ 0 ω)
    (hM₀ : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → ω ∈ M i₀) (hX₀ : ∀ ω, X₀ ω ⊆ X ω)
    (hInit : R7InitialHeights κ ρL ρR P A γ C xL xR c a h₀ u X₀) :
    R5Cover κ ρL ρR P A γ xL xR c a h₀ u C F δ X (fun i ω => (old i ω).2.2) M old q (wallSel γ xL xR q) := by
  intro gB hgB
  have hg₀ := hgB i₀
  rw [hF₀] at hg₀
  filter_upwards [hInit (gB i₀) hg₀] with ω hIω hωA hlive ξ hξ hXξ hS
  obtain ⟨x, r', b, d, hr, hcol, htr, hb, hd, hword⟩ := wall_cover_pathwise (c := c) (γ := γ) (ω := ω) (q := q)
    (hc ω hωA) (hγ ω hωA) hlive (hcExt ω hωA) (hxL ω) (hxR ω) ρL ρR (δ := δ ω)
    (v := harmRep (gB i₀ ω) (H \ liveExt A γ C (fun _ => ∅) 0 ω)) (hIω hωA) hξ hS (fun h => hXξ (hX₀ ω h))
  refine ⟨i₀, x, r', b, d, hM₀ ω hωA hlive, hr, ?_, ?_, ?_, ?_, hword⟩
  · rw [hold₀ ω hωA]
    exact hcol
  · rw [hold₀ ω hωA]
    exact htr
  · rw [hold₀ ω hωA, hF₀]
    exact hb
  · rw [hold₀ ω hωA]
    exact hd

end Wall

end InteractingSLE.Sec7.R5Wall
