/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkNormFacts

/-!
# Theorem 1.4's walk leaves: the common-arc geometry, analytic part

Packet PROVE-T14-WALKNORM. PROVE-T14-WALKINF's named input `WalkInf.WalkPairGeomCOStatement` asks, at a
nondegenerate common continuum of a piece of `R` and one of `L`, for a common point `p` seen from the left of both
prefixes, with a transition `T = c'_L.1 ∘ c'_R.2.1` from `y_R` to `y_L` and a lift difference tending to a multiple of
`2π` (Theorem GW4, proof, p. 637: "an inherited branch change is an integer multiple of `2πχ`").

The analytic conjuncts follow from the geometry of the configuration (`WalkNormTrans`):

* **`WalkPairGeomLocStatement`**: `WalkPairGeomCOStatement` with its three transition conjuncts (limit of `T` at `y_R`,
  `T ∈ ℍ` and `c'_L.2.1 ∘ T = c'_R.2.1` eventually, the lift difference) replaced by the **local transition
  geometry**: the inverse of `R`'s prefix chart maps an upper half-disc at `y_R` into the domain of `L`'s prefix chart,
  `T` has a real limit at every real point of that disc, and its limit at `y_R` is `y_L`;
* **`walkPairGeomCOStatement_of_loc`**: `WalkPairGeomCOStatement` from it and GW1's per-piece simplicity
  (`GW1Z.GW1PieceSimpleStatement`) — the transition facts directly, the lift
  difference by Schwarz reflection (`exists_int_tendsto_lift_sub`), the prefix charts being conformal with derivative
  lifts (`prefixChart_props`) for the almost surely regular pieces of both walks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkNorm

open WalkLaw GW3Between LocalSets WalkMean WalkBdry WalkInf

/-! ### Regular pieces of a run -/

section Regular

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

open Exist.StagedLaw in
/-- The sample event of `StagedPiecesRegular` gives every launched piece of the run as `GW1P.PieceRegular`. -/
theorem pieceRegular_of_event {spec : ExplSpec} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hω : ∀ (k : ℕ) (θ : ℝ) (t : ℝ≥0∞) (c : Chart), spec.2.2[k]? = some (Sum.inl (θ, t)) →
      (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      (D k).1 0 = 0 ∧ ContinuousOn (D k).1 {s | (s : ℝ≥0∞) ≤ min t (D k).2} ∧
        ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (D k).1 (min t (D k).2) η ∧
          (min t (D k).2 = ⊤ → Tendsto (fun s => ‖η s‖) atTop atTop))
    (j : ℕ) (c : Chart) (θ : ℝ) (hl : (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ)) :
    GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2) := by
  obtain ⟨h1, -, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
  exact hω j θ (instrTime spec j) c h1 hl

end Regular

/-! ### The local transition geometry -/

/-- **Named input: the local geometry of a common arc of the two walks, with the transition in its local form.**
`WalkInf.WalkPairGeomCOStatement`, with the simple pieces of both walks as an extra almost sure hypothesis
(`WalkPiecesSimple`, derived in the wiring by `GW1Z.gw1PieceSimpleStatement_of_walkClock`), and with its last three
conjuncts replaced by: for some `δ > 0`, the inverse of `R`'s
prefix chart maps `ℍ ∩ B(y_R, δ)` into the domain of `L`'s prefix chart, the transition `T = c'_L.1 ∘ c'_R.2.1` has a
real limit at every real point of `B(y_R, δ)`, and its limit at `y_R` is `y_L`. -/
def WalkPairGeomLocStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkPairPathFacts κ b jumps E ω) → (∀ᵐ ω ∂P, WalkPiecesSimple κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ pR ∈ (walkRuns κ b jumps E ω).1.1, ∀ pL ∈ (walkRuns κ b jumps E ω).2.1,
        ∀ S ⊆ closure (pR.1.tipSet pR.2.1 pR.2.2) ∩ closure (pL.1.tipSet pL.2.1 pL.2.2),
          IsPreconnected S → ¬ S.Subsingleton →
          ∃ (preR postR preL postL : List Piece) (pcR pcL : Piece) (τR τL : ℚ≥0) (yR yL : ℝ) (p : ℂ)
            (r δ : ℝ),
            (walkRuns κ b jumps E ω).1.1 = preR ++ pcR :: postR ∧ (((τR : ℝ≥0)) : ℝ≥0∞) < pcR.2.2 ∧
            IsLeftSidePt pcR τR yR ∧
            (walkRuns κ b jumps E ω).2.1 = preL ++ pcL :: postL ∧ (((τL : ℝ≥0)) : ℝ≥0∞) < pcL.2.2 ∧
            IsLeftSidePt pcL τL yL ∧
            Tendsto (prefixChart pcR τR).2.1 (𝓝[H] (yR : ℂ)) (𝓝 p) ∧
            Tendsto (prefixChart pcL τL).2.1 (𝓝[H] (yL : ℂ)) (𝓝 p) ∧
            p ∈ wsetOf (walkRuns κ b jumps E ω).1 ∩ wsetOf (walkRuns κ b jumps E ω).2 ∧ 0 < r ∧
            wsetOf (walkRuns κ b jumps E ω).1 ∩ ball p r ⊆ prefixSet preR pcR τR ∧
            wsetOf (walkRuns κ b jumps E ω).2 ∩ ball p r ⊆ prefixSet preL pcL τL ∧
            wsetOf (walkRuns κ b jumps E ω).1 ∩ ball p r = wsetOf (walkRuns κ b jumps E ω).2 ∩ ball p r ∧
            (∀ᶠ ζ in 𝓝[H] (yR : ℂ), (prefixChart pcR τR).2.1 ζ ∈
              H \ (wsetOf (walkRuns κ b jumps E ω).1 ∪ wsetOf (walkRuns κ b jumps E ω).2)) ∧
            0 < δ ∧
            (∀ ζ ∈ H ∩ ball (yR : ℂ) δ, (prefixChart pcR τR).2.1 ζ ∈ (prefixChart pcL τL).dom) ∧
            (∀ z ∈ ball (yR : ℂ) δ, z.im = 0 → ∃ v : ℂ, v.im = 0 ∧
              Tendsto (fun ζ => (prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ)) (𝓝[H] z) (𝓝 v)) ∧
            Tendsto (fun ζ => (prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ)) (𝓝[H] (yR : ℂ))
              (𝓝 (yL : ℂ))

/-- **`WalkInf.WalkPairGeomCOStatement` from the local transition geometry.** -/
theorem walkPairGeomCOStatement_of_loc (hS : GW1Z.GW1PieceSimpleStatement.{u})
    (hloc : WalkPairGeomLocStatement.{u}) : WalkPairGeomCOStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  filter_upwards [hloc κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts
    (ae_walkPiecesSimple hS hκ hκ4 hb hh hcf hζ' hE hR hreg), hRR, hRL]
    with ω hω hωR hωL pR hpR pL hpL S hS hSc hSn
  obtain ⟨preR, postR, preL, postL, pcR, pcL, τR, τL, yR, yL, p, r, δ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, hδ, hsub, hlim, hT⟩ := hω pR hpR pL hpL S hS hSc hSn
  obtain ⟨hcR, hLR⟩ := prefixChart_props (κ := κ) (b := b) (jumps := jumps) _ _ _
    (fun j _ c θ hl => pieceRegular_of_event hωR j c θ hl) (fun j => hreg _ j ω) h1 h2
  obtain ⟨hcL, hLL⟩ := prefixChart_props (κ := κ) (b := b) (jumps := jumps) _ _ _
    (fun j _ c θ hl => pieceRegular_of_event hωL j c θ hl) (fun j => hreg _ j ω) h4 h5
  obtain ⟨n, hn⟩ := exists_int_tendsto_lift_sub hcR hcL hLR hLL hδ hsub hlim
  exact ⟨preR, postR, preL, postL, pcR, pcL, τR, τL, yR, yL, p, r, n, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    h11, h12, h13, h14, hT, eventually_transition hcL hδ hsub, hn⟩

end InteractingSLE.Theorem14.WalkNorm
