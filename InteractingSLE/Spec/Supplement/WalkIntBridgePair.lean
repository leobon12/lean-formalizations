/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBridgePrefix

/-!
# The common-arc leaf conditional on ordered incident-side geometry

The named geometric hypothesis supplies the two recorded prefixes and a
continuous identification of their designated left incident collars. Prefix
domain disjointness, avoidance of the complete walks, all transition facts,
and the subsequent derivative-lift integer are proved from those data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkIntBridge

open WalkBdry WalkNorm WalkMean WalkInf

/-- Two prefixes through an interior common arc, with the designated left
side points. This records physical geometry only; domain avoidance and
transition limits are not fields. -/
structure PairPrefixData (sR sL : ExplState) where
  preR : List Piece
  postR : List Piece
  preL : List Piece
  postL : List Piece
  pcR : Piece
  pcL : Piece
  τR : ℚ≥0
  τL : ℚ≥0
  yR : ℝ
  yL : ℝ
  p : ℂ
  radius : ℝ
  splitR : sR.1 = preR ++ pcR :: postR
  aliveR : (((τR : ℝ≥0)) : ℝ≥0∞) < pcR.2.2
  sideR : IsLeftSidePt pcR τR yR
  splitL : sL.1 = preL ++ pcL :: postL
  aliveL : (((τL : ℝ≥0)) : ℝ≥0∞) < pcL.2.2
  sideL : IsLeftSidePt pcL τL yL
  landR : Tendsto (prefixChart pcR τR).2.1 (𝓝[H] (yR : ℂ)) (𝓝 p)
  landL : Tendsto (prefixChart pcL τL).2.1 (𝓝[H] (yL : ℂ)) (𝓝 p)
  mem_pair : p ∈ wsetOf sR ∩ wsetOf sL
  radius_pos : 0 < radius
  containedR : wsetOf sR ∩ ball p radius ⊆ prefixSet preR pcR τR
  containedL : wsetOf sL ∩ ball p radius ⊆ prefixSet preL pcL τL
  agree : wsetOf sR ∩ ball p radius = wsetOf sL ∩ ball p radius

/-- The left prefix inverse eventually avoids both complete walks. The
prefix-domain disjointness premise is proved for every recorded walk prefix
by `prefixChart_disjoint_prefixSet`. -/
theorem PairPrefixData.eventually_avoid {sR sL : ExplState}
    (d : PairPrefixData sR sL) (hcR : (prefixChart d.pcR d.τR).IsConformal)
    (hdisj : Disjoint ((prefixChart d.pcR d.τR).dom : Set ℂ)
      (prefixSet d.preR d.pcR d.τR)) :
    ∀ᶠ z in 𝓝[H] (d.yR : ℂ), (prefixChart d.pcR d.τR).2.1 z ∈
      H \ (wsetOf sR ∪ wsetOf sL) := by
  filter_upwards [self_mem_nhdsWithin,
    d.landR.eventually (ball_mem_nhds d.p d.radius_pos)] with z hz hzb
  have hzD := hcR.inv_mem_dom hz
  have hnR : (prefixChart d.pcR d.τR).2.1 z ∉ wsetOf sR := by
    intro hm
    exact Set.disjoint_left.1 hdisj hzD (d.containedR ⟨hm, hzb⟩)
  refine ⟨hcR.2.1 hz, fun hm => ?_⟩
  rcases hm with hm | hm
  · exact hnR hm
  · have hR : (prefixChart d.pcR d.τR).2.1 z ∈ wsetOf sR ∩ ball d.p d.radius := by
      rw [d.agree]
      exact ⟨hm, hzb⟩
    exact hnR hR.1

/-- Remaining new common-arc geometry, explicitly retained as a named input:
select the recorded prefixes and identify their left incident collars.
The full stochastic hypotheses are preserved from the requested leaf. -/
def WalkPairAccessGeometryStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkPairPathFacts κ b jumps E ω) →
      (∀ᵐ ω ∂P, WalkPiecesSimple κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ pR ∈ (walkRuns κ b jumps E ω).1.1,
        ∀ pL ∈ (walkRuns κ b jumps E ω).2.1,
        ∀ S ⊆ closure (pR.1.tipSet pR.2.1 pR.2.2) ∩
          closure (pL.1.tipSet pL.2.1 pL.2.2), IsPreconnected S → ¬ S.Subsingleton →
          ∃ d : PairPrefixData (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2,
            Nonempty (SideIdentification (prefixChart d.pcR d.τR)
              (prefixChart d.pcL d.τL) d.yR d.yL)

/-- All conjuncts of the local pair leaf, conditional only on the named
ordered-access geometric construction. -/
theorem walkPairGeomLocStatement_of_accessGeometry
    (hgeom : WalkPairAccessGeometryStatement.{u}) : WalkPairGeomLocStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts hsimple
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  filter_upwards [hgeom κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    E hE hR hreg hfacts hsimple, hRR, hRL]
    with ω hω hωR hωL pR hpR pL hpL S hS hSc hSn
  obtain ⟨d, ⟨G⟩⟩ := hω pR hpR pL hpL S hS hSc hSn
  have hrR := fun j c θ hl => pieceRegular_of_event hωR j c θ hl
  have hrL := fun j c θ hl => pieceRegular_of_event hωL j c θ hl
  obtain ⟨hcR, _⟩ := prefixChart_props (κ := κ) (b := b) (jumps := jumps) _ _ _
    (fun j _ c θ hl => hrR j c θ hl) (fun j => hreg _ j ω) d.splitR d.aliveR
  obtain ⟨hcL, _⟩ := prefixChart_props (κ := κ) (b := b) (jumps := jumps) _ _ _
    (fun j _ c θ hl => hrL j c θ hl) (fun j => hreg _ j ω) d.splitL d.aliveL
  have hdisj := prefixChart_disjoint_prefixSet (κ := κ) (b := b) (jumps := jumps)
    (-(Real.pi / 2)) true _ hrR (fun j => hreg _ j ω) d.splitR d.aliveR
  obtain ⟨δ, hδ, hsub, hreal, hT⟩ := G.local_transition hcL
  exact ⟨d.preR, d.postR, d.preL, d.postL, d.pcR, d.pcL, d.τR, d.τL,
    d.yR, d.yL, d.p, d.radius, δ, d.splitR, d.aliveR, d.sideR,
    d.splitL, d.aliveL, d.sideL, d.landR, d.landL, d.mem_pair,
    d.radius_pos, d.containedR, d.containedL, d.agree,
    d.eventually_avoid hcR hdisj, hδ, hsub, hreal, hT⟩

/-- The original common-arc geometry-and-integer leaf from the explicit
ordered-access input and GW1 piece simplicity. -/
theorem walkPairGeomCOStatement_of_accessGeometry
    (hS : GW1Z.GW1PieceSimpleStatement.{u})
    (hgeom : WalkPairAccessGeometryStatement.{u}) : WalkPairGeomCOStatement.{u} :=
  walkPairGeomCOStatement_of_loc hS (walkPairGeomLocStatement_of_accessGeometry hgeom)

end InteractingSLE.Theorem14.WalkIntBridge
