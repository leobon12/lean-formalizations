import BouRabeeGwynne.TheoremAStatement
import BouRabeeGwynne.TheoremBStatement
import BouRabeeGwynne.Section4BallExitLevyProkhorov

/-!
# MR Corollary 1.2 (random-walk consequences without alternatives (I)–(III)) — DRAFT statements

Source: MR p. 4 (Corollary 1.2) and its proof, MR §7, pp. 15–16; BRG = arXiv:2405.11673v2 §4
(Assumption D with (4.1)–(4.2), Proposition 4.2, Theorem 4.1) and Theorem A.
See `STATEMENT_SPEC.md`.

Reused objects: `TilingSequence`, `NearestVertexData`, `ApproximationCondition` (= BRG (1.3)),
`HasAmbientCollar`, `IsDomain`, `IsLipschitzDomain`, `HarmonicNearClosure`,
`DirichletApproximationTarget`, `HasFiniteAccessibleRegion`, `spatialExitProbability`,
`brownianSpatialHarmonicMeasure`, and the whole conclusion of `TheoremAStatement`.
These are target definitions only; nothing is proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal Topology
open MeasureTheory

namespace BouRabeeGwynne.MeshRates

/-- BRG Assumption D (§4), specialised to the canonical walk on a sequence of orthogonal tilings,
for a given domain `D₀` (BRG's `𝒟`) and `δ > 0`. BRG: `B_r(U) = {x : inf_{y∈U} ‖x-y‖ ≤ r}`, so
`B_r(x)` is the closed ball and `B_δ(D₀)` is `Metric.cthickening δ D₀`; `B` is closed, so a
neighbourhood of `B` is a neighbourhood of `closure B`. (4.1) is the nearest-vertex condition on
`B`; (4.2) is uniform convergence of the discrete Dirichlet extension on `V_n[B]`, with eventual
well-posedness included (as in `DirichletApproximationTarget`). The walk generator `Δ^{G_n}` and
the conductance Laplacian have the same harmonic functions, so `SolvesDirichlet` is used. -/
def TilingAssumptionD {d : ℕ} (G : TilingSequence d) (N : NearestVertexData G)
    (D₀ : Set (Euc d)) (δ : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x ∈ Metric.cthickening δ D₀,
    (∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop,
      ∀ z ∈ Metric.closedBall x r ∩ Metric.cthickening δ D₀,
        dist ((G.tiling n).pos (N.vertex n z)) z ≤ η) ∧
    ∀ h : Euc d → ℝ,
      HarmonicNearClosure h (Metric.closedBall x r ∩ Metric.cthickening δ D₀) →
      DirichletApproximationTarget G (Metric.closedBall x r ∩ Metric.cthickening δ D₀) h
        (fun n v => h ((G.tiling n).pos v))

/-- First assertion of MR Corollary 1.2: "the mesh hypothesis alone verifies Assumption D".
Following MR §7, for every bounded domain `D₀` compactly inside the tiled set there is `δ > 0`
for which Assumption D holds. Hypotheses: those of BRG Theorem A that concern the tilings
((1.3) = `N.ApproximationCondition`), without (I)–(III). -/
def MeshRatesCorollary12AssumptionDStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
  ∀ (G : TilingSequence d) (N : NearestVertexData G), N.ApproximationCondition →
    ∀ D₀ : Set (Euc d), IsDomain D₀ → Bornology.IsBounded D₀ → HasAmbientCollar D₀ G.domain →
      ∃ δ : ℝ, 0 < δ ∧ TilingAssumptionD G N D₀ δ

/-- Harmonic-measure conclusion of BRG Proposition 4.2 (for every translated/rescaled ball
compactly inside the tiled set, as BRG remarks after its proof), without (I)–(III): the actual
discrete harmonic measure (exit position law of the conductance walk) from every vertex of
`V_n[B]` is uniformly close in Lévy–Prokhorov distance to Brownian harmonic measure of `B` seen
from that vertex's position. Eventual finiteness and boundary accessibility are conclusions. -/
def MeshRatesCorollary12HarmonicMeasureStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
  ∀ (G : TilingSequence d) (N : NearestVertexData G), N.ApproximationCondition →
    ∀ (c : Euc d) (r : ℝ), 0 < r → HasAmbientCollar (Metric.ball c r) G.domain →
    ∀ (μ : Measure (BrownianPath d)) (hμ : IsStandardBrownianLaw μ),
    ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop,
      ∃ hg : (G.tiling n).HasFiniteAccessibleRegion (Metric.ball c r),
        ∀ v : (G.tiling n).V, ∀ hv : v ∈ (G.tiling n).interiorVertices (Metric.ball c r),
          levyProkhorovDist
            ((G.tiling n).spatialExitProbability (Metric.ball c r) hg v
              ((G.tiling n).interiorVertices_subset_closedVertices _ hv) : Measure (Euc d))
            (brownianSpatialHarmonicMeasure (Metric.ball c r) Metric.isOpen_ball μ hμ
              ((G.tiling n).pos v) : Measure (Euc d)) < η

/-- Stopped-walk conclusion of BRG Theorem 4.1 in the orthogonal-tiling setting of Theorem A:
`TheoremAStatement` with the hypothesis `PaperRegularity G` (alternatives (I)–(III)) deleted and
everything else copied verbatim (except `1 ≤ d` → `2 ≤ d`, see `STATEMENT_SPEC.md`). -/
def MeshRatesCorollary12StoppedWalkStatement : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
  ∀ (G : TilingSequence d) (N : NearestVertexData G) (U : Set (Euc d)),
    IsLipschitzDomain U → Bornology.IsBounded U → HasAmbientCollar U G.domain →
    N.ApproximationCondition →
    ∃ μ : Measure (BrownianPath d),
      IsStandardBrownianLaw μ ∧
      (∀ z ∈ U,
        AEMeasurable (stoppedBrownianCurve U z) μ ∧
        (∀ᵐ ω ∂μ, continuousExitTime U z ω ≠ ∞) ∧
        IsProbabilityMeasure (stoppedBrownianLaw U z μ)) ∧
      ∃ walkLaw : ℕ → Euc d → Measure (CurveSpace d),
        (∀ᶠ n in Filter.atTop, ∀ z ∈ U,
          IsStoppedTilingWalkLaw (G.tiling n) U (N.vertex n z) (walkLaw n z)) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop, ∀ z ∈ U,
          levyProkhorovEDist (walkLaw n z) (stoppedBrownianLaw U z μ) ≤
            ENNReal.ofReal η

/-- MR Corollary 1.2 in full: Assumption D from the mesh hypothesis alone, and the conclusions of
BRG Proposition 4.2 and Theorem 4.1 without alternatives (I)–(III). B(b) is out of scope. -/
def MeshRatesCorollary12Statement : Prop :=
  MeshRatesCorollary12AssumptionDStatement ∧
    MeshRatesCorollary12HarmonicMeasureStatement ∧
    MeshRatesCorollary12StoppedWalkStatement

end BouRabeeGwynne.MeshRates
