import Mathlib
import MatedCRTHarmonic.Frozen.LFMultigraph
import MatedCRTHarmonic.Frozen.Dart
import MatedCRTHarmonic.Frozen.Dtgt
import MatedCRTHarmonic.Frozen.OutDarts
import MatedCRTHarmonic.Frozen.Deg
import MatedCRTHarmonic.Frozen.State
import MatedCRTHarmonic.Frozen.StateMeasurableSpace
import MatedCRTHarmonic.Frozen.WalkLaw
import MatedCRTHarmonic.Frozen.VertexPath
import MatedCRTHarmonic.Frozen.HitTime
import MatedCRTHarmonic.Frozen.Recurrent
import MatedCRTHarmonic.Frozen.VerticesMeeting
import MatedCRTHarmonic.Frozen.MatedCRTPath2
import MatedCRTHarmonic.Frozen.MatedCRTEdge
import MatedCRTHarmonic.Frozen.MatedCRTIsLocallyFinite
import MatedCRTHarmonic.Frozen.MatedCRTGraph
import MatedCRTHarmonic.Frozen.MatedCRTField
import MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import MatedCRTHarmonic.Frozen.EnergyOn
import MatedCRTHarmonic.Frozen.IsHarmonicExtension
import MatedCRTHarmonic.Frozen.IsTutteEmbedding
import MatedCRTHarmonic.Frozen.ExitGreen
import MatedCRTHarmonic.Frozen.DirichletEnergy
import MatedCRTHarmonic.Frozen.HasBoundedConvexity
import MatedCRTHarmonic.Frozen.MatedCRTCell
import MatedCRTHarmonic.GMSMain.MainResultsWiring

/-!
# [18] Corollary 1.6 (maximal length of embedded edges), main form, conditional on the mating-of-trees input bundle

Main theorem of the formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps* (arXiv:1807.07511), here called [18]. It is conditional on the
mating-of-trees input bundle: it holds for every mating-of-trees coupling (every witness of
`MatedCRT.MatingOfTreesInput γ`); the bundle itself is not proved here. The statement is the frozen
statement text, with the library namespace renamed and the theorem named after [18]; the proof is
`matedCRT_tutte_edge_le_of_matingOfTrees_holds` in `MatedCRTHarmonic.GMSMain.MainResultsWiring`, which proves the same statement.

Every theorem is stated for every mating-of-trees coupling `MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B'
B₀ B₀' U ηL η η₀ bm` with `γ ∈ (0, 2)` on a standard Borel probability space, that is, for every witness of the
bundle `MatedCRT.MatingOfTreesInput γ`: `η` is the whole-plane space-filling SLE_{16/γ²} parametrized by the γ-LQG
area of the γ-quantum cone, with `η(0) = 0`, and `bm` is its normalized boundary-length pair. For a mesh `ε > 0` the
vertex `x : ℤ` stands for `εx ∈ εℤ`, its cell is `MatedCRT.cell ε η x = η([εx − ε, εx])` ([18] (1.3)), its embedded
position is `η(εx)`, and the map `G^ε` is `MatedCRT.graph ε (bm ω) h`, the mated-CRT map of [18] (1.1) with its
double edges. "With probability at least `1 − O_ε(ε^α)`" is `∃ C, ∀ ε ∈ (0, 1), P(bad event) ≤ C ε^α`, with `P` the
outer measure of the bad event; the bad event contains the null set where `G^ε` is not locally finite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic

/-- **[18] Corollary 1.6 (maximal length of embedded edges), main form**, for every mating-of-trees coupling, with
the Tutte embedding of [18] §1.6. As for Theorem 1.5, "`D` simply connected" is replaced by "`D` a domain with `ℂ ∖ D`
connected". For every `ρ ∈ (0, 1)` there is `ξ' = ξ'(ρ, γ) > 0` (chosen before `D`) such that for every open connected
`D ⊂ B_ρ(0)` with `ℂ ∖ D` connected there is a constant `C` (the `O_ε`-constant of (1.10)) with: as `ε → 0`, the
probability that the Tutte embedding `Φ^ε` of `G^ε(D)` with identity boundary data exists and every one of them
satisfies `max_{{x,y} ∈ E(G^ε(D))} |Φ^ε(x) − Φ^ε(y)| ≤ C ε^{ξ'}` tends to `1` (the edges of `G^ε(D)` are the edges of
`G^ε` with both ends in `V_{G^ε}(D)`, [18] (1.5)). -/
theorem corollary1_6 :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ ξ' : ℝ, 0 < ξ' ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → IsConnected D → IsConnected Dᶜ →
          ∃ C : ℝ, Tendsto (fun ε : ℝ =>
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ Φ : ℤ → ℂ,
                (MatedCRT.graph ε (bm ω) h).IsTutteEmbedding (MatedCRT.cell ε (η ω)) D Φ) ∧
              ∀ Φ : ℤ → ℂ,
                (MatedCRT.graph ε (bm ω) h).IsTutteEmbedding (MatedCRT.cell ε (η ω)) D Φ →
                ∀ e : MatedCRT.Edge ε (bm ω),
                  (MatedCRT.graph ε (bm ω) h).src e ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D →
                  (MatedCRT.graph ε (bm ω) h).tgt e ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D →
                    ‖Φ ((MatedCRT.graph ε (bm ω) h).src e) - Φ ((MatedCRT.graph ε (bm ω) h).tgt e)‖ ≤
                      C * ε ^ ξ'}) (𝓝[>] 0) (𝓝 0) := by
  exact GMSMain.MainResults.matedCRT_tutte_edge_le_of_matingOfTrees_holds

end MatedCRTHarmonic
