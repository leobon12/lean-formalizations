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
import MatedCRTHarmonic.GMSMain.MainResultsFinal

/-!
# [18] Theorem 1.5 (Hölder continuity), literal form, conditional on the mating-of-trees input bundle

Main theorem of the formalization of Gwynne–Miller–Sheffield,
*Harmonic functions on mated-CRT maps* (arXiv:1807.07511), here called [18]. It is conditional on the
mating-of-trees input bundle: it holds for every mating-of-trees coupling (every witness of
`MatedCRT.MatingOfTreesInput γ`); the bundle itself is not proved here. The statement is the frozen
statement text, with the library namespace renamed and the theorem named after [18]; the proof is
`matedCRT_holder_of_matingOfTrees_simplyConnected_holds` in `MatedCRTHarmonic.GMSMain.MainResultsFinal`, which proves the same statement.

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

/-- **[18] Theorem 1.5 (Hölder continuity), literal form**, for every mating-of-trees coupling: as `theorem1_5`
with the printed hypothesis "`D` is simply connected" for the open `D ⊂ B_ρ(0)` (`SimplyConnectedSpace D`, which
includes that `D` is nonempty and path-connected). It follows from `theorem1_5` and the planar-topology theorem
`isConnected_compl_of_simplyConnected` (a bounded simply connected open `D ⊂ ℂ` has connected complement). -/
theorem theorem1_5_simplyConnected :
    ∀ γ : ℝ, 0 < γ → γ < 2 →
      ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
        (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
        (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2),
        MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm →
        ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∀ χ : ℝ≥0, 0 < χ → ∃ ξ : ℝ, 0 < ξ ∧
          ∀ D : Set ℂ, IsOpen D → D ⊆ ball (0 : ℂ) ρ → SimplyConnectedSpace D →
          ∀ f : ℂ → ℝ, (∃ K : ℝ≥0, HolderOnWith K χ f (frontier D)) →
          ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
            P {ω | ¬ ∃ h : MatedCRT.IsLocallyFinite ε (bm ω),
              (∃ g : ℤ → ℝ,
                (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g) ∧
              ∀ g : ℤ → ℝ,
                (MatedCRT.graph ε (bm ω) h).IsHarmonicExtension (MatedCRT.cell ε (η ω)) D f g →
                ∀ x ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D,
                  ∀ y ∈ verticesMeeting (MatedCRT.cell ε (η ω)) D,
                    |g x - g y| ≤ A₀ * (max ε (dist (η ω (ε * x)) (η ω (ε * y)))) ^ ξ} ≤
              ENNReal.ofReal (C * ε ^ α) := by
  exact GMSMain.MainResults.matedCRT_holder_of_matingOfTrees_simplyConnected_holds

end MatedCRTHarmonic
