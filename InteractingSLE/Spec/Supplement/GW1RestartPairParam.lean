/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartPairData

/-!
# GW1: reduction of the finite restart pair to its two source laws

The deterministic clock and conditioning assembly is proved here. The two full
field–path source laws are explicit named hypotheses, not consequences of GB6 here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1RestartPair

open Exist Exist.Staged Exist.StagedLaw
open PiecewiseConstantBoundaryData (jumpSet)

/-- All hypotheses of the source-law reduction follow from the current launch
datum. GB6 is used only for that launch's new simple piece. -/
theorem restartData_of_isLaunchClock
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec k ω, IsRegularDriver (E spec k ω))
    (hPieces : ∀ spec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    {right : Bool} {n : ℕ} (hn : n < (jumpSet b jumps).card)
    {V : ℝ≥0 → Ω → ℝ} {ζV : Ω → ℝ≥0∞} {ℓ : Ω → ℝ≥0 → ℝ≥0}
    (hD : GW1Z.IsLaunchClock κ b jumps P h W' (GW1Z.walkSpec b jumps right)
      (E (GW1Z.walkSpec b jumps right)) (2 * n) V ζV ℓ) :
    RestartData κ b jumps P h W' ζ' E right n V ζV ℓ := by
  have hProg := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (GW1Z.walkAngle_mem_Icc right) right
  refine ⟨hκ, hκ4, hb, hh, hcf, hζ, hE, hreg, hPieces, hn, hD, ?_, ?_⟩
  · exact ae_isSimplePiece_of_isLaunchClock hGB6 hT13 hT13₀ hκ hκ4 hb
      (hE _ hProg) (hreg _) (hPieces _ hProg) hD
  · exact GW1WalkExit.walkStageData_of_theorem13 hT13₀
      κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ E hE hreg right

/-- The requested finite step from the two explicitly named new source-law
inputs. This is a conditional helper, not a provider without those inputs. -/
theorem finiteRestartPairStatement_of_terminal_and_retarget_laws
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hTerminal : TerminalRestartLawStatement.{u})
    (hRetarget : FiniteRetargetLawStatement.{u}) :
    GW1LaunchClock.FiniteRestartPairStatement.{u} := by
  intro hGB6 κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ
    E hE hreg hPieces right n hn V ζV ℓ hD
  have hdata := restartData_of_isLaunchClock hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ
    hE hreg hPieces hn hD
  obtain ⟨Q, ζQ, β, hQ⟩ := hTerminal κ b jumps P h W' ζ' E right n V ζV ℓ hdata
  obtain ⟨U, ζ, a, hU⟩ := hRetarget κ b jumps P h W' ζ' E right n V ζV ℓ hdata Q ζQ β hQ
  exact ⟨U, ζ, fun ω => β ω ∘ a ω, isFiniteRestartPair_of_terminal_and_forcedRetarget hQ hU⟩

/-- The walk clocks with precisely the same two remaining source-law inputs. -/
theorem walkLaunchClockStatement_of_terminal_and_retarget_laws
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hTerminal : TerminalRestartLawStatement.{u})
    (hRetarget : FiniteRetargetLawStatement.{u}) : GW1Z.WalkLaunchClockStatement.{u} :=
  GW1LaunchClock.walkLaunchClockStatement_of_finiteRestartPair hGB6 hT13 hT13₀
    (finiteRestartPairStatement_of_terminal_and_retarget_laws hT13 hT13₀ hTerminal hRetarget)

end InteractingSLE.Theorem14.GW1RestartPair
