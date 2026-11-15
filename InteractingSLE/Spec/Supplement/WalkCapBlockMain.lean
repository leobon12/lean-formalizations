/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkCapBlockAmbient

/-!
# Walk-side inputs with only off-sector original seed data remaining

Packet PROVE-T14-WALKSIDE2, seed continuation. The original side-height sector
is proved by the landed GW1 induction. Only original seed data for boundary
words outside that sector remain a named mathematical hypothesis. In the actual
centered-counterflow setting the side-height bound follows from GW0 and
Theorem 1.3, so the off-sector case cannot occur.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkCapBlock

open Exist.Staged Exist.StagedLaw WalkSideResume

/-- The remaining original-state seed input, required only when the original
boundary word fails the side-height bound. It contains no artificial cap. -/
def OffAmbientSeedStatement (θ : ℝ) (right : Bool) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), IsRegularDriver (E spec k ω)) →
      ¬ AmbientSideBound κ b jumps θ right →
      ∀ᵐ ω ∂P, WalkSeedData κ b jumps θ right
        (fun j => E (boundaryWalkSpec b jumps θ right) j ω)

/-- The earlier non-launch input is discharged in the side-height sector and
reduced to original seed data only outside that sector. -/
theorem nonFlowCapNoLaunchStatement_of_offAmbientSeeds {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) {right : Bool}
    (hOff : OffAmbientSeedStatement.{u} θ right) :
    NonFlowCapNoLaunchStatement.{u} θ right := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hR hreg ℓ hℓ hnon
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  by_cases hamb : AmbientSideBound κ b jumps θ right
  · exact ae_noLaunch_capSpec_of_ambient hκ hb hh
      (hE (boundaryWalkSpec b jumps θ right) hw) (hreg _) hamb ℓ hℓ hnon
  · filter_upwards [hOff κ hκ hκ4 b jumps hb P h hh E hE hR hreg hamb] with ω hω
    exact noLaunch_capSpec_of_seedData
      (fun j => E (boundaryWalkSpec b jumps θ right) j ω) hω ℓ hℓ hnon

/-- In the actual infinite-lifetime centered-counterflow setting, GW0 supplies
the side-height bound for either extreme walk. -/
theorem ambientSideBound_of_counterflow (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (right : Bool) :
    AmbientSideBound κ b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right := by
  have hbds := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀)
    hκ hκ4 hb hh hcf hζ
  cases right
  · exact hbds.2
  · exact hbds.1

/-- In the source's infinite-lifetime centered-counterflow setting, the
non-flow-cap conclusion requires no new non-launch or seed-data hypothesis. -/
theorem ae_noLaunch_capSpec_of_counterflow (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {right : Bool} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : IsStagedHistory κ b jumps P h
      (boundaryWalkSpec b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (ℓ : ℕ)
    (hℓ : ℓ ≤ (boundaryWalkSpec b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right).2.2.length)
    (hnon : (boundaryWalkSpec b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right).2.2[ℓ]? ≠
      some (Sum.inl ((if right then -(Real.pi / 2) else Real.pi / 2), ⊤))) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b jumps
        (WalkSide.capSpec (boundaryWalkSpec b jumps (if right then -(Real.pi / 2) else Real.pi / 2) right)
          ℓ (if right then -(Real.pi / 2) else Real.pi / 2) 0)
        (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ = none :=
  ae_noLaunch_capSpec_of_ambient hκ hb hh hE hreg
    (ambientSideBound_of_counterflow h13₀ hκ hκ4 hb hh hcf hζ right) ℓ hℓ hnon

/-- All four exact packet leaves, with the proved side-height sector removed
from the remaining mathematical inputs. Landed statements are unchanged. -/
theorem prefixInputs_of_offAmbientSeeds
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hR : OffAmbientSeedStatement.{u} (-(Real.pi / 2)) true)
    (hL : OffAmbientSeedStatement.{u} (Real.pi / 2) false) :
    WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true ∧
    WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false ∧
    WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false :=
  prefixInputs_of_noLaunch h12 h13
    (nonFlowCapNoLaunchStatement_of_offAmbientSeeds
      ⟨le_rfl, by linarith only [Real.pi_pos]⟩ hR)
    (nonFlowCapNoLaunchStatement_of_offAmbientSeeds
      ⟨by linarith only [Real.pi_pos], le_rfl⟩ hL)

end InteractingSLE.Theorem14.WalkCapBlock
