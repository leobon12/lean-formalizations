/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLwReg
import InteractingSLE.Spec.Supplement.GW2aContStepAux

/-!
# SB3's relative stage ordering with pathwise lifetime positivity

Packet PROVE-T14-SBLEAVES2, finding F5 of its first round. `Lv.HasRelStageOrdering`'s ordering clause is conditional
on `∀ᵐ ω ∂Q, 0 < ζr ω`, where the relative lifetime `ζr` is existentially bound inside the predicate, so no consumer can
discharge it. `HasRelStageOrderingP` states the ordering inside the almost-sure event, conditional on the pathwise
positivity of both lifetimes, which is what a pathwise consumer has: on `{t_L < ζ}` SB2(1)'s link forces `0 < ζr`
(`zeta_pos_of_link`).

The two forms are equivalent in content because a flow line's lifetime is almost surely zero or almost surely positive
(`ae_lifetime_eq_zero_or_ne_of_isFlowLine`, the seed's threshold condition being deterministic, Lemma GW0):
`hasRelStageOrderingP_of_hasRelStageOrdering`. The landed `Lv.ae_hasRelStageOrdering_of_sb2UpperLaunch(_dyCover)` are
re-proved for the corrected predicate (`ae_hasRelStageOrderingP_of_sb2UpperLaunch(_dyCover)`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lw

open Lv

/-- **A flow line has zero lifetime almost surely or almost never** (the seed is a threshold state of its force word
or not; Lemma GW0). The `IsFlowLine` form of `GW2aCont.ae_lifetime_eq_zero_or_ne`. -/
theorem ae_lifetime_eq_zero_or_ne_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {Q : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {α : Ω → ℝ≥0 → ℂ}
    {ζ : Ω → ℝ≥0∞} (hfl : IsFlowLine κ b J x θ Q h α ζ) : (∀ᵐ ω ∂Q, ζ ω = 0) ∨ ∀ᵐ ω ∂Q, ζ ω ≠ 0 := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hC, -⟩ := hfl
  by_cases hthr : ForceWord.ThresholdCondition (flowLineRhoL κ b J x θ) (flowLineRhoR κ b J x θ) 0
      (flowLineXL b J x) (flowLineXR b J x)
  · exact Or.inl (hC.1.ae_lifetime_eq_zero_of_threshold hthr)
  · refine Or.inr ?_
    filter_upwards [hC.1.2.2.2.2] with ω hp h0
    exact hthr ((GW0.lifetime_eq_zero_iff hp).1 h0)

/-- **The relative pair of SB3's step, with pathwise positivity** (the corrected `Lv.HasRelStageOrdering`): as there,
but the ordering through all available endpoints holds almost surely at every sample where both lifetimes are
positive. -/
def HasRelStageOrderingP (κ ψ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (c : Chart) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (L : Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (ζL : Ω → ℝ≥0∞) : Prop :=
  ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ)
    (ηr : Ω → ℝ≥0 → ℂ) (ζr : Ω → ℝ≥0∞),
    IsPiecewiseConstantBoundaryData b' jumps' ∧ (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) ∧
    IsGFFWithBoundaryData Q h' b' jumps' ∧ m ≤ 0 ∧
    IsFlowLine κ b' jumps' 0 (-(Real.pi / 2)) Q h' (GW2aSingle.chosenTrace W ζL) ζL ∧
    IsFlowLine κ b' jumps' m ψ Q h' ηr ζr ∧
    (∀ᵐ ω ∂Q, IsRemainderLink c (η ω) (ζ ω) (L ω) (ηr ω) (ζr ω)) ∧
    ∀ᵐ ω ∂Q, 0 < ζL ω → 0 < ζr ω → ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ ζL ω → (a : ℝ≥0∞) ≤ ζr ω →
      HasOrderedProperCompletions (GW2aSingle.chosenTrace W ζL ω) d (ηr ω) a

/-- **The corrected predicate from the landed one**: the lifetime dichotomy of both flow lines moves the positivity
premises inside the almost-sure event. -/
theorem hasRelStageOrderingP_of_hasRelStageOrdering {κ ψ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {c : Chart} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {L : Ω → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {ζL : Ω → ℝ≥0∞} (hR : HasRelStageOrdering κ ψ Q h c η ζ L W ζL) :
    HasRelStageOrderingP κ ψ Q h c η ζ L W ζL := by
  obtain ⟨b', jumps', h', m, ηr, ζr, hb', hct, hgff, hm, hα, hηr, hlink, hord⟩ := hR
  refine ⟨b', jumps', h', m, ηr, ζr, hb', hct, hgff, hm, hα, hηr, hlink, ?_⟩
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hα with hL0 | hLp
  · filter_upwards [hL0] with ω hω hpos
    exact absurd hω hpos.ne'
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hηr with hr0 | hrp
  · filter_upwards [hr0] with ω hω _ hpos
    exact absurd hω hpos.ne'
  filter_upwards [hord (hLp.mono fun _ hω => pos_iff_ne_zero.2 hω) (hrp.mono fun _ hω => pos_iff_ne_zero.2 hω)]
    with ω hω _ _
  exact hω

/-- SB2(1)'s link forces a positive relative lifetime whenever the upper flow visits `L` before its lifetime. -/
theorem zeta_pos_of_link {c : Chart} {η ηr : ℝ≥0 → ℂ} {ζ ζr : ℝ≥0∞} {L : ℝ}
    (hlink : IsRemainderLink c η ζ L ηr ζr) (hv : firstVisit η ζ L < ζ) : 0 < ζr := by
  obtain ⟨σ, hσ0, -, -, hσ⟩ := hlink hv
  have htL : (((firstVisit η ζ L).toNNReal + σ 0 : ℝ≥0) : ℝ≥0∞) < ζ := by
    rw [hσ0, add_zero, ENNReal.coe_toNNReal (hv.trans_le le_top).ne]; exact hv
  simpa using (hσ 0).1.2 htL

/-- **SB3's relative stage ordering, corrected form**: `Lv.ae_hasRelStageOrdering_of_sb2UpperLaunch` for
`HasRelStageOrderingP`. -/
theorem ae_hasRelStageOrderingP_of_sb2UpperLaunch (hSB2 : SB2UpperLaunchStatement.{u})
    (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    (k : ℕ) {u ψ : ℝ} (hu : u ≤ 0) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps u ψ P h η ζ)
    (hS1 : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k =
          some (c, θ) →
      HasRelStageOrderingP κ ψ (condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h c η ζ
        (fun ω => realMin (lowerPrefix κ b jumps E k u ω))
        (fun t ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).1 t)
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2) := by
  filter_upwards [ae_hasRelStageOrdering_of_sb2UpperLaunch hSB2 hSB1 hS6 h13 hκ hκ4 hb hh hE hreg k hu hψ hL hH
    hη hS1] with ω₀ hω₀ c θ hcθ
  exact hasRelStageOrderingP_of_hasRelStageOrdering (hω₀ c θ hcθ)

/-- `ae_hasRelStageOrderingP_of_sb2UpperLaunch` with SB1 and S6 discharged by the landed PROVE-SB-W5 results. -/
theorem ae_hasRelStageOrderingP_of_sb2UpperLaunch_dyCover (hSB2 : SB2UpperLaunchStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    (k : ℕ) {u ψ : ℝ} (hu : u ≤ 0) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps u ψ P h η ζ)
    (hS1 : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k =
          some (c, θ) →
      HasRelStageOrderingP κ ψ (condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h c η ζ
        (fun ω => realMin (lowerPrefix κ b jumps E k u ω))
        (fun t ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).1 t)
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2) := by
  filter_upwards [ae_hasRelStageOrdering_of_sb2UpperLaunch_dyCover hSB2 h12 h13 h12₀ h13₀ hDy hDy₀ hκ hκ4 hb hh
    hE hreg k hu hψ hL hH hη hS1] with ω₀ hω₀ c θ hcθ
  exact hasRelStageOrderingP_of_hasRelStageOrdering (hω₀ c θ hcθ)

end InteractingSLE.Theorem14.SB.Lw
