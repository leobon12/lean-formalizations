/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2Tip
import InteractingSLE.Spec.Supplement.GW2ConeArc
import InteractingSLE.Spec.Supplement.BR3Ref
import InteractingSLE.Spec.Theorem14

/-!
# Lemma GW2 and the light-cone anchor from the version-2 (R51) tip exhaustion

Packet PROVE-T14-TIP6. The existing chain to the light-cone anchor (`GW2Cone.gw2LightConeStatement_of_inputs`,
`Theorem14.completedRange_eq_closure_lightCone_of_inputs`, `Wire.completedRange_eq_closure_lightCone_of_openR51`)
consumes `GW2Cone.GW2TipExhaustionStatement`, which quantifies over every staged family; by ruling R51 only its
version-2 form `GW2Tip.GW2TipExhaustionR51Statement` (staged families with almost surely continuous launched pieces) is
provable. This file runs the same chain with the version-2 form:

* `GW2LightConeR51Statement`: Lemma GW2 for the staged families with `StagedPiecesRegular`;
* `gw2LightConeR51Statement_of_inputs`: from Theorem 1.3 (frozen type), the three containment steps of GW2 and the
  version-2 tip exhaustion (the proof of `GW2Cone.gw2LightConeStatement_of_inputs` verbatim, the regularity hypothesis
  passed to the exhaustion);
* `completedRange_eq_closure_lightCone_of_tipR51`: the version-2 light-cone anchor's shape (that of
  `Wire.completedRange_eq_closure_lightCone_of_openR51`) from Theorem 1.3 (frozen type, at `u` and `0`), BR6, the two
  schedule containments, the version-2 tip exhaustion and Lemma GW2a (conditional helper; not the provider).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2Tip

open GW2Cone

/-- **Named statement: Lemma GW2, version-2 form** (ruling R51): `Theorem14.GW2LightConeStatement` for the staged
families whose launched pieces are almost surely continuous curves (`StagedPiecesRegular`). -/
def GW2LightConeR51Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ Θ : Set ℝ, Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) → Θ.Countable →
      Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ →
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
          counterflowCompletedRange (fun t => W' t ω)

/-- **Lemma GW2, version-2 form**, from its four named steps (the tip exhaustion in its version-2 form) and Theorem 1.3:
the proof of `GW2Cone.gw2LightConeStatement_of_inputs`. -/
theorem gw2LightConeR51Statement_of_inputs (hT13 : Exist.Theorem13Statement.{u})
    (hC0 : GW2ScheduleContainmentStatement.{u}) (hArc : GW2ForcedArcStatement.{u})
    (hCv : GW2ArcScheduleContainmentStatement.{u}) (hEx : GW2TipExhaustionR51Statement.{u}) :
    GW2LightConeR51Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos, hQ⟩ := hEx κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ?_⟩
  have hSc := countable_setOf_isSchedule hΘc hQc
  have hRc := countable_lowerArcRoots κ b jumps
  have h0 : ∀ᵐ ω ∂P, ∀ l ∈ {l | IsSchedule Θ Q l}, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
      (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hSc).2 fun l hl =>
      hC0 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE l (mem_Icc_of_isSchedule hΘ hl) hl.2
  have harc : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps,
      ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => hArc κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv
  have hv : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps, ∀ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => (ae_ball_iff hSc).2 fun l hl =>
      hCv κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE v hv l (mem_Icc_of_isSchedule hΘ hl) hl.2
  obtain ⟨b', J', h', -, -, hfl⟩ := hcf
  have hκ' : 0 < 16 / κ := by positivity
  have hγ := GW2aSingle.ae_chosenTrace hT13 hκ' hfl
  have hdrv := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hγtop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (GW2aSingle.chosenTrace W' ζ' ω) := by
    filter_upwards [hγ, hζ'] with ω hω hζ
    rw [hζ] at hω
    exact hω.1
  have hex : ∀ᵐ ω ∂P, ∀ q : ℚ, GW2aSingle.chosenTrace W' ζ' ω (q : ℝ).toNNReal ∈ H →
      -(GW2aSingle.chosenTrace W' ζ' ω (q : ℝ).toNNReal)⁻¹ ∈
        closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω)) :=
    ae_all_iff.2 fun q => hQ E hE hreg (GW2aSingle.chosenTrace W' ζ') hγtop (q : ℝ).toNNReal
  filter_upwards [hγ, hζ', hdrv, h0, harc, hv, hex] with ω hγω hζω hdω h0ω harcω hvω hexω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  exact closure_union_zero_eq hγω.1 hWc hdω.1 (hγω.2 rfl)
    (boundaryLightConeFamily_subset h0ω harcω hvω) hexω

/-- **Theorem 1.4, light cone, version 2** (`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`, R51),
provider shape, from Theorem 1.3 (frozen type, at `u` and `0`), BR6, the two schedule containments of GW2, the
version-2 tip exhaustion and Lemma GW2a (conditional helper; not the provider). -/
theorem completedRange_eq_closure_lightCone_of_tipR51 (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u})
    (hC0 : GW2ScheduleContainmentStatement.{u}) (hCv : GW2ArcScheduleContainmentStatement.{u})
    (hEx : GW2TipExhaustionR51Statement.{u}) (hGW2a : GW2aContainmentStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps := by assumption)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ' := by assumption) (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤ := by assumption)
    {Θ : Set ℝ} (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by assumption)
    (hΘc : Θ.Countable := by assumption)
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ := by assumption) :
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          StagedPiecesRegular κ b jumps P spec (E spec)) →
        (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
            counterflowCompletedRange (fun t => W' t ω)) ∧
        ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
          ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
              (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
              {0}) =
            counterflowCompletedRange (fun t => W' t ω) := by
  have hGW2 := gw2LightConeR51Statement_of_inputs h13 hC0
    (gw2ForcedArcStatement_of_br6 hBR6 (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) h13) hCv hEx
  obtain ⟨Q, hQc, hQd, hQpos, hQ⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ⟨hQ E hE hreg, fun 𝒞 h𝒞 h𝒞p => ?_⟩⟩
  have hcont : ∀ᵐ ω ∂P, ∀ p ∈ 𝒞,
      ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff h𝒞).2 fun p hp => hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE p (h𝒞p p hp)
  filter_upwards [hQ E hE hreg, hcont] with ω h1 h2
  exact closure_union_union_eq h1 (iUnion₂_subset h2)

end GW2Tip

end Theorem14

end InteractingSLE
