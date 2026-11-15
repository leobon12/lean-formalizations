/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2InteriorQFixed

/-!
# GW2's light cone from the corrected interior-switch schedule condition

Packet PROVE-T14-GW2Q2. The containment consumer uses the schedule condition only
for `k < l.length`. At every later index the launch record is `none`.
The source-facing light-cone conclusion is unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Tip

open GW2Cone GW2Schedule GW2Later GW2Sched GW2aMulti

/-- GW1's containment induction only needs interior tips at launched instructions. -/
theorem ae_physSet_subset_of_step_launched (hStep : GB6PastStepStatement.{u})
    (hBR4a : BR4a.BR4aStatement.{u}) (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    {x : ℝ} (hx : x = 0 ∨ x ∈ lowerArcRoots κ b jumps) {l : List (ℝ × ℝ≥0)}
    (hl : ∀ p ∈ l, p.1 ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hlt : l.Pairwise (fun p q => p.2 < q.2))
    (hint : ∀ k < l.length, ∀ᵐ ω ∂P,
      AllSucc (schedDelta 0 l) (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k →
      SwitchTipsInterior ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) :
    ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
      (fun k => E ⟨x, true, scheduleProgram 0 l⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) := by
  have hlaunch : ∀ k, ∀ᵐ ω ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
      c.tipSet (stoppedDriver ⟨x, true, scheduleProgram 0 l⟩
        (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k)
        (pieceStop ⟨x, true, scheduleProgram 0 l⟩
          (fun j => E ⟨x, true, scheduleProgram 0 l⟩ j ω) k) ⊆
        counterflowCompletedRange (fun t => W' t ω) := by
    intro k
    by_cases hk : k < l.length
    · exact ae_later_piece_subset_of_step hStep hBR4a hGB6 h13 h13₀ hκ hκ4 hb hh
        hcf hζ' hE hR hx hl hlt (hint k hk)
    · refine Eventually.of_forall fun ω c θ hlaunch => ?_
      rw [launches_run_succ_of_length_le κ b jumps _ _ (by
        change (scheduleProgram 0 l).length ≤ k
        rw [length_scheduleProgram]
        exact Nat.le_of_not_gt hk)] at hlaunch
      exact absurd hlaunch (by simp)
  apply ae_physSet_subset_of_launches κ b jumps (isFlowProgram_scheduleProgram 0 l)
    (E := fun j ω => E ⟨x, true, scheduleProgram 0 l⟩ j ω) _ hlaunch
  rcases hx with rfl | hv
  · exact Eventually.of_forall fun ω => Or.inr rfl
  · exact GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13 h13
      (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ' hv
      (pos_of_mem_lowerArcRoots hv) le_rfl

/-- **Lemma GW2, version 2, on GB9a's schedule set** (supplement pp. 621–623). From Theorem 1.3 (frozen type, at `u`
and `0`), BR6 (the forced arcs), BR4a (the pair at a boundary root), GB6's restart law (the first piece), GB6
conditioned on the piece's prefix (GW1's inductive step, `gb6PastStepStatement_of_prefix`), GB9a's set `Q` (interior
switching tips) and the tip exhaustion for every `Q`. -/
theorem gw2LightConeR51Statement_of_interiorQ' (hT13 : Exist.Theorem13Statement.{u})
    (hT13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (hQ : GW2InteriorScheduleQStatement'.{u}) (hEx : GW2TipExhaustionAllQStatement.{u}) :
    GW2LightConeR51Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  obtain ⟨Q, hQc, hQd, hQpos, hQint⟩ := hQ κ hκ hκ4 b jumps hb P h hh Θ hΘ hΘc
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ?_⟩
  have hStep := gb6PastStepStatement_of_prefix hG hT13
  have hSc := countable_setOf_isSchedule hΘc hQc
  have hRc := countable_lowerArcRoots κ b jumps
  have hsched : ∀ x : ℝ, (x = 0 ∨ x ∈ lowerArcRoots κ b jumps) → ∀ l ∈ {l | IsSchedule Θ Q l},
      ∀ᵐ ω ∂P, ExplState.physSet κ b jumps ⟨x, true, scheduleProgram 0 l⟩
        (fun k => E ⟨x, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    fun x hx l hl => ae_physSet_subset_of_step_launched hStep hBR4a hGB6 hT13 hT13₀ hκ hκ4 hb hh hcf hζ' hE hreg hx
      (mem_Icc_of_isSchedule hΘ hl) hl.2 (hQint E hE hreg x hx l hl)
  have h0 : ∀ᵐ ω ∂P, ∀ l ∈ {l | IsSchedule Θ Q l}, ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩
      (fun k => E ⟨0, true, scheduleProgram 0 l⟩ k ω) ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hSc).2 fun l hl => hsched 0 (Or.inl rfl) l hl
  have harc : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps,
      ((↑) : ℝ → ℂ) '' Icc 0 v ⊆ counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => gw2ForcedArcStatement_of_br6 hBR6
      (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀) hT13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' v hv
  have hv : ∀ᵐ ω ∂P, ∀ v ∈ lowerArcRoots κ b jumps, ∀ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (fun k => E ⟨v, true, scheduleProgram 0 l⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff hRc).2 fun v hv => (ae_ball_iff hSc).2 fun l hl => hsched v (Or.inr hv) l hl
  have hEQ := hEx κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd Q hQc hQd hQpos E hE hreg
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
    ae_all_iff.2 fun q => hEQ (GW2aSingle.chosenTrace W' ζ') hγtop (q : ℝ).toNNReal
  filter_upwards [hγ, hζ', hdrv, h0, harc, hv, hex] with ω hγω hζω hdω h0ω harcω hvω hexω
  rw [hζω] at hγω hdω
  have hWc : Continuous fun t => W' t ω := by
    have hc := hdω.2
    simp only [ENNReal.coe_lt_top, ofPred_true] at hc
    exact continuousOn_univ.1 hc
  exact closure_union_zero_eq hγω.1 hWc hdω.1 (hγω.2 rfl)
    (boundaryLightConeFamily_subset h0ω harcω hvω) hexω

/-- **Theorem 1.4, light cone, version 2**, provider shape: GB9a's corrected schedule
condition is discharged by parametric Theorem 1.2 and Theorem 1.3. The remaining
inputs are BR6, BR4a, GB6, the exhaustion for every `Q`, and Lemma GW2a.
This is a conditional assembly theorem, not a sealed provider. -/
theorem completedRange_eq_closure_lightCone_of_param (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hBR6 : BR6.BR6Statement.{u}) (hBR4a : BR4a.BR4aStatement.{u})
    (hGB6 : Supp8.GB6.GB6RestartStatement.{u}) (hG : GB6PrefixPairStatement.{u})
    (h12p : Exist.Staged.Theorem12ParamStatement.{u}) (hEx : GW2TipExhaustionAllQStatement.{u})
    (hGW2a : GW2aContainmentStatement.{u})
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
  have hQ := gw2InteriorScheduleQStatement'_of_param h13 h12p
  have hGW2 := gw2LightConeR51Statement_of_interiorQ' h13 h13₀ hBR6 hBR4a hGB6 hG hQ hEx
  obtain ⟨Q, hQc, hQd, hQpos, hQ'⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQpos, fun E hE hreg => ⟨hQ' E hE hreg, fun 𝒞 h𝒞 h𝒞p => ?_⟩⟩
  have hcont : ∀ᵐ ω ∂P, ∀ p ∈ 𝒞,
      ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff h𝒞).2 fun p hp => hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE p (h𝒞p p hp)
  filter_upwards [hQ' E hE hreg, hcont] with ω h1 h2
  exact closure_union_union_eq h1 (iUnion₂_subset h2)

end InteractingSLE.Theorem14.GW2Tip
