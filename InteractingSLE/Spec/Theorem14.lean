/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem14Inputs

/-!
# Theorem 1.4 assembled from its named inputs

Packet PROVE-SEC7-D2. The four frozen Theorem 1.4 anchors (R29) — the light cone
(`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`), the frontiers
(`IsCenteredCounterflowDriver.boundaryWalks_frontiers`), the component kernels
(`IsCenteredCounterflowDriver.componentKernels`) and the non-vacuity companion `exists_isStagedHistory` — are proved
here with exactly their frozen binders and conclusions from the named inputs of `Theorem14Inputs.lean` (Lemmas
GW2, GW2a, GW3, GW4, GW6, SB1–SB5 and the GW1/GW2a construction of the supplement).

Proved here (the steps between the supplement lemmas and the frozen statements):

* the second light-cone clause (adding any fixed countable collection of prescribed boundary-continued histories
  gives the same closed range) from the first and GW2a's containment, because the range is then closed
  (`closure_union_union_eq`; p. 623: "Its closed union equals the counterflow range whenever that collection contains
  the GW2 family");
* the containment of both walks in the range from GW2a, the walks being boundary-continued histories with the extreme
  angles `∓π/2` (`isBoundaryContinuedProgram_boundaryWalkSpec`);
* `exists_isStagedHistory` from the construction of one prescribed history at a time (a choice for each history).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

/-- If `closure (F ∪ {0}) = R` and `X ⊆ R`, then also `closure (F ∪ X ∪ {0}) = R` (`R` is closed). -/
theorem closure_union_union_eq {F X R : Set ℂ} (h1 : closure (F ∪ {0}) = R) (h2 : X ⊆ R) :
    closure (F ∪ X ∪ {0}) = R := by
  have hR : IsClosed R := h1 ▸ isClosed_closure
  refine Subset.antisymm (closure_minimal ?_ hR) ?_
  · have hF : F ∪ {0} ⊆ R := h1 ▸ subset_closure
    intro z hz
    rcases hz with (hz | hz) | hz
    · exact hF (Or.inl hz)
    · exact h2 hz
    · exact hF (Or.inr hz)
  · rw [← h1]
    exact closure_mono (union_subset_union_left _ subset_union_left)

/-- The boundary walks of GW1 are boundary-continued histories when their angle lies in `[−π/2, π/2]`. -/
theorem isBoundaryContinuedProgram_boundaryWalkSpec (b : ℝ → ℝ) (jumps : Finset ℝ) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) :
    IsBoundaryContinuedProgram (boundaryWalkSpec b jumps θ right).2.2 := by
  intro θ' t hmem
  simp only [boundaryWalkSpec, List.mem_flatten, List.mem_replicate] at hmem
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hmem
  simp only [List.mem_cons, Sum.inl.injEq, Prod.mk.injEq, reduceCtorEq, List.not_mem_nil, or_false]
    at hl
  rw [hl.1]
  exact hθ

/-- **Theorem 1.4, light cone** (Specification pp. 4–5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone`, from Lemma GW2 (with GW0) and Lemma GW2a. -/
theorem completedRange_eq_closure_lightCone_of_inputs (hGW2 : GW2LightConeStatement.{u})
    (hGW2a : GW2aContainmentStatement.{u}) {κ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (Θ : Set ℝ) (hΘ : Θ ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2)) (hΘc : Θ.Countable)
    (hΘd : Ioo (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure Θ) :
    ∃ Q : Set ℝ≥0, Q.Countable ∧ Dense Q ∧ (∀ q ∈ Q, 0 < q) ∧
      ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
        (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
          IsStagedHistory κ b jumps P h spec (E spec)) →
        (∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪ {0}) =
            counterflowCompletedRange (fun t => W' t ω)) ∧
        ∀ 𝒞 : Set (List Instr), 𝒞.Countable → (∀ p ∈ 𝒞, IsBoundaryContinuedProgram p) →
          ∀ᵐ ω ∂P, closure (boundaryLightConeFamily κ b jumps Θ Q (fun spec k => E spec k ω) ∪
              (⋃ p ∈ 𝒞, ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω)) ∪
              {0}) =
            counterflowCompletedRange (fun t => W' t ω) := by
  obtain ⟨Q, hQc, hQd, hQpos, hQ⟩ := hGW2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' Θ hΘ hΘc hΘd
  refine ⟨Q, hQc, hQd, hQpos, fun E hE => ⟨hQ E hE, fun 𝒞 h𝒞 h𝒞p => ?_⟩⟩
  have hcont : ∀ᵐ ω ∂P, ∀ p ∈ 𝒞,
      ExplState.physSet κ b jumps ⟨0, false, p⟩ (fun k => E ⟨0, false, p⟩ k ω) ⊆
        counterflowCompletedRange (fun t => W' t ω) :=
    (ae_ball_iff h𝒞).2 fun p hp => hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE p (h𝒞p p hp)
  filter_upwards [hQ E hE, hcont] with ω h1 h2
  exact closure_union_union_eq h1 (iUnion₂_subset h2)

/-- **Theorem 1.4, frontiers** (Specification p. 5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.boundaryWalks_frontiers`, from Lemma GW2a (the walks lie in the range), SB1–SB5 with
the GW2 exhaustion (no range point beyond either walk) and Lemma GW6. -/
theorem boundaryWalks_frontiers_of_inputs (hGW2a : GW2aContainmentStatement.{u})
    (hSB : SBFrontierStatement.{u}) (hGW6 : GW6Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec)) :
    ∀ᵐ ω ∂P,
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          rightSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) = ∅) ∧
      (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
          (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) ⊆
          counterflowCompletedRange (fun t => W' t ω) ∧
        counterflowCompletedRange (fun t => W' t ω) ∩
          leftSideOf (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
            (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) = ∅) ∧
      (interior (((↑) : ℝ → ℂ) ⁻¹' counterflowCompletedRange (fun t => W' t ω)) = ∅ →
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) 0 ω).2 = ⊤ ∧
          (E (boundaryWalkSpec b jumps (Real.pi / 2) false) 0 ω).2 = ⊤) := by
  have hpi := Real.pi_pos
  have hR := hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
      ⟨le_rfl, by linarith⟩ true)
  have hL := hGW2a κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
    (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2)
      ⟨by linarith, le_rfl⟩ false)
  filter_upwards [hR, hL, hSB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    hGW6 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω h1 h2 h3 h4
  exact ⟨⟨h1, h3.1⟩, ⟨h2, h3.2⟩, h4⟩

/-- **Theorem 1.4, component kernels** (Specification p. 5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, from Lemma GW3 (the charts) and Theorem GW4 (the kernels). -/
theorem componentKernels_of_inputs (hGW3 : GW3ChartStatement.{u}) (hGW4 : GW4KernelStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec)) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  (hGW3 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE).and
    (hGW4 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE)

/-- **Realizations of the staged histories exist** (companion of Theorem 1.4), with exactly the binders and
conclusion of the frozen `exists_isStagedHistory`, from the construction of one prescribed history at a time (GW1,
GW2a, BW1–BW2): the realizations of different histories are chosen independently. -/
theorem exists_isStagedHistory_of_inputs (hCon : StagedHistoryConstructionStatement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) :
    ∃ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, ∀ spec : ExplSpec,
      IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec) := by
  classical
  refine ⟨fun spec => if hs : IsBoundaryContinuedProgram spec.2.2 then
    (hCon κ hκ hκ4 b jumps hb P h hh spec hs).choose else fun _ _ => (fun _ => 0, 0), fun spec hs => ?_⟩
  simp only [hs, ↓reduceDIte]
  exact (hCon κ hκ hκ4 b jumps hb P h hh spec hs).choose_spec

end Theorem14

end InteractingSLE
