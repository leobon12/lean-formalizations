/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CsJoint
import InteractingSLE.Spec.Supplement.SB2MjFilt

/-!
# The joint line family of a stage in B's own time (D51 items 1–2)

Packet PROVE-SB2-CONDFIN (round 10, D51). The line family of B's stage `ℓ` (a tail stage or the root `ℓ = relOff`) in
the form of NOJUMP's premises (`Nd.SB2LowerStageVersionStatement5`, `Ne.SB2LowerRootVersionStatement8`): the line
filtration `𝓖 t` = the upper past joined with B's past capped at the deterministic B-time `t` (generated, through
instruction `ℓ + 1`), the retained set `A₁ t` and the JOINT set `A₂ t`.

* **`exists_jointLineFamily`**: a filtration `𝓖` with `𝓖 t` exactly the joined capped pasts, and line sets `A₁`,
  `A₂` almost surely `fillVer (A ∪ B_{<ℓ})` and `fillVer (A ∪ B_{≤ℓ,t})`, with the line facts that K2 consumes for the
  union (`Cr.ae_k2_root`'s `hBm`, `hBc`, `hBl`, `hloc`) and `A₁`'s facts (measurable, field-determined, local).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cs

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The joint line family of B's stage `ℓ`**: the line filtration of joined capped pasts, the retained set `A₁ t`
and the joint set `A₂ t`, with the union's line facts and the retained set's facts. -/
theorem exists_jointLineFamily (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
        pastSigma κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
          ω ∧
        A₂ t ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
            (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
            (ℓ + 1) ω) ω) ∧
      ∀ t : ℝ≥0,
        Measurable[mΩ, hittingSigma] (A₁ t) ∧ Measurable[mΩ, hittingSigma] (A₂ t) ∧
        MeasurableSpace.comap (A₁ t) hittingSigma ≤
          aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P ∧
        IsLocalSet (A₁ t) (centredField h u₀) P ∧ IsLocalSet (A₂ t) (centredField h u₀) P ∧
        (∀ ω, A₁ t ω ⊆ H ∧ IsOpen (H \ A₁ t ω)) ∧ (∀ ω, A₂ t ω ⊆ H ∧ IsOpen (H \ A₂ t ω)) ∧
        Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω) ∧
        (∀ ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω))) ∧
        IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (centredField h u₀) P ∧
        IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω) (centredField h u₀) P := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hlw := hE' _ hw
  set s₁ := Lu.upperSpec u l with hs₁
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  set E₁ := StagedReg.regFam E s₁ with hE₁
  set E₂ := StagedReg.regFam E w with hE₂
  -- the line filtration
  have hle : ∀ t : ℝ≥0, pastSigma κ b jumps s₁ E₁ k ⊔
      pastSigma κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) E₂ (ℓ + 1) ≤ mΩ := fun t =>
    sup_le (hup.2.1 k) ((isStagedHistory_capSpec (τ := (t : ℝ≥0∞)) hb hlw (hreg' _) hℓ hwℓ).2.1 (ℓ + 1))
  have hmono : Monotone fun t : ℝ≥0 => pastSigma κ b jumps s₁ E₁ k ⊔
      pastSigma κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) E₂ (ℓ + 1) := fun s t hst =>
    sup_le_sup_left (Mj.pastSigma_capSpec_mono_real E₂ (hreg' _) hℓ.le hwℓ (ENNReal.coe_le_coe.2 hst)) _
  let 𝓖 : Filtration ℝ≥0 mΩ := ⟨fun t => pastSigma κ b jumps s₁ E₁ k ⊔
      pastSigma κ b jumps (capSpec w ℓ (-(Real.pi / 2)) (t : ℝ≥0∞)) E₂ (ℓ + 1), hmono, hle⟩
  -- the sets at every B-time
  choose A₁ A₂ hA₁m hA₂m hd₁ hl₁ hl₂ hc₁ hc₂ hUm hUc hUl hUloc hae using fun t : ℝ≥0 =>
    exists_jointStageSets (P := P) h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ (t : ℝ≥0∞) hu₀
  exact ⟨𝓖, A₁, A₂, fun t => rfl, hae, fun t => ⟨hA₁m t, hA₂m t, hd₁ t, hl₁ t, hl₂ t, hc₁ t, hc₂ t, hUm t, hUc t,
    hUl t, hUloc t⟩⟩

end InteractingSLE.Theorem14.SB.Cs
