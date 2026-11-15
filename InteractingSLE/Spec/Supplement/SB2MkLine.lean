/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MkPull
import InteractingSLE.Spec.Supplement.SB2MjFilt

/-!
# SB2(2)'s lower lines with one explored set: marks, union mean inputs and the line family

Packet PROVE-SB2-LCMEAN, round 8. Round 4's line sets (`Mg.exists_sb2LowerStageSets_marked`) and the explored set with
the explored mean (`Mi.exists_capMean_hind`, rounds 6–7) were different objects. With the filled explored set of
`Mk.exists_capFill_hind` they are one:

* **`exists_sb2LowerSets_fill`**: at SB2(2)'s lower piece `ℓ` capped at `τ`, the retained set `A₁` (round 4's filled
  line version of `A ∪ B_{<ℓ}`) and the explored set `A₂` (the filled line version of `B_{≤ℓ,τ}`) with every set-level
  input of the stage pull-back route (`Ln.ae_chartTransport_eq_couplingMean_of_stagePullback`: measurability, `A₁`'s
  field measurability, locality of `A₁`, `A₂`, `A₁ ∪ A₂`, unbounded lower-union components), the union's
  joint-past measurability and marks (K2's line set), and, almost surely on the capped launch event, `A₂`'s complement
  (the post-cap chart domain), `corr₂`, `dom₂`, `hind₂` and (at an upper launch) the stage pull-back given finite
  fibres of the boundary map (`ae_isStagePullback_fill`);
* **`exists_sb2LineFamily_fill`**: the same at every real cap `t`, with the filtration `t ↦` (upper past at `k`) `⊔`
  (capped walk past at `t`) of `Mj.capFiltration` (K2's `hBm`, `hBc`, `hloc` and the route's inputs for one family).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mk

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

open Mi in
/-- **SB2(2)'s lower-line sets with one explored set**: the retained set `A₁` and the filled explored set `A₂` at the
lower piece `ℓ` capped at `τ`, with the set-level inputs of the stage pull-back route, the union's joint-past
measurability and marks, and the explored-side package of `exists_capFill_hind`. -/
theorem exists_sb2LowerSets_fill (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (τ : ℝ≥0) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ A₁ A₂ : Ω → Set ℂ,
      Measurable[mΩ, hittingSigma] A₁ ∧ Measurable[mΩ, hittingSigma] A₂ ∧
      MeasurableSpace.comap A₁ hittingSigma ≤
        aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P ∧
      IsLocalSet A₁ (centredField h u₀) P ∧ IsLocalSet A₂ (centredField h u₀) P ∧
      IsLocalSet (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P ∧
      Measurable[pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
          pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1), hittingSigma]
        (fun ω => A₁ ω ∪ A₂ ω) ∧
      IsHistoryAvoidanceLocal (pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
          pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
        (fun ω => A₁ ω ∪ A₂ ω) (centredField h u₀) P ∧
      (∀ ω, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) ∧ (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      (∀ᵐ ω ∂P, A₁ ω = fillVer (fun ω =>
          WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
          WalkLaw.stageSet κ b jumps
            (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
        A₂ ω = fillVer (WalkLaw.stageSet κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ω) ∧
      (∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ ω), ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ ω)) z)) ∧
      (∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω), ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z)) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ τ →
        H \ A₂ ω = ((ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) τ)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω)
            (ℓ + 1)).2.2.2.2.1.dom : Set ℂ) ∧
        (∀ v ∈ H, (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 v ∈ A₂ ω ↔
          v ∈ fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ ω)
            (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ ω)) ∧
        H \ ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).dom : Set ℂ) ⊆ A₂ ω) ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ τ →
        (ExplState.run κ b jumps (Lu.upperSpec u l)
          (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none →
        ∃ g : ℂ → ℂ, ContinuousOn g Hbar ∧ EqOn g (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 H ∧
          ((∀ z, (g ⁻¹' {z} ∩ Hbar).Finite) →
            Ln.IsStagePullback (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω) g (A₁ ω) (A₂ ω)
              {w | (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 w ∈ A₁ ω}
              (fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ ω)
                (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ ω)))) ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g →
        ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
          ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ τ →
          ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g ω φ = ∫ z, v z * φ z) →
            EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (β ω, -(Real.pi / 2), recOf (τ : ℝ≥0∞)
              (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))).mean
                (fwdMap (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ ω)
                  (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ ω)
                  ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).1 z)) -
              chiC κ * ((logDerivFwd (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ τ ω)
                  (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ τ ω)
                  ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).1 z)).im +
                (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.2 z)) (H \ A₂ ω) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hcap := isStagedHistory_capSpec (τ := (τ : ℝ≥0∞)) hb (hE' _ hw) (hreg' _) hℓ hwℓ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  set s₁ := Lu.upperSpec u l with hs₁
  set s₂ := capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (τ : ℝ≥0∞) with hs₂
  set E₁ := StagedReg.regFam E s₁ with hE₁
  set E₂ := StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) with hE₂
  -- the retained set (round 4)
  obtain ⟨hA1, ho1, hd1, hloc1⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k ℓ
  obtain ⟨-, -, -, hloc⟩ := Lcd.stageUnion_markedLocal h12p h13 hκ hκ4 hb hh hup hcap (hreg' _) (hreg' _)
    hu₀ k (ℓ + 1)
  have h𝓜₁ : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ ℓ ≤ mΩ := sup_le (hup.2.1 k) (hcap.2.1 ℓ)
  have h𝓜 : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤ mΩ :=
    sup_le (hup.2.1 k) (hcap.2.1 (ℓ + 1))
  have h𝓜₁𝓜 : pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ ℓ ≤
      pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) :=
    sup_le_sup_left (pastSigma_mono s₂ E₂ (Nat.le_succ ℓ)) _
  have h𝓜₂𝓜 : pastSigma κ b jumps s₂ E₂ (ℓ + 1) ≤
      pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1) := le_sup_right
  obtain ⟨B₁, hB₁m, hB₁c, hB₁ae, hB₁loc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, h𝓜₁⟩
    (fun ω => union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω))
    ho1 hA1 hloc1
  obtain ⟨hA₁m, hA₁c, -, hA₁l⟩ := fillVer_package hh0 h𝓜₁ hB₁c hB₁m hB₁loc
  -- the explored set (round 8)
  obtain ⟨A₂, hA₂m, hA₂c, hA₂fill, hA₂sub, hA₂l, -, hA₂cl, hA₂mean⟩ :=
    exists_capFill_hind h12p h13 hθ true hκ hκ4 hb hh hE hER ℓ hℓ hwℓ τ hu₀
  -- the union
  have hUm : Measurable[pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1), hittingSigma]
      fun ω => fillVer B₁ ω ∪ A₂ ω := by
    let _ : MeasurableSpace Ω := pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1)
    exact measurable_union_hitting (hA₁m.mono h𝓜₁𝓜 le_rfl) (hA₂m.mono h𝓜₂𝓜 le_rfl)
  have hUloc : IsHistoryAvoidanceLocal (pastSigma κ b jumps s₁ E₁ k ⊔ pastSigma κ b jumps s₂ E₂ (ℓ + 1))
      (fun ω => fillVer B₁ ω ∪ A₂ ω) (centredField h u₀) P := by
    refine Lv.isHistoryAvoidanceLocal_of_ae_enlargement hloc ?_ fun U hUH => hUm (measurableSet_avoid U.isOpen hUH)
    filter_upwards [hB₁ae, hA₂sub] with ω h1 h2
    rintro z ⟨hz | hz, -⟩
    · have hz' : z ∈ B₁ ω := by rw [h1]; exact Or.inl hz
      exact Or.inl (subset_fillVer (fun ω => (hB₁c ω).1) ω hz')
    · exact Or.inr (h2 hz)
  have hUc : ∀ ω, fillVer B₁ ω ∪ A₂ ω ⊆ H ∧ IsOpen (H \ (fillVer B₁ ω ∪ A₂ ω)) := by
    intro ω
    refine ⟨union_subset (hA₁c ω).1 (hA₂c ω).1, ?_⟩
    have e : H \ (fillVer B₁ ω ∪ A₂ ω) = (H \ fillVer B₁ ω) ∩ (H \ A₂ ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, mem_union]
      tauto
    rw [e]
    exact (hA₁c ω).2.inter (hA₂c ω).2
  have hUl : IsLocalSet (fun ω => fillVer B₁ ω ∪ A₂ ω) (centredField h u₀) P :=
    ((isLocalSet_tfae hh0 (hUm.mono h𝓜 le_rfl) (Eventually.of_forall hUc)).out 4 1).2 hUloc.isAvoidanceLocal
  -- unbounded lower-union components
  have hU := Mg.ae_not_isBounded_lowerUnion_stageSet h13 hκ hb hup (hreg' _)
  have hC := Mg.ae_not_isBounded_lowerUnion_stageSet h13 hκ hb hcap (hreg' _)
  have hunb₁ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (fillVer B₁ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (fillVer B₁ ω)) z) := by
    filter_upwards [hU, hC, hB₁ae] with ω h1 h2 hBω
    refine not_isBounded_lowerUnion_fillVer (fun ω => (hB₁c ω).1) ω ?_
    rw [hBω]
    exact Sec5.Aux61Restart.not_isBounded_lowerUnion_union (h1 k) (h2 ℓ)
  have hunb₂ : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z) := by
    filter_upwards [hC, hA₂fill] with ω h2 hfω
    rw [hfω]
    exact not_isBounded_lowerUnion_fillVer (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ω (h2 (ℓ + 1))
  have hpull := ae_isStagePullback_fill (A₁ := fillVer B₁) (A₂ := A₂) h13 hκ hb hE hER hlθ k ℓ hℓ τ
    (hB₁ae.mono fun ω h1 => by unfold fillVer; rw [h1]) (hA₂cl.mono fun ω hω hcap => (hω hcap).2)
  refine ⟨fillVer B₁, A₂, hA₁m.mono h𝓜₁ le_rfl, hA₂m.mono (hcap.2.1 (ℓ + 1)) le_rfl,
    hA₁m.comap_le.trans hd1, hA₁l, hA₂l, hUl, hUm, hUloc, hA₁c, hA₂c, ?_, hunb₁, hunb₂, hA₂cl, hpull, hA₂mean⟩
  filter_upwards [hB₁ae, hA₂fill] with ω h1 h2
  refine ⟨?_, h2⟩
  unfold fillVer
  rw [h1]

open Mi in
/-- **SB2(2)'s line family with one explored set**: the filtration `𝓖 t = ` (upper past at `k`) `⊔` (capped walk past
at `t`) and, at every real cap `t`, the sets `A₁ t`, `A₂ t` of `exists_sb2LowerSets_fill`: the line set
`A₁ t ∪ A₂ t` is measurable, relatively closed, local and marked local for `𝓖 t` (K2's `hBm`, `hBc`, `hloc`), the
route's set-level inputs hold, and almost surely on the capped launch event `A₂ t` satisfies `corr₂`, `dom₂` and
`hind₂`. -/
theorem exists_sb2LineFamily_fill (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
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
      ∀ t : ℝ≥0,
        Measurable[mΩ, hittingSigma] (A₁ t) ∧ Measurable[mΩ, hittingSigma] (A₂ t) ∧
        Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω) ∧
        MeasurableSpace.comap (A₁ t) hittingSigma ≤
          aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P ∧
        (∀ ω, A₁ t ω ⊆ H ∧ IsOpen (H \ A₁ t ω)) ∧ (∀ ω, A₂ t ω ⊆ H ∧ IsOpen (H \ A₂ t ω)) ∧
        (∀ ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω))) ∧
        IsLocalSet (A₁ t) (centredField h u₀) P ∧ IsLocalSet (A₂ t) (centredField h u₀) P ∧
        IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (centredField h u₀) P ∧
        IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω) (centredField h u₀) P ∧
        (∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ t ω),
          ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ t ω)) z)) ∧
        (∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ t ω),
          ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ t ω)) z)) ∧
        (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
          (∀ v ∈ H, (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 v ∈ A₂ t ω ↔
            v ∈ fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
              (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)) ∧
          H \ ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).dom : Set ℂ) ⊆ A₂ t ω) ∧
        (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
          (ExplState.run κ b jumps (Lu.upperSpec u l)
            (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none →
          ∃ g : ℂ → ℂ, ContinuousOn g Hbar ∧ EqOn g (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 H ∧
            ((∀ z, (g ⁻¹' {z} ∩ Hbar).Finite) →
              Ln.IsStagePullback (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω) g (A₁ t ω) (A₂ t ω)
                {w | (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 w ∈ A₁ t ω}
                (fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
                  (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)))) ∧
        ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₂ t) (centredField h u₀) P g →
          ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
            ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
            ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ t ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ t ω → g ω φ = ∫ z, v z * φ z) →
              EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (β ω, -(Real.pi / 2), recOf (t : ℝ≥0∞)
                (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))).mean
                  (fwdMap (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
                    (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)
                    ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).1 z)) -
                chiC κ * ((logDerivFwd (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
                    (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)
                    ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).1 z)).im +
                  (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.2 z)) (H \ A₂ t ω) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hle : ∀ t : ℝ≥0, pastSigma κ b jumps
      (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤ mΩ :=
    fun t => (isStagedHistory_capSpec (τ := (t : ℝ≥0∞)) hb (hE' _ hw) (hreg' _) hℓ hwℓ).2.1 (ℓ + 1)
  have hset := fun t : ℝ≥0 =>
    exists_sb2LowerSets_fill (u := u) h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ t hu₀
  choose A₁ A₂ hA₁m hA₂m hA₁σ hA₁l hA₂l hUl hUm hUloc hA₁c hA₂c _hfill hunb₁ hunb₂ hcl hpull hmean using hset
  refine ⟨Mj.capFiltration _ (StagedReg.regFam E _) (hreg' _) hℓ.le hwℓ hle (hup.2.1 k), A₁, A₂, fun t => rfl,
    fun t => ⟨hA₁m t, hA₂m t, (hUm t).mono (sup_le (hup.2.1 k) (hle t)) le_rfl, hA₁σ t, hA₁c t, hA₂c t,
      fun ω => ⟨union_subset (hA₁c t ω).1 (hA₂c t ω).1, ?_⟩, hA₁l t, hA₂l t, hUl t, hUloc t, hunb₁ t, hunb₂ t,
      ?_, hpull t, hmean t⟩⟩
  · have e : H \ (A₁ t ω ∪ A₂ t ω) = (H \ A₁ t ω) ∩ (H \ A₂ t ω) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, not_or]
      tauto
    rw [e]
    exact (hA₁c t ω).2.inter (hA₂c t ω).2
  · filter_upwards [hcl t] with ω hω hcap
    exact (hω hcap).2

end InteractingSLE.Theorem14.SB.Mk
