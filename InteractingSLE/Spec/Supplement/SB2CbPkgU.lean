/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CbLaw

/-!
# hcan and hTL from (P1) with the law's cover at upper launches (D82 item 3)

Packet PROVE-SB2-CANON, round 8. Every piece of (P1), from the base law on, covers only the samples where the upper
walk launches at `k` (F3LAW's handoff R6.2), so (P1)'s target is `Cz.SB2LowerStageLawInUStatement` (`SB2CbLaw`). This
file carries round 1's and rounds 5–6's chain from (P1) to hcan with the law's cover restricted the same way:

* **`SB2LowerStagePkgUStatement`**: round 1's per-stage package `Cz.SB2LowerStagePkgStatement` with the cover at upper
  launches;
* **`tailCanonAt_of_mvLawU`**: round 1's `tailCanonAt_of_mvLaw` with the hull's event `G₁` intersected with the upper
  launch event of the regularized upper family (an event of the retained past, `Lv.measurableSet_launch_pastSigma`,
  almost surely equal to `Lu.upperLaunchSet`); every other step as in round 1;
* **`sb2LowerStageCanonStatement_of_pkgU`**: hcan from the package;
* **`pkgTail_of_k2U`**: round 5's (P2)–(P4) at the tails; the cover is used only on `F ⊆ stageEvent`, inside the upper
  launch;
* **`sb2LowerStagePkgUStatement_of_lawU`**: round 6's package proof from (P1) in the new form (the line family is
  CONDFIN's `Cx.exists_rootLineFamily`, whose `A₁ 0` is hitting-measurable with relatively closed complement);
* **`sb2LowerStageCanonStatement_of_lawU`**, **`sb2LowerTailLiftExStatement_of_lawU`**: hcan and the top's hTL from
  (P1) in the new form (with CONDFIN's K2 at the tails, `sb2LowerTailK2Statement`, and GEOM2's root identification).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw Restart.DomainMarkov Restart.DomainMarkov.K2 Supp8.Q3Stop
  Sec7.PocketTraversal LocalSets Lv Ms Mf WalkSide Lk Lu Mx Mz
open Supp8.GB6.RelDrv (IsStopDrvMatch)

/-- **The per-stage package with the law's cover at upper launches (D82 item 3).** `Cz.SB2LowerStagePkgStatement` with
the retained law asked to cover the launches of B's stage `ℓ` only at an upper launch. -/
def SB2LowerStagePkgUStatement (h12p : Theorem12ParamStatement.{u}) : Prop :=
  ∀ κ : ℝ, ∀ hκ : 0 < κ, κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (u : ℝ) (l : List (ℝ × ℝ≥0)) (k : ℕ), u ≤ 0 → l.Pairwise (fun p q => p.2 < q.2) →
      (∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅) →
      0 < k → ∀ ℓ : ℕ,
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)) →
    ∃ (𝓜 : MeasurableSpace Ω) (A K' : Ω → Set ℂ) (G' : Set Ω) (Y : Ω → DistOn upperHalfPlaneOpens)
      (β : Ω → BoundaryWord) (M : ℝ) (x₀ : Ω → ℝ) (T : Set Ω),
      Ms.stageMarks κ b jumps E u l k ℓ ≤ 𝓜 ∧ 𝓜 ≤ mΩ ∧
      ∃ hlaw : @Fl.MvLaw κ Ω 𝓜 mΩ _ P _ h A K' G' Y β M,
        Measurable[aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] β ∧
        (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G') ∧
        (∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → A ω = fillH (Nc.retX κ b jumps E u l k ℓ ω)) ∧
        Measurable[mΩ ⊓ aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] x₀ ∧
        MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] T ∧
        (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
          (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
            (ℓ + 1)).2.2.2.1 ℓ ≠ none →
          Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
            (lowerD b jumps E ω) + 2 ≤ ℓ →
          (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ T) ∧
        ∀ᵐ ω ∂P, ω ∈ T → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → (lowerD b jumps E ω ℓ).2 ≠ 0 →
          Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h
            (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) x₀ hlaw.2.1 hlaw.2.2.1 ω

/-- **`Mz.TailCanonAt ℓ` from the retained law covering the launches at upper launches** (D82 item 3). -/
theorem tailCanonAt_of_mvLawU (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    -- the retained law at `ℓ`
    (h𝒮𝓜 : Ms.stageMarks κ b jumps E u l k ℓ ≤ 𝓜) (h𝓜 : 𝓜 ≤ mΩ)
    {A K' : Ω → Set ℂ} {G' : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → BoundaryWord} {M : ℝ}
    (hlaw : Fl.MvLaw κ 𝓜 P h A K' G' Y β M) (hβ : Measurable[aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] β)
    (hcovL : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G')
    (hA : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → A ω = fillH (Nc.retX κ b jumps E u l k ℓ ω))
    -- the offset
    {x₀ : Ω → ℝ} (hx₀ : Measurable[mΩ ⊓ aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] x₀)
    -- the tail event
    {T : Set Ω} (hT : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] T)
    (hTcov : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (lowerD b jumps E ω)
        (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (lowerD b jumps E ω) + 2 ≤ ℓ →
      (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ T)
    -- the chain facts (identification of B's piece with the canonical code)
    (hfacts : ∀ᵐ ω ∂P, ω ∈ T → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → (lowerD b jumps E ω ℓ).2 ≠ 0 →
      Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) x₀
        hlaw.2.1 hlaw.2.2.1 ω) :
    TailCanonAt h12p hκ b jumps P h E u l k ℓ := by
  classical
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hER
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have h𝒮 : Ms.stageMarks κ b jumps E u l k ℓ ≤ mΩ := h𝒮𝓜.trans h𝓜
  have h𝒮₁ : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ :=
    sup_le ((hE' _ hsu).2.1 k) ((hE' w hw).2.1 (ℓ + 1))
  have hmono : Ms.stageMarks κ b jumps E u l k ℓ ≤ Ms.stageMarks κ b jumps E u l k (ℓ + 1) :=
    stageMarks_mono (Nat.le_succ ℓ)
  -- the upper launch event of the regularized family
  obtain ⟨U, hUm, hUiff⟩ : ∃ U : Set Ω, MeasurableSet[Ms.stageMarks κ b jumps E u l k ℓ] U ∧
      ∀ᵐ ω ∂P, (ω ∈ U ↔ ω ∈ upperLaunchSet κ b jumps E u l k) := by
    refine ⟨{ω | (ExplState.run κ b jumps (upperSpec u l) (fun j => StagedReg.regFam E (upperSpec u l) j ω)
      (k + 1)).2.2.2.1 k ≠ none}, le_sup_left (b := pastSigma κ b jumps w (StagedReg.regFam E w) ℓ) _
        (Lv.measurableSet_launch_pastSigma hb (hE' _ hsu).1 (hreg' _) k), ?_⟩
    filter_upwards [hrun _ hsu] with ω hr
    change _ ≠ none ↔ _ ≠ none
    rw [hr (k + 1)]
  -- the exact hull
  obtain ⟨K, G₁, hKm, hKc, hKp, hG₁, hG₁cov, hG₁f⟩ :=
    exists_exactRetHull h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hu₀
  -- the exact offset
  have hx₀Ω : Measurable x₀ := hx₀.mono inf_le_left le_rfl
  have hx₀k : ∀ᵐ ω₀ ∂P, ω₀ ∈ (univ : Set Ω) →
      ∀ᵐ ω ∂(condExpKernel P (Ms.stageMarks κ b jumps E u l k ℓ) ω₀), x₀ ω = x₀ ω₀ := by
    filter_upwards [ae_ae_eq_of_measurable_aeSigma h𝒮 hx₀] with ω₀ h1 _ using h1
  obtain ⟨x₁, hx₁m, hx₁e⟩ := Qx.exists_measurable_ae_eq_of_kernel_const (P := P) h𝒮 hx₀Ω hx₀k
  -- the law given the retained past
  have hG₁G' : ∀ᵐ ω ∂P, ω ∈ G₁ ∩ U → ω ∈ G' := by
    filter_upwards [hG₁f, hcovL, hUiff] with ω h1 h2 h3 hω using h2 (h3.1 hω.2) (h1 hω.1).1
  have hKA : ∀ᵐ ω ∂P, ω ∈ G₁ ∩ U → fillH (K ω) = A ω := by
    filter_upwards [hG₁f, hA] with ω h1 h2 hω using (h1 hω.1).2.trans (h2 (h1 hω.1).1).symm
  obtain ⟨c, hcm, hce, hlawc⟩ :=
    exists_stageLaw_of_mvLaw h𝒮𝓜 h𝓜 hh.1 hlaw hβ hKc hKp hKm hx₁m (hG₁.inter hUm) hG₁G' hKA
  -- the zero-lifetime event of B's piece `ℓ`
  set Z : Set Ω := {ω | ((ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) (ℓ + 1)).2.2.1 ℓ).2.1 ≠ 0}
    with hZdef
  have hZ : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] Z := by
    refine le_sup_right (a := pastSigma κ b jumps (upperSpec u l) (StagedReg.regFam E (upperSpec u l)) k) _ ?_
    have hm : Measurable[pastSigma κ b jumps w (StagedReg.regFam E w) (ℓ + 1)]
        (pastMap κ b jumps w (StagedReg.regFam E w) (ℓ + 1)) := Measurable.of_comap_le le_rfl
    have hc : Measurable[pastSigma κ b jumps w (StagedReg.regFam E w) (ℓ + 1)] fun ω =>
        (pastMap κ b jumps w (StagedReg.regFam E w) (ℓ + 1) ω ⟨ℓ, Nat.lt_succ_self ℓ⟩).2.1 :=
      measurable_fst.comp (measurable_snd.comp ((measurable_pi_apply _).comp hm))
    exact (measurableSet_eq_fun hc measurable_const).compl
  -- the event `G`
  set G : Set Ω := G₁ ∩ U ∩ Z ∩ T with hGdef
  have hG : MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] G :=
    ((hmono _ (hG₁.inter hUm)).inter hZ).inter hT
  -- on a launch, `Z` is the positivity of the raw lifetime
  have hZiff : ∀ᵐ ω ∂P, (ExplState.run κ b jumps w (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
      (ω ∈ Z ↔ (lowerD b jumps E ω ℓ).2 ≠ 0) := by
    filter_upwards [hrun w hw] with ω hr hl
    have hlr : (ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
      rw [hr (ℓ + 1)]; exact hl
    have e : ((ExplState.run κ b jumps w (fun j => StagedReg.regFam E w j ω) (ℓ + 1)).2.2.1 ℓ).2.1 =
        (lowerD b jumps E ω ℓ).2 := by
      rw [hr (ℓ + 1)]
      exact Fl.retained_lifetime_of_launch hl
    simp only [hZdef, mem_ofPred_eq, e]
  have hRw := hER w hw
  have hRu := hER _ hsu
  refine tailCanonAt_of_chainFacts h12p hκ b jumps P h E u l k ℓ hRw hRu h𝒮₁ hh.1 hKc hKp hcm hKm hx₁m hG ?_ ?_
    ?_ ?_
  · filter_upwards [hlawc] with ω₁ h1 hω₁ using h1 hω₁.1.1
  · filter_upwards [hG₁cov, hZiff, hTcov, hUiff] with ω h1 h2 h3 h4 hup hl htail hz
    exact ⟨⟨⟨h1 hl, h4.2 hup⟩, (h2 hl).2 hz⟩, h3 hup hl htail hz⟩
  · filter_upwards [hG₁f] with ω h1 hω using (h1 hω.1.1.1).2
  · filter_upwards [hG₁f, hfacts, hZiff, hce, hx₁e, hlaw.2.2.2.2.1, hG₁G', hA] with ω h1 h2 h3 h4 h5 h6 h7 h8 hω
    obtain ⟨hl, hfK⟩ := h1 hω.1.1.1
    have hz : (lowerD b jumps E ω ℓ).2 ≠ 0 := (h3 hl).1 hω.1.2
    have hfK' : fillH (K' ω) = fillH (K ω) := by
      rw [h6 (h7 hω.1.1), h8 hl]; exact hfK.symm
    have hx : x₁ ω = x₀ ω := (h5 (mem_univ ω)).symm
    refine chainFacts_congr h12p hκ E u l k ℓ hfK'.symm ?_ hx (h2 hω.2 hl hz)
    rw [h4 hω.1.1, hx]

/-- **hcan from the per-stage package with the law's cover at upper launches** (Theorems 1.2–1.3). -/
theorem sb2LowerStageCanonStatement_of_pkgU (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (hpkg : SB2LowerStagePkgUStatement.{u} h12p) :
    SB2LowerStageCanonStatement.{u} h12p := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ
  by_cases hflow : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))
  · have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length := (List.getElem?_eq_some_iff.1 hflow).1
    obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
    obtain ⟨𝓜, A, K', G', Y, β, M, x₀, T, h𝒮𝓜, h𝓜, hlaw, hβ, hcovL, hA, hx₀, hT, hTcov, hfacts⟩ :=
      hpkg κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hflow
    exact tailCanonAt_of_mvLawU (mΩ := mΩ) (𝓜 := 𝓜) h12p h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ hu₀
      h𝒮𝓜 h𝓜 hlaw hβ hcovL hA
      hx₀ hT hTcov hfacts
  · exact tailCanonAt_of_not_flow h12p hκ b jumps P h E u l k ℓ hflow

/-- **(P4) at a tail stage, with (P2) and (P3), for the law's cover at upper launches** (D82 item 3). -/
theorem pkgTail_of_k2U (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    -- the retained law at `ℓ`
    {A K' : Ω → Set ℂ} {G' : Set Ω} {Y : Ω → DistOn upperHalfPlaneOpens} {β : Ω → BoundaryWord} {M : ℝ}
    (hlaw : @Fl.MvLaw κ Ω 𝓜 mΩ _ P _ h A K' G' Y β M)
    (hcovL : ∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → ω ∈ G')
    (hAL : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠
      none →
      A ω = fillH (Nc.retX κ b jumps E u l k ℓ ω))
    -- the line family
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω)
    -- Statement6's objects for the word `β`
    {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {relLife : Ω → ℝ≥0∞} {F : Set Ω}
    (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω) (hx₀ : Measurable[lineFiltC P 𝓖 0] x₀)
    (hF : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hent : ∀ᵐ ω ∂P, ω ∈ F → IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω)
      (realMax (Nc.retX κ b jumps E u l k ℓ ω))
      ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω)))
    (hFae : ∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ
          ∧ 0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
    {types : Set WordType} (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β ω)) ∈ types)
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) types pc tL
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2
      → ∃ m, (S.ver m).a t ω < S.V m ω)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P,
      ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) F w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W
        (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) w)
        (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β ω)) w) ω)
    -- K2's inputs and outputs at `ℓ`
    (hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β ω))
    (hlawK : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β ω₀)).jumps)
    (hK2 : ∀ᵐ ω ∂P, ω ∈ F →
      (∀ m, IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β ω),
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
        (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
      (driverCode h12p hκ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β ω),
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω) :
    ∃ (x₀' : Ω → ℝ) (T : Set Ω),
      Measurable[mΩ ⊓ aeSigma (Ms.stageMarks κ b jumps E u l k ℓ) P] x₀' ∧
      MeasurableSet[Ms.stageMarks κ b jumps E u l k (ℓ + 1)] T ∧
      (∀ᵐ ω ∂P, ω ∈ upperLaunchSet κ b jumps E u l k →
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
          (lowerD b jumps E ω) + 2 ≤ ℓ →
        (lowerD b jumps E ω ℓ).2 ≠ 0 → ω ∈ T) ∧
      ∀ᵐ ω ∂P, ω ∈ T → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠
        none →
        (lowerD b jumps E ω ℓ).2 ≠ 0 →
        Qx.ChainFacts h12p hκ (b := b) (jumps := jumps) E u l k ℓ h
          (fun ω => BoundaryWord.shiftW (x₀' ω) (β ω)) x₀' hlaw.2.1 hlaw.2.2.1 ω := by
  classical
  obtain ⟨hE', hreg', hrun'⟩ := StagedReg.regFam_spec hb hE hER
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  -- the σ-algebras
  have h𝒮₁ : Ms.stageMarks κ b jumps E u l k (ℓ + 1) ≤ mΩ :=
    sup_le ((hE' _ hsu).2.1 k) ((hE' _ hw).2.1 (ℓ + 1))
  have h𝒮 : Ms.stageMarks κ b jumps E u l k ℓ ≤ mΩ := (Mz.stageMarks_mono (Nat.le_succ ℓ)).trans h𝒮₁
  have hG0 : pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤ mΩ
          := by rw [← h𝓖 0]; exact 𝓖.le 0
  have hx₀' : Measurable[mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) P] x₀ := by
    rw [← h𝓖 0]; exact hx₀
  have hF' : MeasurableSet[mΩ ⊓ aeSigma (pastSigma κ b jumps (Lu.upperSpec u l)
      (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        ((0 : ℝ≥0) : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) P] F := by
    rw [← h𝓖 0]; exact hF
  -- (P2) the offset and (P3) the tail event
  obtain ⟨x₁, hx₁m, hx₁e⟩ := exists_offset_stageMarks E u l k ℓ hℓ hwℓ hG0 hx₀'
  obtain ⟨T, hTm, hFT⟩ := exists_eq_of_measurableSet_inf_aeSigma
    (capPast_le_stageMarks_succ E u l k ℓ hℓ hwℓ) hF'
  refine ⟨x₁, T, hx₁m.mono (le_inf h𝒮 (le_aeSigma _ P)) le_rfl, hTm, ?_, ?_⟩
  · filter_upwards [hFae, hFT.mem_iff] with ω h1 h2 hup hl hoff hpos
    exact h2.1 (h1.2 ⟨⟨hup, hl⟩, lt_of_lt_of_le (Nat.lt_add_of_pos_right two_pos) hoff, pos_iff_ne_zero.2 hpos⟩)
  -- (P4) the chain facts
  have hFae' : ∀ᵐ ω ∂P, ω ∈ F → (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ
          ∧ 0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) := by
    filter_upwards [hFae] with ω h1 using h1.1
  have hle0 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  obtain ⟨-, hlc, -, hdom, hfwd, hliftm⟩ := Mt.hullChart_k2Inputs hKm hKc hKp hx₀
  have hZm : Measurable fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω) :=
    Chart.measurable_chartTransport_random' (c := fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => Mu.isConformal_canon x₀ hKc hKp ω) (fun z => hle0 _ (hdom z))
      (fun z => (hfwd z).mono hle0 le_rfl) (fun z => (hliftm z).mono hle0 le_rfl) hlc hh.1 1 0 (chiC κ)
  have hcont := ae_continuousOn_driverOf h12p h13 hκ hκ4 (-(Real.pi / 2)) hle0 hc hZm hF hlawK
  have hfacts := ae_chainFacts_tail h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hA hKc hKp
    hKF hent hFae' htypes hcover S hcl hle hK2 hcont
  have hgood := ae_stageGoodAt_retX h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hFae' hent
  filter_upwards [hFT.mem_iff, hfacts, hgood, hKF, hA 0, hx₁e, hcovL, hAL, hlaw.2.2.2.2.1, hrun' _ hw, hFae']
    with ω hFTω hf hg hKω hA0 hx₁ω hcov hAω hK'A hrw hFω hT hl hpos
  have hωF : ω ∈ F := hFTω.2 hT
  have hfillK : fillH (K ω) = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
    rw [hKω hωF, hA0.1]; exact fillVer_first_eq (hg hωF) _
  have hfill : fillH (K' ω) = fillH (K ω) := by rw [hK'A (hcov (hFω hωF).1.1 hl), hAω hl, hfillK]
  -- the offsets agree
  have hlr : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
      none := by
    rw [hrw (ℓ + 1)]; exact hl
  have hlife : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2
    = (lowerD b jumps E ω ℓ).2 := by
    have e1 := Fl.retained_lifetime_of_launch hlr
    have e2 := Fl.retained_lifetime_of_launch hl
    rw [hrw (ℓ + 1)] at e1
    exact e1.symm.trans e2
  have hx : x₀ ω = x₁ ω := hx₁ω hlr (by rw [hlife]; exact hpos) (hreg' _ ℓ ω).2.1
  exact chainFacts_congr h12p hκ E u l k ℓ hfill (by rw [hx]) hx.symm (hf hωF)

/-- **The per-stage package (covers at upper launches) from (P1) in the measurable-family form and K2 at the tails**
(Theorems 1.2–1.3). -/
theorem sb2LowerStagePkgUStatement_of_lawU (h12p : Theorem12ParamStatement.{u}) (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0})
    (hP1 : SB2LowerStageLawInUStatement.{u}) (hK2 : SB2LowerTailK2Statement.{u} h12p) :
    SB2LowerStagePkgUStatement.{u} h12p := by
  intro κ hκ hκ4 b jumps hb Ω mΩ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hflow
  have hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length :=
    (List.getElem?_eq_some_iff.1 hflow).1
  obtain ⟨u₀, hu₀, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
  -- the joint line family and F3LAW's law for it
  obtain ⟨𝓖, A₁, A₂B, A₂, h𝓖, hfam⟩ :=
    Cx.exists_rootLineFamily (P := P) (u := u) (l := l) h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hflow hu₀
  have hA := stmt6Sets_of_rootSets hfam
  obtain ⟨hA₁m, -, -, -, -, -, -, -, hA₁c, -⟩ := hfam 0
  obtain ⟨K', G', Y, β, M, types, hlaw, hβ, hcovL, htypes, hcovAll, hmeanP, hheightP⟩ :=
    hP1 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft hk ℓ hflow 𝓖 A₁ A₂ h𝓖 hA hA₁m
      hA₁c
  have hlaw' := hlaw
  obtain ⟨-, -, -, -, -, -, -, hβ𝓜, hsort, hM0, hMb, -⟩ := hlaw'
  -- SB2LIFT's Statement6 for the law's word
  have h6 := sb2LowerStageVersionStatement6_of_6E (Sx.sb2LowerStageVersionStatement6E h12 h13 h12₀ h13₀)
  obtain ⟨K, x₀, pc, tL, relLife, F, hKm, hKc, hKp, hKF, hx₀, hF, hpc, htL, hent, hFae, hS⟩ :=
    h6 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft ℓ 𝓖 A₁ A₂ h𝓖 hA β types hβ
      hsort htypes u₀ hu₀ (hmeanP u₀ hu₀) hheightP
  have hcover : ∀ᵐ ω ∂P, ω ∈ F →
      angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β ω)) ∈ types := by
    filter_upwards [hFae, hcovAll] with ω h1 h2 hω using h2 (h1.1 hω).1.1 (h1.1 hω).1.2 (x₀ ω)
  obtain ⟨S, hcl, hleAll, hlife⟩ := hS hcover
  -- the word's conditional law at the offset, and K2
  have hle0 : lineFiltC P 𝓖 0 ≤ mΩ := (lineFiltC P 𝓖).le 0
  have hFG : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ G' := by
    filter_upwards [hFae, hcovL] with ω h1 h2 hω using h2 (h1.1 hω).1.1 (h1.1 hω).1.2
  have hlawK := Fo.ae_lawx_of_mvLaw hh.1 hle0 hlaw hKm hKc hKp hx₀ hF hFG hKF
  have hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β ω) :=
    BoundaryWord.measurable_shiftW.comp (hx₀.prodMk hβ𝓜)
  have hk2 := hK2 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft ℓ hℓ u₀ hu₀ 𝓖 A₁
    A₂B A₂ h𝓖 hfam F K x₀ β types pc tL relLife S hKm hKc hKp hKF hx₀ hF hpc htL hent hFae hc hsort hlawK
    (hmeanP u₀ hu₀) htypes hcover M hM0 hMb (hleAll 0) hlife
  -- the retained set on launches
  have hAL : ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (lowerD b jumps E ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none → A₁ 0 ω = fillH (Nc.retX κ b jumps E u l k ℓ ω) := by
    filter_upwards [hA 0, Nc.ae_retGeom h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hℓ] with ω h1 h2 hl
    rw [h1.1]; exact (h2 hl).2.2.2.2
  -- (P2)–(P4)
  obtain ⟨x₀', T, hx₀', hT, hTcov, hfacts⟩ := pkgTail_of_k2U h12p h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu
    hlθ k ℓ hleft hℓ hflow hlaw hcovL hAL h𝓖 hA hKm hKc hKp hKF hx₀ hF hent hFae htypes hcover S hcl (hleAll 0) hc
    hlawK hk2
  -- the marks
  obtain ⟨hE', -, -⟩ := StagedReg.regFam_spec hb hE hER
  have hw : IsBoundaryContinuedProgram (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2 :=
    isBoundaryContinuedProgram_boundaryWalkSpec b jumps ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hsu : IsBoundaryContinuedProgram (Lu.upperSpec u l).2.2 := Lu.isBoundaryContinuedProgram_upperSpec hlθ
  have h𝒮 : Ms.stageMarks κ b jumps E u l k ℓ ≤ mΩ :=
    (Mz.stageMarks_mono (Nat.le_succ ℓ)).trans (sup_le ((hE' _ hsu).2.1 k) ((hE' _ hw).2.1 (ℓ + 1)))
  have h𝒮𝓖 : Ms.stageMarks κ b jumps E u l k ℓ ≤ 𝓖 0 := by
    rw [h𝓖 0]
    refine sup_le_sup le_rfl ?_
    rw [← WalkSide.pastSigma_capSpec_of_le (θ := -(Real.pi / 2)) (τ := ((0 : ℝ≥0) : ℝ≥0∞)) hℓ.le
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) le_rfl]
    exact pastSigma_mono _ _ (Nat.le_succ ℓ)
  have hsm : Ms.stageMarks κ b jumps E u l k ℓ ≤ lineFiltC P 𝓖 0 :=
    le_inf h𝒮 (h𝒮𝓖.trans (le_aeSigma _ P))
  exact ⟨lineFiltC P 𝓖 0, A₁ 0, K', G', Y, β, M, x₀', T, hsm, hle0, hlaw, hβ, hcovL, hAL, hx₀', hT, hTcov,
    hfacts⟩

/-- **hcan from (P1) with the law's cover at upper launches** (Theorems 1.2–1.3; K2 at the tails by
`sb2LowerTailK2Statement`). -/
theorem sb2LowerStageCanonStatement_of_lawU (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hP1 : SB2LowerStageLawInUStatement.{u}) :
    Mz.SB2LowerStageCanonStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) :=
  sb2LowerStageCanonStatement_of_pkgU _ h13 h13₀
    (sb2LowerStagePkgUStatement_of_lawU _ h12 h13 h12₀ h13₀ hP1 (sb2LowerTailK2Statement h12 h13 h12₀ h13₀))

/-- **The top's hTL from (P1) with the law's cover at upper launches and GEOM2's root identification**
(Theorems 1.2–1.3). -/
theorem sb2LowerTailLiftExStatement_of_lawU (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hP1 : SB2LowerStageLawInUStatement.{u})
    (hI : Ct.SB2LowerRootIdentStatement.{u} (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)) :
    Lk.SB2LowerTailLiftExStatement.{u} :=
  Cg.sb2LowerTailLiftExStatement_of_rest h12 h13 h12₀ h13₀
    (Lk.sb2LowerGeomRestV6 h12 h13 h12₀ h13₀ (Lk.sb2LowerStartDataStatement_of_thms h12 h13 h12₀ h13₀))
    (sb2LowerStageCanonStatement_of_lawU h12 h13 h12₀ h13₀ hP1)
    (Cy.sb2LowerRelPosWRootStatement_of_ident h12 h13 h12₀ h13₀ hI)

end InteractingSLE.Theorem14.SB.Cz
