/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MjCorr
import InteractingSLE.Spec.Supplement.SB2MgSets
import InteractingSLE.Spec.Supplement.SBLwChart
import InteractingSLE.Spec.Supplement.SB2HEntry
import InteractingSLE.Spec.Supplement.WalkLeafChart
import InteractingSLE.Spec.Sec7.SideHeightRange
import InteractingSLE.Spec.Exist.StagedLaw2Launch

/-!
# SB2(2)'s filled explored set: the fill/domain identity and the explored mean

Packet PROVE-SB2-LCMEAN, round 8. Two explored sets were in use for SB2(2)'s lower piece `ℓ` capped at `τ`: round 4's
filled line version `fillVer B` of the capped walk prefix `B_{≤ℓ,τ}` (K2's line sets, the union mean of rounds 3–4)
and round 6's `ℍ ∖ c'.dom` (with the explored mean `hind₂` and, round 7, the clauses `corr₂`, `dom₂`). They agree on
the capped launch event, by the **fill/domain identity** `c'.dom = ℍ ∖ fill(B_{≤ℓ,τ})`. It follows from the landed
`Lw.isDomainChart_runChart` (a regular run chart that is not finished is a chart of `ℍ ∖ fill(prefixPhysSet)`):

* `prefixPhysSet_inter_H_eq`, `fillH_prefixPhysSet_eq`: the recorded prefix meets `ℍ` in the stage set, with the same
  fill; `dom_runChart_eq`: the domain of a regular run chart that is not finished is `ℍ ∖ fill(prefixPhysSet)`;
* `stStatus_capSpec_ne_done`: after a capped launch with `τ < ζ` the capped run is at a tip (not finished);
* **`dom_capChart_eq`**: on a capped launch, the post-cap chart's domain is `ℍ ∖ fill(B_{≤ℓ,τ})`, and the capped stage
  set is bounded;
* **`exists_capFill_hind`**: for the filled line version `A₂ = fillVer B` itself (measurable and marked local for the
  capped past, local, almost surely `fillVer B_{≤ℓ,τ}`): its complement is the post-cap chart domain on the capped
  launch event, it satisfies `corr₂` and `dom₂` for B's stage chart and the stopped piece, and **`hind₂`** in the form
  of `Ln.IsStagePullback`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mk

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField

/-! ### The recorded prefix, the stage set and the run chart's domain -/

section Det

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The recorded prefix meets `ℍ` in the stage set. -/
theorem prefixPhysSet_inter_H_eq {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω : Ω) :
    SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k ∩ H = WalkLaw.stageSet κ b jumps spec E k ω := by
  refine Subset.antisymm (fun z hz => WalkLeaf.mem_stageSet_of_mem_prefixPhysSet spec E k ω hz.1 hz.2) ?_
  rintro z ⟨hz, hzH⟩
  exact ⟨Or.inl (Or.inr hz), hzH⟩

/-- The recorded prefix and the stage set have the same fill. -/
theorem fillH_prefixPhysSet_eq {Ω : Type*} (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (ω : Ω) :
    fillH (SB.prefixPhysSet κ b jumps spec (fun j => E j ω) k) = fillH (WalkLaw.stageSet κ b jumps spec E k ω) := by
  rw [← Sec7.SideHeight.fillH_inter_H, prefixPhysSet_inter_H_eq]

/-- The domain of a regular run chart that is not finished is `ℍ ∖ fill(prefixPhysSet)`. -/
theorem dom_runChart_eq (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) :
    (((ExplState.run κ b jumps spec D n).2.2.2.2.1).dom : Set ℂ) =
      H \ fillH (SB.prefixPhysSet κ b jumps spec D n) := by
  have hD := Lw.isDomainChart_runChart (κ := κ) (b := b) (jumps := jumps) spec D hreg n hnot
  rw [hD.1.coe_dom]
  exact hD.2.1

variable {w : ExplSpec} {ℓ : ℕ} {θ : ℝ} {t : ℝ≥0∞}

/-- **After a capped launch with `τ` before the lifetime, the capped run is at a tip** (not finished). -/
theorem stStatus_capSpec_ne_done (hℓ : ℓ ≤ w.2.2.length) (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t)))
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hl : (ExplState.run κ b jumps w D (ℓ + 1)).2.2.2.1 ℓ ≠ none) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < (D ℓ).2) :
    stStatus (ExplState.run κ b jumps (capSpec w ℓ θ τ) D (ℓ + 1)) ≠ GW1Conn.stDone := by
  rw [← launches_run_capSpec_succ (τ := (τ : ℝ≥0∞)) hℓ hwℓ D] at hl
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (capSpec w ℓ θ τ) D hcθ
  have hne : min (τ : ℝ≥0∞) (D ℓ).2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  rw [he, instrTime_capSpec hℓ, (launch_eq_of_ne_top _ _ _ _ _ hne).2.2.2.2.1]
  simp only [lStatus, hτ, ↓reduceIte]
  decide

/-- **The fill/domain identity on a capped launch**: the post-cap chart is a chart of `ℍ ∖ fill(B_{≤ℓ,τ})`, and the
capped stage set is bounded. -/
theorem dom_capChart_eq {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) (hℓ : ℓ ≤ w.2.2.length)
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤)))
    (hreg : ∀ k c θ', (ExplState.run κ b jumps w (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (E k ω).1 (min (instrTime w k) (E k ω).2))
    (hl : (ExplState.run κ b jumps w (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) {τ : ℝ≥0}
    (hτ : (τ : ℝ≥0∞) < (E ℓ ω).2) :
    (((ExplState.run κ b jumps (capSpec w ℓ θ τ) (fun j => E j ω) (ℓ + 1)).2.2.2.2.1).dom : Set ℂ) =
        H \ fillH (WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1) ω) ∧
      Bornology.IsBounded (WalkLaw.stageSet κ b jumps (capSpec w ℓ θ τ) E (ℓ + 1) ω) := by
  have hreg' := pieceRegular_capSpec (fun j => E j ω) hℓ hwℓ hreg τ
  have hnot := stStatus_capSpec_ne_done (κ := κ) (b := b) (jumps := jumps) hℓ hwℓ (fun j => E j ω) hl hτ
  refine ⟨?_, ?_⟩
  · rw [dom_runChart_eq _ _ hreg' (ℓ + 1) hnot, fillH_prefixPhysSet_eq]
  · refine (Lx.isCompact_prefixPhysSet_run _ _ hreg' (ℓ + 1) hnot).isBounded.subset ?_
    rw [← prefixPhysSet_inter_H_eq]
    exact inter_subset_left

end Det

/-! ### SB2(2): the filled explored set and its mean -/

section SB2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

open Mi Mj in
/-- **SB2(2)'s filled explored set with its mean and the explored-side clauses of the stage pull-back**: the filled
line version `A₂` of the capped walk prefix `B_{≤ℓ,τ}` (measurable and marked local for the capped past, local, almost
surely `fillVer B_{≤ℓ,τ}`) has, almost surely on the capped launch event, the post-cap chart domain as complement,
satisfies `corr₂` and `dom₂` for B's stage chart and the stopped piece, and the explored-chain formula (`hind₂`). -/
theorem exists_capFill_hind (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u}) {θ : ℝ}
    (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) (right : Bool) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (ℓ : ℕ) (hℓ : ℓ < (boundaryWalkSpec b jumps θ right).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps θ right).2.2[ℓ]? = some (Sum.inl (θ, ⊤))) (τ : ℝ≥0)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ A₂ : Ω → Set ℂ,
      Measurable[pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1), hittingSigma] A₂ ∧
      (∀ ω, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧
      (∀ᵐ ω ∂P, A₂ ω = Mf.fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)) ω) ∧
      (∀ᵐ ω ∂P, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1) ω ⊆ A₂ ω) ∧
      IsLocalSet A₂ (centredField h u₀) P ∧
      IsHistoryAvoidanceLocal (pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
        (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) (ℓ + 1)) A₂ (centredField h u₀) P ∧
      (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
          (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
        H \ A₂ ω = ((ExplState.run κ b jumps (capSpec (boundaryWalkSpec b jumps θ right) ℓ θ τ)
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps θ right) j ω) (ℓ + 1)).2.2.2.2.1.dom : Set ℂ) ∧
        (∀ v ∈ H, (sb2StageChart κ E b jumps θ right ℓ ω).2.1 v ∈ A₂ ω ↔
          v ∈ fwdHull (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)) ∧
        H \ ((sb2StageChart κ E b jumps θ right ℓ ω).dom : Set ℂ) ⊆ A₂ ω) ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A₂ (centredField h u₀) P g →
        ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
          ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps θ right)
            (StagedReg.regFam E (boundaryWalkSpec b jumps θ right)) ℓ τ →
          ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ ω) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ ω → g ω φ = ∫ z, v z * φ z) →
            EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞)
              (StagedReg.regFam E (boundaryWalkSpec b jumps θ right) ℓ ω))).mean
                (fwdMap (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)
                  ((sb2StageChart κ E b jumps θ right ℓ ω).1 z)) -
              chiC κ * ((logDerivFwd (sb2StopDrv E b jumps θ right ℓ τ ω)
                  (sb2StopTime E b jumps θ right ℓ τ ω) ((sb2StageChart κ E b jumps θ right ℓ ω).1 z)).im +
                (sb2StageChart κ E b jumps θ right ℓ ω).2.2 z)) (H \ A₂ ω) := by
  classical
  set w := boundaryWalkSpec b jumps θ right with hwdef
  have hw : IsBoundaryContinuedProgram w.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ right
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hR' : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (StagedReg.regFam E spec) := fun spec hs =>
    stagedPiecesRegular_of_regular h13 hκ hb (hE' spec hs) (hreg' spec)
  set E' := StagedReg.regFam E w with hE'def
  have hEw : IsStagedHistory κ b jumps P h w E' := hE' w hw
  set w' := capSpec w ℓ θ (τ : ℝ≥0∞) with hw'
  have hS' : IsStagedHistory κ b jumps P h w' E' := isStagedHistory_capSpec hb hEw (hreg' w) hℓ hwℓ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨hav, ho, hloc⟩ := Lcd.stageSet_markedLocal_of_thm12_thm13 h12p h13 hκ hκ4 hb hh hS' (hreg' w) hu₀
    (ℓ + 1)
  obtain ⟨B, hBm, hBc, hBae, hBloc⟩ := Lcd.exists_lineVersion (P := P) ⟨_, hS'.2.1 (ℓ + 1)⟩
    (fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) ho hav hloc
  obtain ⟨hAm𝓜, hAc, hAloc, hAl⟩ := Mf.fillVer_package hh0 (hS'.2.1 (ℓ + 1)) hBc hBm hBloc
  have hAm : Measurable[mΩ, hittingSigma] (Mf.fillVer B) := hAm𝓜.mono (hS'.2.1 (ℓ + 1)) le_rfl
  obtain ⟨c', hc'c, hc'l, hc'h, hdom, hfwd, hCm, hliftm, hc'eq⟩ :=
    WalkInf.prefixChartVersionStatement_of_mem hθ right κ hκ hκ4 b jumps hb P h hh
      (fun spec => StagedReg.regFam E spec) hE' hR' hreg' ℓ τ
  have hPR := (hR' w hw).ae_pieceRegular
  -- the fill/domain identity on the capped launch event
  have hfd : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E' ℓ τ → H \ Mf.fillVer B ω = ((c' ω).dom : Set ℂ) := by
    filter_upwards [hc'eq, hPR, hBae] with ω hcω hPRω hBω hω
    obtain ⟨hd, hbd⟩ := dom_capChart_eq (κ := κ) (b := b) (jumps := jumps) E' ω hℓ.le hwℓ hPRω hω.1 hω.2
    rw [hcω hω, hd, Mf.fillVer_of_bounded (hBω ▸ hbd), Sec7.SideHeight.fillH_closure, hBω]
  -- the filled set contains the prefix
  have hsub : ∀ᵐ ω ∂P, WalkLaw.stageSet κ b jumps w' E' (ℓ + 1) ω ⊆ Mf.fillVer B ω := by
    filter_upwards [hBae] with ω hBω
    rw [← hBω]
    exact Mf.subset_fillVer (fun ω => (hBc ω).1) ω
  have hfill : ∀ᵐ ω ∂P, Mf.fillVer B ω = Mf.fillVer (WalkLaw.stageSet κ b jumps w' E' (ℓ + 1)) ω := by
    filter_upwards [hBae] with ω hBω
    unfold Mf.fillVer
    rw [hBω]
  have hAD : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E' ℓ τ →
      ((c' ω).dom : Set ℂ) ⊆ H \ Mf.fillVer B ω ∧ IsOpen ((H \ Mf.fillVer B ω) \ (c' ω).dom) := by
    filter_upwards [hfd] with ω hω hcap
    rw [hω hcap]
    exact ⟨subset_rfl, by simp⟩
  -- the explored-side clauses
  have hclauses : ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps w E' ℓ τ →
      H \ Mf.fillVer B ω = ((ExplState.run κ b jumps w' (fun j => E' j ω) (ℓ + 1)).2.2.2.2.1.dom : Set ℂ) ∧
      (∀ v ∈ H, (sb2StageChart κ E b jumps θ right ℓ ω).2.1 v ∈ Mf.fillVer B ω ↔
        v ∈ fwdHull (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)) ∧
      H \ ((sb2StageChart κ E b jumps θ right ℓ ω).dom : Set ℂ) ⊆ Mf.fillVer B ω := by
    filter_upwards [hc'eq, hPR, hfd] with ω hcω hPRω hfdω hω
    set c := sb2StageChart κ E b jumps θ right ℓ ω with hcdef
    have hcC : c.IsConformal :=
      (GW1RestartFinal.chart_boundaryRange_run w (fun j => StagedReg.regFam E w j ω) hPRω ℓ).1
    obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω.1
    have hch := chart_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) hℓ.le hwℓ
      (fun j => StagedReg.regFam E w j ω) hl τ
    obtain ⟨hWc₀, hW0₀⟩ := continuous_stopDrv (hreg' w ℓ ω) hω.2
    have hWc : Continuous (sb2StopDrv E b jumps θ right ℓ τ ω) := hWc₀
    have hW0 : sb2StopDrv E b jumps θ right ℓ τ ω 0 = 0 := hW0₀
    have hT : (0 : ℝ) ≤ sb2StopTime E b jumps θ right ℓ τ ω := NNReal.coe_nonneg _
    have hc'l : c' ω =
        c.loewner (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω) := by
      rw [hcω hω, hch]
      rfl
    have hcl :
        (c.loewner (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)).IsConformal :=
      hc'l ▸ hc'c ω
    have hcomp := hfdω hω
    have hmemA : ∀ x ∈ H, x ∈ Mf.fillVer B ω ↔ x ∉ ((c' ω).dom : Set ℂ) := by
      intro x hx
      constructor
      · intro hxA hxD
        rw [← hcomp] at hxD
        exact hxD.2 hxA
      · intro hxD
        by_contra hxA
        exact hxD (hcomp ▸ ⟨hx, hxA⟩)
    refine ⟨hcomp.trans (by rw [hcω hω]), fun v hv => ?_, fun z hz => ?_⟩
    · rw [hmemA _ (hcC.2.1 hv), hc'l, mem_dom_loewner_iff hcC hWc hW0 hT hcl hv, not_not]
    · refine (hmemA z hz.1).2 fun hzD => hz.2 ?_
      rw [hc'l] at hzD
      exact dom_loewner_subset hcC hWc hW0 hT hcl hzD
  refine ⟨Mf.fillVer B, hAm𝓜, hAc, hfill, hsub, hAl, hAloc, hclauses, fun g hg => ?_⟩
  obtain ⟨β, -, hmean⟩ := ae_capMean hκ hb hh hEw (hreg' w) hℓ hwℓ τ hu₀ hAm hAl hAloc hc'c hc'l hdom hfwd hCm
    hliftm hc'eq hAD hg
  refine ⟨β, ?_⟩
  have hbumps := ae_all_iff.2 fun i : ℚ × ℚ × ℚ => hmean (ratBump i)
  filter_upwards [hbumps, hfd, hc'eq] with ω hbω hfdω hcω hω v hv hvg
  have hcomp := hfdω hω
  rw [hcomp] at hv hvg ⊢
  have hβs := isSorted_stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞) (E' ℓ ω))
  set β' := stopWord κ (β ω, θ, recOf (τ : ℝ≥0∞) (E' ℓ ω)) with hβ'
  have hcm := harmonicOnNhd_chartMean (hc'c ω) (hc'h ω) hβs hu₀.1 (chiC κ)
  have hdH : ((c' ω).dom : Set ℂ) ⊆ H := (hc'c ω).dom_subset
  have hu₀c : ContinuousOn u₀ (c' ω).dom := fun z hz => (hu₀.1 z (hdH hz)).1.continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z) (c' ω).dom := by
    have h1 : ContinuousOn (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z - u₀ z) (c' ω).dom :=
      fun z hz => (hcm z hz).1.continuousAt.continuousWithinAt
    refine (h1.add hu₀c).congr fun z _ => ?_
    simp only [Pi.add_apply]
    ring
  have heq : EqOn v (fun z => β'.mean ((c' ω).1 z) - chiC κ * (c' ω).2.2 z - u₀ z) (c' ω).dom := by
    refine eqOn_of_ratBump (c' ω).dom.isOpen hdH hv hcm fun i hi => ?_
    rw [← hvg _ hi, hbω i hω hi, ← integral_sub (WholeField.integrable_mul_testOn hfc _ hi)
      (WholeField.integrable_mul_testOn hu₀c _ hi)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hω.1
  have hch := chart_run_capSpec_succ (κ := κ) (b := b) (jumps := jumps) hℓ.le hwℓ
    (fun j => StagedReg.regFam E w j ω) hl τ
  have e₁ : ∀ z, (c' ω).1 z = fwdMap (sb2StopDrv E b jumps θ right ℓ τ ω) (sb2StopTime E b jumps θ right ℓ τ ω)
      ((sb2StageChart κ E b jumps θ right ℓ ω).1 z) := by
    intro z
    rw [hcω hω, hch]
    rfl
  have e₂ : ∀ z, (c' ω).2.2 z = (logDerivFwd (sb2StopDrv E b jumps θ right ℓ τ ω)
      (sb2StopTime E b jumps θ right ℓ τ ω) ((sb2StageChart κ E b jumps θ right ℓ ω).1 z)).im +
        (sb2StageChart κ E b jumps θ right ℓ ω).2.2 z := by
    intro z
    rw [hcω hω, hch]
    rfl
  intro z hz
  have e := heq hz
  simp only at e ⊢
  rw [e, e₁, e₂]
  ring

end SB2

end InteractingSLE.Theorem14.SB.Mk
