/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxAe
import InteractingSLE.Spec.Supplement.SB2QuHead
import InteractingSLE.Spec.Supplement.SB2MfFill
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier

/-!
# The stage-set facts of the terminal hull identity, almost surely

The input `hphys` of `Qx.ae_fill_eq_stepHull_of_versions`.

Worker REVIEW-FABLE-T14 (items 2–3 of PROVE-SB2-LCMEAN's handoff R13.8). For the line family of F2b′ at B's stage `ℓ`
(`A₁ t = fill(upper ∪ B before ℓ)`, `A₂ t = fill(B through ℓ capped at t)`, for the regularized drivers), almost surely
on B's launch at `ℓ`, when the fill of the retained union through the connector `ℓ + 1`,
`S₂ = upper ∪ stageSet(capSpec (ℓ + 2) 0)(ℓ + 2)`, is a hull:

* `fill(upper ∪ B before ℓ) ⊆ fill S₂`; every `A₂ q ⊆ ℍ` and `⊆ fill S₂` (`q` rational);
* `S₂ ∩ ℍ ⊆ fill(upper ∪ B before ℓ) ∪ ⋃_{q < ζ_ℓ} A₂ q`.

Ingredients: GW1's chain facts for the regularized walk (`Lk.ae_walkChainFacts_of_reg`, Theorems 1.2–1.3) give the
piece's `PieceSimpleAt`; `Qx.stageSet_capSpec_subset`, `Qx.stageSet_succ_succ_subset`.

* `ae_walkChainFacts_regFam`, `pieceSimpleAt_of_chainFacts`, **`ae_phys`**.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Qx

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide GW1Bookkeep Lk Mf Qw

/-- **GW1's chain facts for the regularized lower walk**, almost surely (Theorems 1.2–1.3). -/
theorem ae_walkChainFacts_regFam (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec)) :
    ∀ᵐ ω ∂P, WalkChainFacts κ b jumps (-(Real.pi / 2))
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hGB6 := Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀) (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  have hS := GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 h13 h13₀ hClock
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hT := GW1WalkFinish.walkTipCoordinatesStatement_of_d4 h13 hD4
  have hC := GW1WalkFinish.walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 h13₀) hD4
  exact ae_walkChainFacts_of_reg hS h13 hT hC κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' (StagedReg.regFam E) hE' hreg'

/-- A launched piece of a walk with GW1's chain facts is simple (`PieceSimpleAt`), in the chart of its stage. -/
theorem pieceSimpleAt_of_chainFacts {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hW : WalkChainFacts κ b jumps (-(Real.pi / 2)) D)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ∃ (old : Set ℂ) (q₀ q₁ : ℝ),
      PieceSimpleAt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D ℓ).2.2.2.2.1
        (D ℓ).1 (D ℓ).2 old q₀ q₁ := by
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨-, hqP⟩ := prefix_facts hW.1 hW.2 ℓ
  have hnd := WalkIntRunChron.not_done_of_launch _ D hcθ
  have hS := hW.1 ℓ c θ' hcθ (hqP hnd)
  obtain ⟨-, -, hc⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hcθ
  rw [GW1WalkExit.instrTime_walk_of_launch hl, min_eq_right le_top, hc] at hS
  exact ⟨_, _, _, hS⟩


theorem fillH_closure (A : Set ℂ) : fillH (closure A) = fillH A := by
  simp only [fillH, closure_closure]

theorem self_inter_H_subset_fillH (A : Set ℂ) : A ∩ H ⊆ fillH A := fun _ hz =>
  mem_fillH_of_mem_closure hz.2 (subset_closure hz.1)

/-- **The stage-set facts of the terminal hull identity, almost surely on B's launch at `ℓ`.** -/
theorem ae_phys {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)
    {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂ t ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1)) ω)
    (hWC : ∀ᵐ ω ∂P, WalkChainFacts κ b jumps (-(Real.pi / 2))
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω))
    (hrun : ∀ᵐ ω ∂P, ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
        ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)
    {F : Set Ω} {K : Ω → Set ℂ} (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω)
    (hFl : ∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ∀ᵐ ω ∂P, ω ∈ F →
      IsHPHull (fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω)) →
      fillH (K ω) ⊆ fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ∧
      (∀ q : ℚ, A₂ (Real.toNNReal q) ω ⊆ H) ∧
      (∀ q : ℚ, A₂ (Real.toNNReal q) ω ⊆ fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l)
        (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω)) ∧
      (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) ∩ H ⊆ fillH (K ω) ∪
        ⋃ (q : ℚ) (_ : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2),
          A₂ (Real.toNNReal q) ω := by
  set w := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hw
  set Er := StagedReg.regFam E w with hEr
  have hAq : ∀ᵐ ω ∂P, ∀ q : ℚ, A₁ (Real.toNNReal q) ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)) Er ℓ ω) ω ∧
      A₂ (Real.toNNReal q) ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2))
        ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)) Er (ℓ + 1)) ω := ae_all_iff.2 fun q => hA _
  filter_upwards [hAq, hA 0, hWC, hrun, hKF, hFl] with ω hAω hA0 hWω hrω hKω hFω hωF hZ
  set Su := WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω with hSu
  have hl : (ExplState.run κ b jumps w (fun j => Er j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    rw [hrω]; exact hFω hωF
  obtain ⟨old, q₀, q₁, hS⟩ := pieceSimpleAt_of_chainFacts hWω hl
  obtain ⟨-, hlen⟩ := walk_instr_of_launch hl
  obtain ⟨hev, -⟩ := GW1W.even_of_launches_walk hl
  have hlen2 : ℓ + 2 ≤ w.2.2.length := by
    have hL : w.2.2.length = 2 * ((PiecewiseConstantBoundaryData.jumpSet b jumps).card + 1) := by
      simp only [hw, boundaryWalkSpec, List.length_flatten, List.map_replicate, List.sum_replicate,
        List.length_cons, List.length_nil, smul_eq_mul]
      ring
    rw [hL] at hlen ⊢
    omega
  have hcap0 : WalkLaw.stageSet κ b jumps (capSpec w (ℓ + 2) (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) Er (ℓ + 2) ω =
      WalkLaw.stageSet κ b jumps w Er (ℓ + 2) ω := WalkInf.stageSet_capSpec_of_le hlen2 ω le_rfl
  have hcapl : ∀ τ : ℝ≥0∞, WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) Er ℓ ω =
      WalkLaw.stageSet κ b jumps w Er ℓ ω := fun τ => WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl
  rw [hcap0] at hZ ⊢
  set S₂ := Su ∪ WalkLaw.stageSet κ b jumps w Er (ℓ + 2) ω with hS₂
  have hS₂H : S₂ ⊆ H := union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ _)
    (WalkLaw.stageSet_subset_H _ _ _ _ _ _ _)
  have hS₂b : Bornology.IsBounded S₂ :=
    hZ.2.1.subset fun z hz => self_inter_H_subset_fillH S₂ ⟨hz, hS₂H hz⟩
  have hS₁ : Su ∪ WalkLaw.stageSet κ b jumps w Er ℓ ω ⊆ S₂ :=
    union_subset_union_right _ (WalkLaw.stageSet_mono (κ := κ) (b := b) (jumps := jumps) w Er ω
      (by omega : ℓ ≤ ℓ + 2))
  have hA₁eq : ∀ τ : ℝ≥0∞, fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) Er ℓ ω) ω =
      fillH (Su ∪ WalkLaw.stageSet κ b jumps w Er ℓ ω) := by
    intro τ
    rw [fillVer_of_bounded (B := fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) Er ℓ ω) (by
          change Bornology.IsBounded (Su ∪ WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) Er ℓ ω)
          rw [hcapl τ]; exact hS₂b.subset hS₁), fillH_closure]
    change fillH (Su ∪ WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) Er ℓ ω) = _
    rw [hcapl τ]
  have hcapsub : ∀ τ : ℝ≥0∞, WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) Er (ℓ + 1) ω ⊆ S₂ :=
    fun τ => (stageSet_capSpec_subset κ b jumps hl hS τ).trans subset_union_right
  have hA₂eq : ∀ q : ℚ, A₂ (Real.toNNReal q) ω =
      fillH (WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)) Er
        (ℓ + 1) ω) := by
    intro q
    rw [(hAω q).2, fillVer_of_bounded (hS₂b.subset (hcapsub _)), fillH_closure]
  have hK : fillH (K ω) = fillH (Su ∪ WalkLaw.stageSet κ b jumps w Er ℓ ω) := by
    rw [hKω hωF, hA0.1]
    exact hA₁eq _
  refine ⟨by rw [hK]; exact fillH_mono hS₁, fun q => by rw [hA₂eq q]; exact fillH_subset_H _,
    fun q => by rw [hA₂eq q]; exact fillH_mono (hcapsub _), ?_⟩
  rintro z ⟨hz | hz, hzH⟩
  · exact Or.inl (by rw [hK]; exact self_inter_H_subset_fillH _ ⟨Or.inl hz, hzH⟩)
  · rcases stageSet_succ_succ_subset κ b jumps hl hS hz with hzl | hzq
    · exact Or.inl (by rw [hK]; exact self_inter_H_subset_fillH _ ⟨Or.inr hzl, hzH⟩)
    · simp only [mem_iUnion, exists_prop] at hzq
      obtain ⟨q, hq, hzq⟩ := hzq
      have hq' : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < (E w ℓ ω).2 := by
        rwa [hEr, StagedReg.regFam, StagedReg.regHist_snd] at hq
      refine Or.inr (mem_iUnion₂.2 ⟨q, hq', ?_⟩)
      rw [hA₂eq q]
      exact self_inter_H_subset_fillH _ ⟨hzq, hzH⟩

/-- **The terminal hull identity of the step, almost surely on F2b′'s live event, from the line family and the
versions alone**: `Qx.ae_fill_eq_stepHull_of_versions` with its stage-set input discharged by `Qx.ae_phys`. -/
theorem ae_fill_eq_stepHull (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ) {F : Set Ω}
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {K : Ω → Set ℂ} {x₀ : Ω → ℝ}
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) {β : Ω → BoundaryWord}
    {types : Set Supp8.Q3Stop.WordType} (htypes : types.Countable) {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0}
    {relLife : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂ (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β types pc
      tL (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hcl2 : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F →
      (t : ℝ≥0∞) < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 → ∃ m, (S.ver m).a t ω < S.V m ω)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → Lv.angleWordType κ (-(Real.pi / 2)) (β ω) ∈ types)
    (hseed : ∀ w ∈ types, ∀ᵐ ω ∂P, ω ∈ Lv.wordTypeCell κ (-(Real.pi / 2)) β F w →
      ω ∈ Lv.seedCell κ (-(Real.pi / 2)) β F w)
    (hK2 : ∀ᵐ ω ∂P, ω ∈ F → ∀ m, Supp8.GB6.RelDrv.IsStopDrvMatch (driverCode h12p hκ (-(Real.pi / 2))
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
      (fun t => (S.ver m).W t ω) (S.V m ω))
    (hlife : ∀ᵐ ω ∂P, ω ∈ F → (driverOf h12p hκ (-(Real.pi / 2))
      (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω)
    (hA : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂ t ω = fillVer (WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1)) ω)
    (hWC : ∀ᵐ ω ∂P, WalkChainFacts κ b jumps (-(Real.pi / 2))
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω))
    (hrun : ∀ᵐ ω ∂P, ∀ n, ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
        ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n)
    (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω)
    (hFl : ∀ᵐ ω ∂P, ω ∈ F → (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ∀ᵐ ω ∂P, ω ∈ F → relLife ω ≠ ⊤ →
      LocalExt.IsDrvGood (recHist (recOf ⊤ (driverOf h12p hκ (-(Real.pi / 2))
        (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))) →
      IsHPHull (fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω)) →
      fillH (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (ℓ + 2)
          (-(Real.pi / 2)) ((0 : ℝ≥0) : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 2) ω) =
        stepHull (fillH (K ω)) (x₀ ω) (recDrv (driverOf h12p hκ (-(Real.pi / 2))
          (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))))
          ((driverOf h12p hκ (-(Real.pi / 2))
            (β ω, Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2.toNNReal : ℝ) := by
  have hA₁ : ∀ q : ℚ, ∀ᵐ ω ∂P, ω ∈ F → A₁ (Real.toNNReal q) ω = fillH (K ω) := by
    intro q
    filter_upwards [hA (Real.toNNReal q), hA 0, hKF, hrun, hFl] with ω hq h0 hK hr hl hωF
    have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠
          none := by
      rw [hr]; exact hl hωF
    obtain ⟨-, hlen⟩ := walk_instr_of_launch hl'
    rw [hK hωF, h0.1, hq.1]
    unfold fillVer
    beta_reduce
    rw [WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl]
  exact ae_fill_eq_stepHull_of_versions h12p hκ hKc hKp htypes S hcl2 hcover hseed hK2 hlife hA₁
    (ae_phys u l k ℓ hA hWC hrun hKF hFl)

/-- **A zero-lifetime piece adds nothing**: at a launching stage `ℓ` of the walk whose piece is simple
(`PieceSimpleAt`) with lifetime `0`, the stage set through the connector `ℓ + 1` is the stage set before `ℓ` (the piece's
only physical point is its real seed, and the connector launches nothing). -/
theorem stageSet_succ_succ_eq_of_zero {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {θ : ℝ}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ} {ω : Ω} {old : Set ℂ} {q₀ q₁ : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (hS : PieceSimpleAt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) ℓ).2.2.2.2.1
      (E ℓ ω).1 (E ℓ ω).2 old q₀ q₁) (h0 : (E ℓ ω).2 = 0) :
    WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps θ true) E (ℓ + 2) ω =
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps θ true) E ℓ ω := by
  have hstart : ∃ (f : ℂ → ℂ) (α : ℝ≥0 → ℂ), f (α 0) = (q₀ : ℂ) ∧
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) ℓ).2.2.2.2.1.tipSet
        (fun r : ℝ≥0 => (E ℓ ω).1 (min (r : ℝ≥0∞) (E ℓ ω).2).toNNReal) (E ℓ ω).2 =
        f '' (α '' {t | (t : ℝ≥0∞) ≤ (E ℓ ω).2}) := by
    have hS' := hS
    obtain ⟨f, α, C, hf, -, -, hW0, hWc, hgen, -, -, hs, -, -⟩ := hS'
    refine ⟨f, α, hs, ?_⟩
    refine CounterflowRange.tipSet_stopped_eq_of_tendsto hgen hWc hW0 fun t ht => hf _ ?_
    exact Sec7.IsGeneratingTrace.mem_Hbar hgen
      (hWc.mono fun s (hs : (s : ℝ≥0∞) < (E ℓ ω).2) => (show (s : ℝ≥0∞) ≤ (E ℓ ω).2 from hs.le)) hW0 ht
  obtain ⟨f, α, hs, himg⟩ := hstart
  have hno : WalkLaw.pieceSet κ b jumps (boundaryWalkSpec b jumps θ true) E (ℓ + 1) ω = ∅ := by
    unfold WalkLaw.pieceSet
    simp only [walk_noLaunch_succ hl, ↓reduceIte]
  have hp : WalkLaw.pieceSet κ b jumps (boundaryWalkSpec b jumps θ true) E ℓ ω = ∅ := by
    rw [pieceSet_walk_eq κ b jumps hl, himg]
    refine eq_empty_of_forall_notMem fun z hz => ?_
    obtain ⟨⟨_, ⟨t, ht, rfl⟩, hzt⟩, hzH⟩ := hz
    subst hzt
    have ht0 : t = 0 := by
      have : (t : ℝ≥0∞) ≤ 0 := by rw [← h0]; exact ht
      exact_mod_cast le_antisymm (by exact_mod_cast this) (zero_le (a := t))
    subst ht0
    have : (0 : ℝ) < (f (α 0)).im := hzH
    rw [hs] at this
    simp at this
  rw [show ℓ + 2 = ℓ + 1 + 1 from rfl, WalkLaw.stageSet_succ, WalkLaw.stageSet_succ, hno, hp, union_empty,
    union_empty]

end InteractingSLE.Theorem14.SB.Qx
