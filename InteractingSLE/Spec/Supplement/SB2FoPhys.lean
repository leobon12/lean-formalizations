/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxPhys

/-!
# D51: the step's terminal hull identity for the JOINT second line set

Worker PROVE-SB2-F3LAW (round 3, D51 item 1). With NOJUMP's joint second line set (`Nd.SB2LowerStageVersionStatement5`)
`A₂ t = fill (A ∪ B_{≤ℓ} capped at t)`, the stage-set input of `Qx.ae_fill_eq_stepHull_of_versions` still holds: each
`A₂ t` lies in `ℍ` and in the fill of the next retained union `S₂ = A ∪ B_{≤ℓ+1}`, and the points of `S₂` in `ℍ` lie
in `fill (A ∪ B_{<ℓ})` or in some `A₂ q` with `q` below the piece's lifetime (they are in B's own capped set, a subset).

* **`ae_phys_joint`** (`Qx.ae_phys` for the joint set), **`ae_fill_eq_stepHull_joint`** (`Qx.ae_fill_eq_stepHull`
  for the joint set).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Fo

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide GW1Bookkeep Lk Mf Qw Qx

theorem ae_phys_joint {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)
    {A₁ A₂ : ℝ≥0 → Ω → Set ℂ}
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
      A₂ (Real.toNNReal q) ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)) Er (ℓ + 1) ω) ω :=
      ae_all_iff.2 fun q => hA _
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
  have hcapsub : ∀ τ : ℝ≥0∞, Su ∪ WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) τ) Er (ℓ + 1) ω ⊆ S₂ :=
    fun τ => union_subset_union_right _ (Qx.stageSet_capSpec_subset κ b jumps hl hS τ)
  have hA₂eq : ∀ q : ℚ, A₂ (Real.toNNReal q) ω =
      fillH (Su ∪ WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)) Er
        (ℓ + 1) ω) := by
    intro q
    rw [(hAω q).2, fillVer_of_bounded (B := fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2)) ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)) Er (ℓ + 1) ω)
        (by
          change Bornology.IsBounded (Su ∪ WalkLaw.stageSet κ b jumps (capSpec w ℓ (-(Real.pi / 2))
            ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)) Er (ℓ + 1) ω)
          exact hS₂b.subset (hcapsub _)), fillH_closure]
  have hK : fillH (K ω) = fillH (Su ∪ WalkLaw.stageSet κ b jumps w Er ℓ ω) := by
    rw [hKω hωF, hA0.1]
    exact hA₁eq _
  refine ⟨by rw [hK]; exact fillH_mono hS₁, fun q => by rw [hA₂eq q]; exact fillH_subset_H _,
    fun q => by rw [hA₂eq q]; exact fillH_mono (hcapsub _), ?_⟩
  rintro z ⟨hz | hz, hzH⟩
  · exact Or.inl (by rw [hK]; exact self_inter_H_subset_fillH _ ⟨Or.inl hz, hzH⟩)
  · rcases Qx.stageSet_succ_succ_subset κ b jumps hl hS hz with hzl | hzq
    · exact Or.inl (by rw [hK]; exact self_inter_H_subset_fillH _ ⟨Or.inr hzl, hzH⟩)
    · simp only [mem_iUnion, exists_prop] at hzq
      obtain ⟨q, hq, hzq⟩ := hzq
      have hq' : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < (E w ℓ ω).2 := by
        rwa [hEr, StagedReg.regFam, StagedReg.regHist_snd] at hq
      refine Or.inr (mem_iUnion₂.2 ⟨q, hq', ?_⟩)
      rw [hA₂eq q]
      exact self_inter_H_subset_fillH _ ⟨Or.inr hzq, hzH⟩

theorem ae_fill_eq_stepHull_joint (h12p : Theorem12ParamStatement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
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
      A₂ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω)
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
  exact Qx.ae_fill_eq_stepHull_of_versions h12p hκ hKc hKp htypes S hcl2 hcover hseed hK2 hlife hA₁
    (ae_phys_joint u l k ℓ hA hWC hrun hKF hFl)

end InteractingSLE.Theorem14.SB.Fo
