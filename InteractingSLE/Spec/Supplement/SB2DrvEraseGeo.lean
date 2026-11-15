/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvEntrEv
import InteractingSLE.Spec.Supplement.SB2DrvErase
import InteractingSLE.Spec.Supplement.SB2DrvEntrance
import InteractingSLE.Spec.Supplement.WalkStageLocalAE
import InteractingSLE.Spec.Supplement.WalkMeanAssembly
import InteractingSLE.Spec.Supplement.WalkSideDom
import InteractingSLE.Spec.Supplement.WalkSideAssembly
import InteractingSLE.Spec.Supplement.WalkLeafChart
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier

/-!
# The geometry of SB2(1)'s erasure

Packet PROVE-T14-SB2DRV (round 3), the geometric half of clause (E2). The finite iterated unions
`B_n = A ∪ η_0([0, T_0]) ∪ ⋯ ∪ η_n([0, T_n])` of the entrance construction are relatively closed in `ℍ` (each capped
range is compact, `isClosed_image_frozen`), and almost surely on the launch event the domain of the launch chart lies
in `ℍ \ B_n` and is clopen there: the walk part from the run (`WalkSide.disjoint_dom_or_done`,
`WalkLeaf.mem_stageSet_of_frontier`), the erased part from

* **`SB2ErasedAvoidStatement`** (named input, Lemma S2's geometry, supplement p. 632 "the erased history lies in
  `K_A`"): almost surely on the launch event, the launch chart's domain `D_A` misses the upper flow up to
  `min(ζ, T_L)`.

Also: a version `A''` of the retained lower prefix with `A'' ⊆ ℍ`, `ℍ \ A''` open and measurable avoidance events
for every sample (`exists_walkVersion`), and the iterated-union facts `iterSet_subset_H`, `isOpen_H_sdiff_iterSet`,
`isOpen_sdiff_dom_iterSet`, `subset_sdiff_iterSet`, `measurableSet_disjoint_iterSet`.

**R48.** Theorems 1.2–1.3 are hypotheses; this serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw LocalSets Sec6 Restart WalkInf

/-! ### Closed capped ranges -/

/-- The range up to any time of a continuous path frozen after `m` is compact, hence closed. -/
theorem isClosed_image_frozen {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) {m : ℝ≥0} (hfz : ∀ t, m ≤ t → γ t = γ m)
    (τ : ℝ≥0∞) : IsClosed (γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ}) := by
  by_cases hτ : τ ≤ (m : ℝ≥0∞)
  · have hτt : τ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτ
    have e : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ} = Icc 0 τ.toNNReal := by
      ext t
      simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and]
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hτt]
    rw [e]
    exact (isCompact_Icc.image hγ).isClosed
  · have e : γ '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ} = γ '' Icc 0 m := by
      ext z
      constructor
      · rintro ⟨t, -, rfl⟩
        by_cases htm : t ≤ m
        · exact ⟨t, ⟨zero_le, htm⟩, rfl⟩
        · exact ⟨m, ⟨zero_le, le_rfl⟩, (hfz t (not_le.1 htm).le).symm⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, (ENNReal.coe_le_coe.2 ht.2).trans (not_le.1 hτ).le, rfl⟩
    rw [e]
    exact (isCompact_Icc.image hγ).isClosed

/-! ### Iterated unions: geometry and measurability -/

section IterGeo

variable {Ω : Type*} {𝒴 : Type*} {A : Ω → Set ℂ} {η : ℕ → Ω → ℝ≥0 → ℂ} {Y : Ω → 𝒴}
  {S : 𝒴 → (ℚ≥0 → ℂ) → ℝ≥0∞}

theorem iterSet_subset_H (hA : ∀ ω, A ω ⊆ H) (n : ℕ) (ω : Ω) : iterSet A η Y S n ω ⊆ H := by
  induction n with
  | zero => exact union_subset (hA ω) inter_subset_right
  | succ n ih => exact union_subset ih inter_subset_right

theorem isOpen_H_sdiff_iterSet {ω : Ω} (hA : IsOpen (H \ A ω))
    (hK : ∀ j, IsClosed (η j ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S (Y ω) (pathCoord (η j ω))})) (n : ℕ) :
    IsOpen (H \ iterSet A η Y S n ω) := by
  have step : ∀ (X : Set ℂ) (j : ℕ), IsOpen (H \ X) →
      IsOpen (H \ (X ∪ rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω))))) := by
    intro X j hX
    have e : H \ (X ∪ rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω)))) =
        (H \ X) ∩ (η j ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S (Y ω) (pathCoord (η j ω))})ᶜ := by
      ext z
      simp only [rangeUpTo, Set.mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff, not_or, not_and]
      tauto
    rw [e]
    exact hX.inter (hK j).isOpen_compl
  induction n with
  | zero => exact step _ 0 hA
  | succ n ih => exact step _ (n + 1) ih

theorem isOpen_sdiff_dom_iterSet {ω : Ω} {Dm : Set ℂ} (hA : IsOpen ((H \ A ω) \ Dm))
    (hK : ∀ j, IsClosed (η j ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S (Y ω) (pathCoord (η j ω))})) (n : ℕ) :
    IsOpen ((H \ iterSet A η Y S n ω) \ Dm) := by
  have step : ∀ (X : Set ℂ) (j : ℕ), IsOpen ((H \ X) \ Dm) →
      IsOpen ((H \ (X ∪ rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω))))) \ Dm) := by
    intro X j hX
    have e : (H \ (X ∪ rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω))))) \ Dm =
        ((H \ X) \ Dm) ∩ (η j ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S (Y ω) (pathCoord (η j ω))})ᶜ := by
      ext z
      simp only [rangeUpTo, Set.mem_sdiff, mem_union, mem_inter_iff, mem_compl_iff, not_or, not_and]
      tauto
    rw [e]
    exact hX.inter (hK j).isOpen_compl
  induction n with
  | zero => exact step _ 0 hA
  | succ n ih => exact step _ (n + 1) ih

theorem subset_sdiff_iterSet {ω : Ω} {Dm : Set ℂ} (hA : Dm ⊆ H \ A ω)
    (hR : ∀ j, Disjoint Dm (rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω))))) (n : ℕ) :
    Dm ⊆ H \ iterSet A η Y S n ω := by
  induction n with
  | zero =>
    intro z hz
    exact ⟨(hA hz).1, fun h => h.elim (hA hz).2 (Set.disjoint_left.1 (hR 0) hz)⟩
  | succ n ih =>
    intro z hz
    exact ⟨(ih hz).1, fun h => h.elim (ih hz).2 (Set.disjoint_left.1 (hR (n + 1)) hz)⟩

theorem measurableSet_disjoint_iterSet [MeasurableSpace Ω] {ζ : ℕ → Ω → ℝ≥0∞}
    (hc : ∀ n ω, Continuous (η n ω)) (h0 : ∀ n ω, η n ω 0 ∉ H)
    (hA : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet {ω | Disjoint (A ω) U})
    (hR : ∀ n, Measurable (ruleHist (η n) (ζ n) Y S)) (n : ℕ) {U : TopologicalSpace.Opens ℂ}
    (hUH : (U : Set ℂ) ⊆ H) : MeasurableSet {ω | Disjoint (iterSet A η Y S n ω) U} := by
  have step : ∀ (X : Ω → Set ℂ) (j : ℕ), MeasurableSet {ω | Disjoint (X ω) U} →
      MeasurableSet {ω | Disjoint (X ω ∪ rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω)))) U} := by
    intro X j hX
    have e : {ω | Disjoint (X ω ∪ rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω)))) U} =
        {ω | Disjoint (X ω) U} ∩ {ω | Disjoint (rangeUpTo (η j ω) (S (Y ω) (pathCoord (η j ω)))) U} := by
      ext ω
      simp only [mem_ofPred_eq, disjoint_union_left, mem_inter_iff]
    rw [e, ruleHist_preimage_avoidHist (ζ := ζ j) (hc j) (h0 j) U.isOpen hUH]
    exact hX.inter (hR j (measurableSet_avoidHist U.isOpen.measurableSet))
  induction n with
  | zero => exact step A 0 (hA U hUH)
  | succ n ih => exact step _ (n + 1) ih

end IterGeo

/-! ### A capped point before the first hit is a point of the flow before its first visit -/

theorem capped_point_le_firstVisit {γ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {z : ℂ} {γc : ℝ≥0 → ℂ} {m : ℝ≥0}
    (hc : Continuous γc) (hver : ∀ t, γc t = γ (capTime m ζ t)) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) ≤ hitQ z (pathCoord γc)) :
    ((capTime m ζ t : ℝ≥0) : ℝ≥0∞) ≤ min ζ (firstVisit γ ζ z) := by
  have h1 := coe_capTime_le (ζ := ζ) m t
  refine le_min (h1.trans (min_le_left _ _)) (le_iInf₂ fun s' hs' => ?_)
  by_contra hlt
  rw [not_le] at hlt
  have hs'c : (s' : ℝ≥0∞) ≤ min ζ m := (hlt.trans_le h1).le
  have hγc : γc s' = z := by rw [hver, capTime_of_le hs'c]; exact hs'.2
  have hhit : hitQ z (pathCoord γc) ≤ s' := by
    rw [hitQ_pathCoord hc]
    exact iInf₂_le s' hγc
  have h2 : ((capTime m ζ t : ℝ≥0) : ℝ≥0∞) ≤ t := ENNReal.coe_le_coe.2 (capTime_le_self m t)
  exact absurd (h2.trans (ht.trans hhit)) (not_le.2 hlt)

/-! ### The named geometric input -/

/-- **Named input (Lemma S2's geometry of the erasure, supplement p. 632)**: almost surely on the launch event, the
domain `D_A` of the launch chart misses the upper flow up to `min(ζ, T_L)` ("the erased history lies in `K_A`"). -/
def SB2ErasedAvoidStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
    SB2LaunchProblem κ b jumps P h E k u ψ η ζ →
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) →
      Disjoint ((launchChart κ b jumps E (k + 1) ω).dom : Set ℂ)
        (η ω '' {s : ℝ≥0 | (s : ℝ≥0∞) ≤
          min (ζ ω) (firstVisit (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E (k + 1) u ω)))})

/-! ### SB2(1): the walk version and the domain of the finite unions -/

section SB2

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **A version of the retained lower prefix that is nice at every sample**: in `ℍ`, with open complement in `ℍ`, with
measurable avoidance events, almost surely the explored set. -/
theorem exists_walkVersion (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ A'' : Ω → Set ℂ, (∀ ω, A'' ω ⊆ H) ∧ (∀ ω, IsOpen (H \ A'' ω)) ∧
      (∀ᵐ ω ∂P, A'' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) ∧
      ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet {ω | Disjoint (A'' ω) U} := by
  classical
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hS := HP.staged _ (isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true)
  obtain ⟨hev, hopen, -⟩ := walkPrefix_markedLocal h12p h13 HP hu₀ (k + 1)
  obtain ⟨A', hA'H, hA'ae, hA'm⟩ := WalkLaw.exists_version_of_aeSigma
    (fun ω => WalkLaw.stageSet_subset_H κ b jumps _ _ (k + 1) ω) hopen hev
  set N : Set Ω := {ω | ¬ IsOpen (H \ A' ω)} with hN
  have hae : ∀ᵐ ω ∂P, IsOpen (H \ A' ω) := by
    filter_upwards [hA'ae, hopen] with ω h1 h2
    rw [h1]
    exact h2
  have hN0 : P N = 0 := ae_iff.1 hae
  set Good : Set Ω := (toMeasurable P N)ᶜ with hGood
  have hGm : MeasurableSet Good := (measurableSet_toMeasurable _ _).compl
  have hGo : ∀ ω ∈ Good, IsOpen (H \ A' ω) := fun ω hω => by
    by_contra hn
    exact hω (subset_toMeasurable P N hn)
  have hGae : ∀ᵐ ω ∂P, ω ∈ Good := by
    rw [ae_iff]
    have e : {ω | ¬ ω ∈ Good} = toMeasurable P N := by ext ω; simp [hGood]
    rw [e, measure_toMeasurable]
    exact hN0
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  refine ⟨fun ω => if ω ∈ Good then A' ω else ∅, fun ω => ?_, fun ω => ?_, ?_, fun U hUH => ?_⟩
  · by_cases hω : ω ∈ Good
    · simp only [hω, ite_true]; exact hA'H ω
    · simp only [hω, ite_false]; exact empty_subset _
  · by_cases hω : ω ∈ Good
    · simp only [hω, ite_true]; exact hGo ω hω
    · simp only [hω, ite_false, sdiff_empty]; exact hHo
  · filter_upwards [hGae, hA'ae] with ω h1 h2
    simp only [h1, ite_true, h2]
  · have e : {ω | Disjoint ((fun ω => if ω ∈ Good then A' ω else ∅) ω) U} =
        (Good ∩ {ω | Disjoint (A' ω) U}) ∪ Goodᶜ := by
      ext ω
      by_cases hω : ω ∈ Good <;> simp [hω]
    rw [e]
    exact (hGm.inter (hS.2.1 (k + 1) _ (hA'm U hUH))).union hGm.compl

/-- **The geometry of the finite unions**: almost surely on the launch event, for every `n`, the chart's domain lies in
`ℍ \ B_n` and is clopen there (`B_n` built on a nice version `A''` of the retained lower prefix). -/
theorem ae_dom_iterSet (hgeo : SB2ErasedAvoidStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) {u₀ : ℂ → ℝ} (D : EntranceUnion κ b jumps P h E k u η ζ u₀)
    {A'' : Ω → Set ℂ} (hA''o : ∀ ω, IsOpen (H \ A'' ω))
    (hA''ae : ∀ᵐ ω ∂P, A'' ω = WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω) :
    ∀ᵐ ω ∂P, ω ∈ launchSet κ b jumps E (k + 1) → ∀ n,
      ((I.chart ω).dom : Set ℂ) ⊆ H \ iterSet A'' D.ηc D.point hitQ n ω ∧
      IsOpen ((H \ iterSet A'' D.ηc D.point hitQ n ω) \ (I.chart ω).dom) := by
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hR := HP.pieces_regular _ hw
  filter_upwards [hgeo κ b jumps P h E k u ψ η ζ HP, I.chart_eq,
    ae_verChart_eq_runChart hR (HP.drivers_regular _) (k + 1), hR.ae_pieceRegular, hA''ae, D.version, D.Lp_eq]
    with ω hg hce hver hpr hA hv hL hl n
  have hDrun : ((I.chart ω).dom : Set ℂ) =
      (((ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)).2.2.2.2.1).dom : Set ℂ) := by
    show ((((verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (I.entry ω)).dom : Set ℂ)) = _
    rw [Chart.dom_recenter, hver]
    rfl
  have hDl : ((I.chart ω).dom : Set ℂ) = ((launchChart κ b jumps E (k + 1) ω).dom : Set ℂ) := by
    have e := congrArg (fun c : Chart => (c.dom : Set ℂ)) (hce hl)
    simp only [Chart.dom_recenter] at e
    rw [← e]
    show ((((verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (I.entry ω)).dom : Set ℂ)) = _
    rw [Chart.dom_recenter]
  have hreg' : ∀ (j : ℕ) (c : Chart) (θ' : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hlj => hpr j c θ' hlj
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  have hdis := (WalkSide.disjoint_dom_or_done (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1)).resolve_left hnd
  have hconf := (GW1RestartFinal.chart_boundaryRange_run (κ := κ) (b := b) (jumps := jumps) _ _ hreg' (k + 1)).1
  have hwalk : ((I.chart ω).dom : Set ℂ) ⊆ H \ A'' ω := by
    rw [hDrun, hA]
    intro z hz
    exact ⟨hconf.dom_subset hz, fun hzA => Set.disjoint_left.1 hdis hz hzA.1⟩
  have hwalko : IsOpen ((H \ A'' ω) \ (I.chart ω).dom) := by
    rw [hDrun]
    refine WalkSide.isOpen_diff_dom (hA''o ω) fun z hzH hzcl hzD => ?_
    rw [hA]
    exact WalkLeaf.mem_stageSet_of_frontier _ _ ω hreg' (k + 1) z hzH hzcl hzD
  have hz' : D.point ω = (realMin (lowerPrefix κ b jumps E (k + 1) u ω) : ℂ) := by
    simp only [EntranceUnion.point, hL hl]
  have hRj : ∀ j, Disjoint ((I.chart ω).dom : Set ℂ)
      (rangeUpTo (D.ηc j ω) (hitQ (D.point ω) (pathCoord (D.ηc j ω)))) := by
    intro j
    rw [Set.disjoint_right]
    rintro z ⟨⟨t, ht, rfl⟩, -⟩
    have hs := capped_point_le_firstVisit (D.paths.cont j ω) (hv j) ht
    rw [hz'] at hs
    rw [hDl, hv j t]
    exact Set.disjoint_right.1 (hg hl) ⟨capTime (j : ℝ≥0) (ζ ω) t, hs, rfl⟩
  have hK : ∀ j, IsClosed (D.ηc j ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ hitQ (D.point ω) (pathCoord (D.ηc j ω))}) :=
    fun j => isClosed_image_frozen (D.paths.cont j ω) (D.frozen j ω) _
  exact ⟨subset_sdiff_iterSet hwalk hRj n, isOpen_sdiff_dom_iterSet hwalko hK n⟩

end SB2

end InteractingSLE.Theorem14.SB.Lv
