/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ScheduleRun
import InteractingSLE.Spec.Supplement.GW2Sched
import InteractingSLE.Spec.Supplement.GW1PieceRun
import InteractingSLE.Spec.Supplement.SBLemmaS34Proof
import InteractingSLE.Spec.Exist.StagedLaw4
import InteractingSLE.Spec.Supplement.GW6Reduction

/-!
# Theorem 1.4: an own angle history is the range of a path (`SB.OwnHistoryPathRegStatement`)

Packet PROVE-T14-SB7, item (b). Lemmas S1–S4 of the supplement (pp. 576–582) treat the own angle history `A` of S0
(the frozen schedule history `⟨0, true, scheduleProgram 0 l⟩` through `k` instructions, `SB.schedulePrefix`) as "a
parameterized part of the original history": `A = p([0, 1])` for a continuous path from `0` in `closure ℍ`.

The run of a schedule (PROVE-T14-TIP3's `GW2Schedule.run_gw2`) launches piece `j` exactly when every earlier piece
stopped strictly before its lifetime, in the chart `succChart` (the root translation followed by the centred Loewner
maps of the earlier stopped pieces). The pieces are joined end to end: the physical start of piece `j + 1` is the
vertical limit at `0` of the next chart, which is the tip of piece `j` at its stop (both are the same radial limit,
`tendsto_tip_stopped_of_tendsto`). When every launched piece is regular (`GW1P.PieceRegular`: continuous driver up to
its stop and a continuous generating trace `α`), each chart along the run has a continuous boundary extension `f`
(PROVE-T14-GW1P's `isClosed_pieces_run`) and the tip set of the piece is `f(α([0, S]))`
(`tipSet_stopped_eq_of_tendsto`), the range of a path. Concatenating these paths (`Path.trans`) gives the history.

## Main results

* **`exists_path_prefixPhysSet_schedule`** (deterministic): if every launched piece of a schedule run is regular, the
  physical set through `k` instructions is `p([0, 1])` for a continuous path from `0` in `closure ℍ`;
* **`ownHistoryPathRegStatement`**: `SB.OwnHistoryPathRegStatement` (for every `StagedPiecesRegular` family);
* `s4HullRegStatement`: hence S4's hull clause `SB.S4HullRegStatement` (by `SB.s4HullRegStatement_of_path`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

universe u

namespace InteractingSLE

namespace Theorem14

namespace OwnHistoryPath

open Exist Exist.Staged Exist.StagedLaw GW2Schedule GW1P CounterflowRange

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The schedule history of S0 from the root `0` (GW2 convention). -/
abbrev schedSpec (l : List (ℝ × ℝ≥0)) : ExplSpec := (0, true, scheduleProgram 0 l)

/-- A stuck flow step changes neither the pieces nor the arcs. -/
theorem pieces_arcs_flowStep_of_isStuck (s : ExplState) (hs : IsStuck (stStatus s)) (k : ℕ)
    (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.flowStep κ b true s k D θ t).1 = s.1 ∧ (ExplState.flowStep κ b true s k D θ t).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases hs with h | ⟨o, h⟩
  · change status = Exist.StagedLaw.stDead at h
    subst h
    exact ⟨rfl, rfl⟩
  · change status = Exist.StagedLaw.stThr o at h
    subst h
    exact ⟨rfl, rfl⟩

/-- The run of a schedule after an instruction of the program. -/
theorem run_succ_sched (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length) :
    ExplState.run κ b jumps (schedSpec l) D (k + 1) = ExplState.flowStep κ b true
      (ExplState.run κ b jumps (schedSpec l) D k) k (D k) (schedAngle l k) (schedDelta 0 l k) := by
  have hins : (schedSpec l).2.2[k]? = some (Sum.inl (schedAngle l k, schedDelta 0 l k)) :=
    isFlowProg_scheduleProgram 0 l k hk
  rw [run_succ, hins]
  rfl

/-- The run of a schedule after the program has ended. -/
theorem run_succ_sched_of_le (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : (scheduleProgram 0 l).length ≤ k) :
    ExplState.run κ b jumps (schedSpec l) D (k + 1) = ExplState.run κ b jumps (schedSpec l) D k := by
  have hins : (schedSpec l).2.2[k]? = none := List.getElem?_eq_none hk
  rw [run_succ, hins]

/-- The own time of instruction `k` of a schedule. -/
theorem instrTime_sched (l : List (ℝ × ℝ≥0)) {k : ℕ} (hk : k < (scheduleProgram 0 l).length) :
    instrTime (schedSpec l) k = schedDelta 0 l k := by
  unfold instrTime
  rw [isFlowProg_scheduleProgram 0 l k hk]

/-- The physical set grows by the tip set of the launched piece. -/
theorem prefixPhysSet_succ_of_allSucc (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length) (hs : AllSucc (schedDelta 0 l) D k) :
    SB.prefixPhysSet κ b jumps (schedSpec l) D (k + 1) = SB.prefixPhysSet κ b jumps (schedSpec l) D k ∪
      (succChart 0 (schedDelta 0 l) D k).tipSet
        (fun r : ℝ≥0 => (D k).1 (min (r : ℝ≥0∞) (min (schedDelta 0 l k) (D k).2)).toNNReal)
        (min (schedDelta 0 l k) (D k).2) := by
  have h := run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := schedSpec l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D k hk.le
  obtain ⟨hlive, hchart⟩ := h.1 hs
  unfold SB.prefixPhysSet
  simp only []
  rw [run_succ_sched l D hk, flowStep_of_isLive _ hlive, pieces_launch, arcs_launch]
  have hc : (ExplState.run κ b jumps (schedSpec l) D k).2.2.2.2.1 = succChart 0 (schedDelta 0 l) D k := hchart
  rw [hc]
  ext z
  simp only [mem_union, mem_iUnion, List.mem_append, List.mem_singleton, exists_prop]
  constructor
  · rintro ((h1 | ⟨p, hp | rfl, hz⟩) | h3)
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr ⟨p, hp, hz⟩))
    · exact Or.inr hz
    · exact Or.inl (Or.inr h3)
  · rintro (((h1 | ⟨p, hp, hz⟩) | h3) | h4)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr ⟨p, Or.inl hp, hz⟩)
    · exact Or.inr h3
    · exact Or.inl (Or.inr ⟨_, Or.inr rfl, h4⟩)

/-- Without a launch the physical set does not change. -/
theorem prefixPhysSet_succ_of_not_allSucc (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length) (hs : ¬ AllSucc (schedDelta 0 l) D k) :
    SB.prefixPhysSet κ b jumps (schedSpec l) D (k + 1) = SB.prefixPhysSet κ b jumps (schedSpec l) D k := by
  have h := run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := schedSpec l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D k hk.le
  obtain ⟨h1, h2⟩ := pieces_arcs_flowStep_of_isStuck (κ := κ) (b := b) _ (h.2 hs) k (D k) (schedAngle l k)
    (schedDelta 0 l k)
  unfold SB.prefixPhysSet
  simp only []
  rw [run_succ_sched l D hk, h1, h2]

/-! ### The path -/

/-- The vertical approach to `0` stays in `ℍ`. -/
theorem tendsto_mul_I_nhdsWithin_H : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝[H] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have h : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝 0) (𝓝 (((0 : ℝ) : ℂ) * I)) :=
      ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
    rw [Complex.ofReal_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    change 0 < ((y : ℂ) * I).im
    simpa using hy

/-- **The physical set of a schedule run with regular pieces is the range of a path from `0`** (with the vertical
limit of the current chart at `0` as its end point while the history is live). -/
theorem exists_path_schedule (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (schedSpec l) D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime (schedSpec l) k) (D k).2)) :
    ∀ k : ℕ, ∃ (x : ℂ) (Γ : Path (0 : ℂ) x), range Γ = SB.prefixPhysSet κ b jumps (schedSpec l) D k ∧
      (∀ z ∈ range Γ, 0 ≤ z.im) ∧
      (k ≤ (scheduleProgram 0 l).length → AllSucc (schedDelta 0 l) D k →
        (∀ z ∈ H, (succChart 0 (schedDelta 0 l) D k).2.1 z ∈ H) ∧
        Tendsto (fun y : ℝ => (succChart 0 (schedDelta 0 l) D k).2.1 ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 x)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, Path.refl 0, ?_, ?_, fun _ _ => ⟨fun z hz => ?_, ?_⟩⟩
    · rw [Path.refl_range]
      unfold SB.prefixPhysSet
      simp [ExplState.run, ExplState.init]
    · intro z hz
      rw [Path.refl_range, mem_singleton_iff] at hz
      rw [hz, Complex.zero_im]
    · change (Chart.id.recenter 0).2.1 z ∈ H
      simpa [InteractingSLE.Chart.recenter, InteractingSLE.Chart.id] using hz
    · change Tendsto (fun y : ℝ => (Chart.id.recenter 0).2.1 ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 0)
      simp only [InteractingSLE.Chart.recenter, InteractingSLE.Chart.id, Complex.ofReal_zero, add_zero]
      exact tendsto_mul_I_nhdsWithin_H.mono_right nhdsWithin_le_nhds
  | succ k ih =>
  obtain ⟨x, Γ, hrange, him, hlim⟩ := ih
  by_cases hk : k < (scheduleProgram 0 l).length
  swap
  · refine ⟨x, Γ, ?_, him, fun hk' => absurd hk' (by omega)⟩
    rw [hrange]
    unfold SB.prefixPhysSet
    simp only []
    rw [run_succ_sched_of_le l D (not_lt.1 hk)]
  by_cases hs : AllSucc (schedDelta 0 l) D k
  swap
  · refine ⟨x, Γ, ?_, him, fun _ hs' => absurd (hs'.mono (Nat.le_succ k)) hs⟩
    rw [hrange, prefixPhysSet_succ_of_not_allSucc l D hk hs]
  obtain ⟨hmaps, hx⟩ := hlim hk.le hs
  have hrun := run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := schedSpec l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D k hk.le
  have hl := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := schedSpec l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk).1 hs
  have hr := hreg k _ _ hl
  rw [instrTime_sched l hk] at hr
  have hstop := hr.continuous_stoppedReal
  have hSne : min (schedDelta 0 l k) (D k).2 ≠ ⊤ :=
    ne_top_of_le_ne_top (schedDelta_ne_top 0 l k) (min_le_left _ _)
  have hgood : HasProperBdryExt (succChart 0 (schedDelta 0 l) D k) := by
    have h1 := (isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) (schedSpec l) D hreg k).1
    have h3 : (ExplState.run κ b jumps (schedSpec l) D k).2.2.2.2.1 = succChart 0 (schedDelta 0 l) D k :=
      (hrun.1 hs).2
    rwa [h3] at h1
  obtain ⟨f, C, hf, -⟩ := hgood
  obtain ⟨hW0, hWc, α, hα, -⟩ := hr
  set S := min (schedDelta 0 l k) (D k).2 with hSdef
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
  have hfc : ContinuousOn f Hbar := continuousOn_of_tendsto hf
  set T : ℝ≥0 := S.toNNReal with hTdef
  have hTS : (T : ℝ≥0∞) = S := ENNReal.coe_toNNReal hSne
  have hx0 : f 0 = x := by
    have h0 : (0 : ℂ) ∈ Hbar := by
      change (0 : ℝ) ≤ (0 : ℂ).im
      rw [Complex.zero_im]
    exact tendsto_nhds_unique ((hf 0 h0).comp tendsto_mul_I_nhdsWithin_H) hx
  -- the path of the new piece
  have hgS : ∀ s : unitInterval, ((((s : ℝ).toNNReal * T : ℝ≥0)) : ℝ≥0∞) ≤ S := fun s => by
    rw [← hTS]
    refine ENNReal.coe_le_coe.2 (mul_le_of_le_one_left (zero_le (a := T)) ?_)
    rw [Real.toNNReal_le_one]
    exact s.2.2
  have hgc : Continuous fun s : unitInterval => (s : ℝ).toNNReal * T :=
    (continuous_real_toNNReal.comp continuous_subtype_val).mul continuous_const
  have hαc : Continuous fun s : unitInterval => α ((s : ℝ).toNNReal * T) :=
    hα.2.1.comp_continuous hgc hgS
  have hcont : Continuous fun s : unitInterval => f (α ((s : ℝ).toNNReal * T)) :=
    hfc.comp_continuous hαc fun s => hαH _ (hgS s)
  let γ : Path x (f (α T)) :=
    { toFun := fun s => f (α ((s : ℝ).toNNReal * T))
      continuous_toFun := hcont
      source' := by
        change f (α (((0 : ℝ)).toNNReal * T)) = x
        rw [Real.toNNReal_zero, zero_mul, hα.1, hx0]
      target' := by
        change f (α (((1 : ℝ)).toNNReal * T)) = f (α T)
        rw [Real.toNNReal_one, one_mul] }
  have hγrange : range γ = f '' (α '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S}) := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨α _, ⟨_, hgS s, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      have htT : t ≤ T := by rw [← ENNReal.coe_le_coe, hTS]; exact ht
      rcases eq_or_ne T 0 with hT0 | hT0
      · have ht0 : t = 0 := le_antisymm (hT0 ▸ htT) (zero_le (a := t))
        refine ⟨0, ?_⟩
        change f (α (((0 : ℝ)).toNNReal * T)) = f (α t)
        rw [Real.toNNReal_zero, zero_mul, ht0]
      · have hTpos : (0 : ℝ) < T := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hT0)
        refine ⟨⟨(t : ℝ) / T, div_nonneg t.2 T.2, (div_le_one hTpos).2 (NNReal.coe_le_coe.2 htT)⟩, ?_⟩
        change f (α (((t : ℝ) / T).toNNReal * T)) = f (α t)
        congr 2
        ext
        rw [NNReal.coe_mul, Real.coe_toNNReal _ (div_nonneg (NNReal.coe_nonneg t) (NNReal.coe_nonneg T)),
          div_mul_cancel₀ _ hTpos.ne']
  have htip := tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht)
  have hfH : ∀ p ∈ Hbar, 0 ≤ (f p).im := fun p hp => by
    have := neBot_nhdsWithin_H hp
    exact ge_of_tendsto ((Complex.continuous_im.tendsto _).comp (hf p hp))
      (eventually_nhdsWithin_of_forall fun z hz => le_of_lt (hmaps z hz))
  refine ⟨f (α T), Γ.trans γ, ?_, ?_, fun _ _ => ⟨fun z hz => ?_, ?_⟩⟩
  · rw [Path.trans_range, hrange, hγrange, ← htip, prefixPhysSet_succ_of_allSucc l D hk hs]
  · intro z hz
    rw [Path.trans_range] at hz
    rcases hz with hz | hz
    · exact him z hz
    · rw [hγrange] at hz
      obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hz
      exact hfH _ (hαH t ht)
  · change (succChart 0 (schedDelta 0 l) D k).2.1
      (fwdMapInv (stopDrv (schedDelta 0 l k) (D k)) (stopTime (schedDelta 0 l k) (D k)) z) ∈ H
    exact hmaps _ (QuantumZipper.RS.fwdMapInv_mem_H hstop.1 hstop.2 (NNReal.coe_nonneg _) hz)
  · change Tendsto (fun y : ℝ => (succChart 0 (schedDelta 0 l) D k).2.1
      (fwdMapInv (stopDrv (schedDelta 0 l k) (D k)) (stopTime (schedDelta 0 l k) (D k)) ((y : ℂ) * I)))
      (𝓝[>] 0) (𝓝 (f (α T)))
    exact tendsto_tip_stopped_of_tendsto hα hWc hW0 (t := T) hTS.le (hf _ (hαH T hTS.le))

/-- **The own history of a schedule with regular pieces is `p([0, 1])`** for a continuous path from `0` in
`closure ℍ` (deterministic). -/
theorem exists_path_prefixPhysSet_schedule (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (schedSpec l) D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime (schedSpec l) k) (D k).2)) (k : ℕ) :
    ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
      SB.prefixPhysSet κ b jumps (schedSpec l) D k = p '' Icc 0 1 := by
  obtain ⟨x, Γ, hrange, him, -⟩ := exists_path_schedule (κ := κ) (b := b) (jumps := jumps) l D hreg k
  have himg : Γ.extend '' Icc 0 1 = range Γ := Γ.image_extend_of_subset subset_rfl
  refine ⟨Γ.extend, Γ.continuous_extend.continuousOn, Γ.extend_zero, fun s hs => ?_, ?_⟩
  · exact him _ (himg ▸ mem_image_of_mem _ hs)
  · rw [himg, hrange]

/-- **`SB.OwnHistoryPathRegStatement`**: for a family of staged histories that is `StagedPiecesRegular` for every
boundary-continued program, almost surely the own angle history of a schedule through `k` instructions is `p([0, 1])`
for a continuous path from `0` in `closure ℍ`. -/
theorem ownHistoryPathRegStatement : SB.OwnHistoryPathRegStatement.{u} := by
  intro κ _ _ b jumps _ Ω _ _ P _ h _ E _ hR l k _ hl
  have hbc : IsBoundaryContinuedProgram (schedSpec l).2.2 :=
    GW2Sched.isBoundaryContinuedProgram_scheduleProgram hl 0
  filter_upwards [(hR _ hbc).ae_pieceRegular] with ω hω
  exact exists_path_prefixPhysSet_schedule (κ := κ) (b := b) (jumps := jumps) l
    (fun j => E (schedSpec l) j ω) hω k

/-- **S4's hull clause** for regular families (`SB.S4HullRegStatement`), from `ownHistoryPathRegStatement` and
PROVE-T14-SB6's `SB.s4HullRegStatement_of_path`. -/
theorem s4HullRegStatement : SB.S4HullRegStatement.{u} :=
  SB.s4HullRegStatement_of_path ownHistoryPathRegStatement

end OwnHistoryPath

end Theorem14

end InteractingSLE
