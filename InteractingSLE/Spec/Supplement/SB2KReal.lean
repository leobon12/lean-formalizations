/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2KPast
import InteractingSLE.Spec.Supplement.SB2JZero
import InteractingSLE.Spec.Supplement.WalkStageLocalMeas
import InteractingSLE.Spec.Supplement.SBLyRight
import InteractingSLE.Spec.Supplement.WalkIntChronoRange

/-!
# The leftmost real point of SB2(1)'s retained lower prefix

Packet PROVE-T14-SB2FIN5 (SB2(1)'s past-measurable entry point, step 1). SB2(1)'s entry point is the left entry value
of the launch chart at `L = realMin (lowerPrefix …)`. The retained prefix is the root, the launched pieces, the real
connectors and the bridge `[u, 0]`. This file reads `L` off the launched pieces:

* `physPiece`, **`iUnion_pieces_run`**: the recorded pieces of a run are the physical pieces of its launching
  instructions;
* **`realMin_lt_iff`**: when every connector lies in `[0, ∞)` (GW1's right walk without left thresholds,
  `GW1Conn.rInv_run`), `L < q` iff `u < q` or some launched piece has a real point left of `q`.

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The physical piece launched by instruction `j` (empty if it launches nothing): the tip set, through the chart of
the run before the instruction, of the driver stopped at `min t_j ζ_j`. -/
def physPiece (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (j : ℕ) :
    Set ℂ :=
  if (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none then ∅ else
    (stChart (ExplState.run κ b jumps spec D j)).tipSet
      (fun r : ℝ≥0 => (D j).1 (min (r : ℝ≥0∞) (min (instrTime spec j) (D j).2)).toNNReal)
      (min (instrTime spec j) (D j).2)

/-- **The recorded pieces of a run are the physical pieces of its launching instructions.** -/
theorem iUnion_pieces_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    (⋃ p ∈ (ExplState.run κ b jumps spec D n).1, p.1.tipSet p.2.1 p.2.2) =
      ⋃ j ∈ Finset.range n, physPiece κ b jumps spec D j := by
  induction n with
  | zero => simp [ExplState.run, ExplState.init]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.set_biUnion_insert, ← ih, union_comm]
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · have e := GW1P.pieces_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      simp only [physPiece, hl, ↓reduceIte, union_empty, e]
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      have hne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by
        rw [hl]; exact Option.some_ne_none _
      rw [he, CounterflowRange.pieces_launch]
      simp only [physPiece, hne, ↓reduceIte]
      ext z
      simp only [mem_iUnion, mem_union, exists_prop, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨p, hp | rfl, hz⟩
        · exact Or.inl ⟨p, hp, hz⟩
        · exact Or.inr hz
      · rintro (⟨p, hp, hz⟩ | hz)
        · exact ⟨p, Or.inl hp, hz⟩
        · exact ⟨_, Or.inr rfl, hz⟩

/-- **The leftmost real point of the retained lower prefix.** If the prefix is compact and every connector of the run
lies in `[0, ∞)`, then `L = realMin (lowerPrefix …) < q` iff `u < q` or a launched piece has a real point left of
`q`. -/
theorem realMin_lt_iff {Ω : Type*} {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} {u : ℝ} (hu : u ≤ 0)
    {ω : Ω} (hAc : IsCompact (lowerPrefix κ b jumps E n u ω))
    (harc : ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n).2.1, a ⊆ Ici 0) (q : ℝ) :
    realMin (lowerPrefix κ b jumps E n u ω) < q ↔ u < q ∨ ∃ j < n, ∃ z ∈ physPiece κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) j, z.im = 0 ∧ z.re < q := by
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec
  set D := fun j => E spec j ω with hD
  have hS : {x : ℝ | (x : ℂ) ∈ lowerPrefix κ b jumps E n u ω}.Nonempty :=
    ⟨u, Or.inr ⟨u, ⟨le_rfl, hu⟩, rfl⟩⟩
  have hB : BddBelow {x : ℝ | (x : ℂ) ∈ lowerPrefix κ b jumps E n u ω} := by
    obtain ⟨C, hC⟩ := hAc.isBounded.exists_norm_le
    refine ⟨-C, fun x hx => ?_⟩
    have h1 := hC _ hx
    rw [Complex.norm_real, Real.norm_eq_abs] at h1
    exact neg_le_of_abs_le h1
  have hmem : ∀ z, z ∈ lowerPrefix κ b jumps E n u ω ↔
      z = 0 ∨ (∃ j < n, z ∈ physPiece κ b jumps spec D j) ∨
        (∃ a ∈ (ExplState.run κ b jumps spec D n).2.1, ∃ x ∈ a, (x : ℂ) = z) ∨ ∃ x ∈ Icc u 0, (x : ℂ) = z := by
    intro z
    have hP := iUnion_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D n
    simp only [lowerPrefix, prefixPhysSet, ← hspec, ← hD, hP]
    simp only [mem_union, mem_singleton_iff, mem_iUnion, Finset.mem_range, exists_prop, mem_image]
    have h0 : (spec.1 : ℂ) = 0 := by simp [hspec, boundaryWalkSpec]
    rw [h0]
    simp only [or_assoc]
  unfold realMin
  rw [csInf_lt_iff hB hS]
  constructor
  · rintro ⟨x, hx, hxq⟩
    rcases (hmem _).1 hx with h0 | ⟨j, hj, hz⟩ | ⟨a, ha, y, hy, hyx⟩ | ⟨y, hy, hyx⟩
    · have : x = 0 := by exact_mod_cast h0
      exact Or.inl (by linarith)
    · exact Or.inr ⟨j, hj, x, hz, by simp, by simpa using hxq⟩
    · have hyx' : y = x := by exact_mod_cast hyx
      have := harc a ha hy
      rw [hyx'] at this
      exact Or.inl (lt_of_le_of_lt hu (lt_of_le_of_lt this hxq))
    · have hyx' : y = x := by exact_mod_cast hyx
      exact Or.inl (lt_of_le_of_lt (hyx' ▸ hy.1) hxq)
  · rintro (huq | ⟨j, hj, z, hz, him, hre⟩)
    · exact ⟨u, (hmem _).2 (Or.inr (Or.inr (Or.inr ⟨u, ⟨le_rfl, hu⟩, rfl⟩))), huq⟩
    · refine ⟨z.re, (hmem _).2 (Or.inr (Or.inl ⟨j, hj, ?_⟩)), hre⟩
      have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext (by simp) (by simp [him])
      rwa [hz']

/-- The real ray `(−∞, r]` in `ℂ`. -/
def rayK (r : ℝ) : Set ℂ := {z | z.im = 0 ∧ z.re ≤ r}

theorem isClosed_rayK (r : ℝ) : IsClosed (rayK r) :=
  (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le Complex.continuous_re continuous_const)

open WalkLaw in
/-- **A real point of a continuous path left of `q`, by dyadic times**: a path continuous on `[0, S]` (`S` finite) has
a real point left of `q` iff for some rational `r < q` and every `p`, some time `m / (N + 1) ≤ S` is mapped within
`1 / (p + 1)` of the ray `(−∞, r]`. -/
theorem exists_real_lt_iff_qTime {F : ℝ≥0 → ℂ} {S : ℝ≥0∞} (hS : S ≠ ⊤)
    (hF : ContinuousOn F {t | (t : ℝ≥0∞) ≤ S}) (q : ℝ) :
    (∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ S ∧ (F t).im = 0 ∧ (F t).re < q) ↔
      ∃ r : ℚ, (r : ℝ) < q ∧ ∀ p : ℕ, ∃ m N : ℕ, (qTime m N : ℝ≥0∞) ≤ S ∧
        infDist (F (qTime m N)) (rayK r) < 1 / ((p : ℝ) + 1) := by
  constructor
  · rintro ⟨t, htS, him, hre⟩
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn hre
    refine ⟨r, hr2, fun p => ?_⟩
    obtain ⟨m, hm, hmt⟩ := exists_qTime_tendsto t
    have hmS : ∀ N, (qTime (m N) N : ℝ≥0∞) ≤ S := fun N => (ENNReal.coe_le_coe.2 (hm N)).trans htS
    have hc : Tendsto (fun N => F (qTime (m N) N)) atTop (𝓝 (F t)) :=
      (hF t htS).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hmt, Eventually.of_forall hmS⟩)
    have h0 : infDist (F t) (rayK r) = 0 := infDist_zero_of_mem ⟨him, hr1.le⟩
    have hd : Tendsto (fun N => infDist (F (qTime (m N) N)) (rayK r)) atTop (𝓝 0) := by
      rw [← h0]
      exact ((continuous_infDist_pt (rayK r)).tendsto _).comp hc
    obtain ⟨N, hN⟩ := (hd.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((p : ℝ) + 1)))).exists
    exact ⟨m N, N, hmS N, hN⟩
  · rintro ⟨r, hrq, hr⟩
    choose m N hmS hd using hr
    set T : ℝ≥0 := S.toNNReal with hT
    have hmem : ∀ p, qTime (m p) (N p) ∈ Icc (0 : ℝ≥0) T := fun p =>
      ⟨zero_le, by
        rw [hT, ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hS]
        exact hmS p⟩
    obtain ⟨t, htT, φ, hφ, hlim⟩ := isCompact_Icc.tendsto_subseq hmem
    have htS : (t : ℝ≥0∞) ≤ S := by
      rw [← ENNReal.coe_toNNReal hS]
      exact ENNReal.coe_le_coe.2 htT.2
    have hc : Tendsto (fun p => F (qTime (m (φ p)) (N (φ p)))) atTop (𝓝 (F t)) :=
      (hF t htS).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun p => hmS (φ p)⟩)
    have hd1 : Tendsto (fun p => infDist (F (qTime (m (φ p)) (N (φ p)))) (rayK r)) atTop
        (𝓝 (infDist (F t) (rayK r))) := ((continuous_infDist_pt (rayK r)).tendsto _).comp hc
    have hd2 : Tendsto (fun p => infDist (F (qTime (m (φ p)) (N (φ p)))) (rayK r)) atTop (𝓝 0) := by
      have hb : Tendsto (fun p : ℕ => 1 / ((φ p : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
      exact squeeze_zero (fun p => infDist_nonneg) (fun p => (hd (φ p)).le) hb
    have h0 : infDist (F t) (rayK r) = 0 := tendsto_nhds_unique hd1 hd2
    have hK : F t ∈ rayK r := by
      rw [← (isClosed_rayK r).closure_eq, mem_closure_iff_infDist_zero ⟨((r : ℝ) : ℂ), by simp [rayK]⟩]
      exact h0
    exact ⟨t, htS, hK.1, lt_of_le_of_lt hK.2 hrq⟩

/-- **Before the run is finished every launched piece has a finite stop** (a launch with infinite stop finishes the
run, and a finished run stays finished). -/
theorem stop_ne_top_of_not_done (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {j n : ℕ} (hjn : j < n)
    (hl : (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none)
    (hn : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) :
    min (instrTime spec j) (D j).2 ≠ ⊤ := by
  intro htop
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hcθ
  have hd : stStatus (ExplState.run κ b jumps spec D (j + 1)) = GW1Conn.stDone := by
    rw [he]
    exact Lx.stStatus_launch_of_top _ _ _ _ _ htop
  have key : ∀ m, j + 1 ≤ m → stStatus (ExplState.run κ b jumps spec D m) = GW1Conn.stDone := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hd
    | succ m _ ih =>
      rw [GW1WalkFinish.done_run_succ spec D ih]
      exact ih
  exact hn (key n hjn)

open WalkLaw in
/-- **A regular launched piece is a continuous path, the limit of its approximating tip points.** -/
theorem exists_physPiece_path (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hD : ∀ (j : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2)) {j : ℕ}
    (hl : (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none) :
    ∃ F : ℝ≥0 → ℂ, ContinuousOn F {t | (t : ℝ≥0∞) ≤ min (instrTime spec j) (D j).2} ∧
      physPiece κ b jumps spec D j = F '' {t | (t : ℝ≥0∞) ≤ min (instrTime spec j) (D j).2} ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ min (instrTime spec j) (D j).2 →
        Tendsto (fun n => tipApprox κ b jumps spec D j t n) atTop (𝓝 (F t)) := by
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hl
  have hpr := hD j x.1 x.2 (by rw [hx])
  obtain ⟨f, C, hf, -⟩ := (GW1P.isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) spec D hD j).1
  set S : ℝ≥0∞ := min (instrTime spec j) (D j).2 with hS
  obtain ⟨hW0, hWc, α, hα, -⟩ := hpr
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
  have hy : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))⟩
  refine ⟨fun t => f (α t), (GW1P.continuousOn_of_tendsto hf).comp hα.2.1 fun t ht => hαH t ht, ?_,
    fun t ht => (CounterflowRange.tendsto_tip_stopped_of_tendsto hα hWc hW0 ht (hf _ (hαH t ht))).comp hy⟩
  simp only [physPiece, hl, ↓reduceIte]
  rw [← hS, CounterflowRange.tipSet_stopped_eq_of_tendsto hα hWc hW0 fun t ht => hf _ (hαH t ht), image_image]

open WalkLaw in
/-- **The events "a launched piece has a real point left of `q`" are measurable** on an event `M` of regular pieces,
before the run is finished: they agree there with measurable events built from the measurable versions of the
approximating tip points (`WalkLaw.exists_measurable_tipApprox`), their limits, dyadic times and the rays
`(−∞, r]` (`exists_real_lt_iff_qTime`). -/
theorem exists_measurableSet_physPiece_real.{v} (hb : IsPiecewiseConstantBoundaryData b jumps) (spec : ExplSpec)
    {Ω : Type v} [MeasurableSpace Ω] {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) {M : Set Ω} (hM : MeasurableSet M)
    (hMreg : ∀ ω ∈ M, ∀ (j : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
      GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2)) (n : ℕ) :
    ∃ S : ℝ → Set Ω, (∀ q, MeasurableSet (S q)) ∧ ∀ ω ∈ M,
      stStatus (ExplState.run κ b jumps spec (fun i => E i ω) n) ≠ GW1Conn.stDone → ∀ q : ℝ,
        (ω ∈ S q ↔ ∃ j < n, ∃ z ∈ physPiece κ b jumps spec (fun i => E i ω) j, z.im = 0 ∧ z.re < q) := by
  choose Y hYm hY using fun (j : ℕ) (τ : ℝ≥0) (m : ℕ) =>
    exists_measurable_tipApprox hb spec hEm hreg hM hMreg j τ m
  set Fm : ℕ → ℝ≥0 → Ω → ℂ := fun j τ ω => limUnder atTop (fun m => Y j τ m ω) with hFm
  have hFmm : ∀ j τ, Measurable (Fm j τ) := fun j τ =>
    (StronglyMeasurable.limUnder (fun m => (hYm j τ m).stronglyMeasurable)).measurable
  have hL : ∀ j, MeasurableSet {ω | (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none} :=
    fun j => ((runMeasStatement κ b jumps hb spec E hEm hreg) j).1
  refine ⟨fun q => ⋃ j ∈ Finset.range n,
    ({ω | (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j ≠ none} ∩
      ⋃ r : ℚ, {_ω | (r : ℝ) < q} ∩ ⋂ p : ℕ, ⋃ m : ℕ, ⋃ N : ℕ,
        {ω | (qTime m N : ℝ≥0∞) ≤ min (instrTime spec j) (E j ω).2 ∧
          infDist (Fm j (qTime m N) ω) (rayK r) < 1 / ((p : ℝ) + 1)}), fun q => ?_, ?_⟩
  · refine MeasurableSet.biUnion (Finset.range n).countable_toSet fun j _ => (hL j).inter ?_
    refine MeasurableSet.iUnion fun r => MeasurableSet.const _ |>.inter ?_
    refine MeasurableSet.iInter fun p => MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun N => ?_
    exact (measurableSet_le measurable_const (measurable_const.min (measurable_snd.comp (hEm j)))).inter
      (measurableSet_lt ((continuous_infDist_pt _).measurable.comp (hFmm j _)) measurable_const)
  · intro ω hω hnd q
    have hD : ∀ (j : ℕ) (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (E j ω).1 (min (instrTime spec j) (E j ω).2) := hMreg ω hω
    simp only [Finset.mem_range, mem_iUnion, mem_inter_iff, mem_ofPred_eq, mem_iInter, exists_prop]
    refine exists_congr fun j => ?_
    by_cases hl : (ExplState.run κ b jumps spec (fun i => E i ω) (j + 1)).2.2.2.1 j = none
    · simp only [hl, ne_eq, not_true_eq_false, false_and, and_false, physPiece, ↓reduceIte, mem_empty_iff_false,
        exists_false]
    · obtain ⟨F, hFc, hFe, hFt⟩ := exists_physPiece_path spec (fun i => E i ω) hD hl
      rw [hFe]
      refine and_congr_right fun hjn => ?_
      have hSf := stop_ne_top_of_not_done spec (fun i => E i ω) hjn hl hnd
      have hFmF : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) ≤ min (instrTime spec j) (E j ω).2 → Fm j τ ω = F τ := fun τ hτ => by
        have h1 := hFt τ hτ
        have h2 : (fun m => tipApprox κ b jumps spec (fun i => E i ω) j τ m) = fun m => Y j τ m ω :=
          funext fun m => hY j τ m ω hω hl
        rw [h2] at h1
        exact h1.limUnder_eq
      have hiff := exists_real_lt_iff_qTime hSf hFc q
      simp only [mem_image, mem_ofPred_eq] at hiff ⊢
      constructor
      · rintro ⟨-, r, hrq, hp⟩
        obtain ⟨t, ht, h1, h2⟩ := hiff.2 ⟨r, hrq, fun p => by
          obtain ⟨m, N, hmN, hd⟩ := hp p
          exact ⟨m, N, hmN, by rwa [← hFmF _ hmN]⟩⟩
        exact ⟨F t, ⟨t, ht, rfl⟩, h1, h2⟩
      · rintro ⟨_, ⟨t, ht, rfl⟩, h1, h2⟩
        obtain ⟨r, hrq, hp⟩ := hiff.1 ⟨t, ht, h1, h2⟩
        refine ⟨hl, r, hrq, fun p => ?_⟩
        obtain ⟨m, N, hmN, hd⟩ := hp p
        exact ⟨m, N, hmN, by rwa [hFmF _ hmN]⟩

end InteractingSLE.Theorem14.SB.Lv
