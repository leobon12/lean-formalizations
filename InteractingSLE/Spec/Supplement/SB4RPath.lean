/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OwnHistoryPath
import InteractingSLE.Spec.Supplement.SB4RFrame

/-!
# SB4's retained upper history is a path from `0`, adherent to its interior points

Packet PROVE-T14-SB4LEAF. SB4's sewing frame reads the retained upper history `A = upperPrefix … k`
(the schedule history from the upper seed `u ≤ 0` through `k` instructions, with the bridge `[u, 0]`) as `p([0, 1])`
for a continuous path from `0` in `closure ℍ`. PROVE-T14-SB7's `OwnHistoryPath.exists_path_schedule` proves this for
the seed `0`; here the same induction is run from any seed `x₀`, with one more invariant: every point of the history
off its seed is a limit of its points in `ℍ` (a generating trace spends no time interval on `ℝ`,
`IsGeneratingTrace.exists_mem_H`, "a nontrivial real subarc would have zero capacity", p. 530).

* `mem_closure_times_H`, `mem_closure_image_inter_H` (a generating trace is adherent to its interior times);
* **`exists_path_schedule_seed`** (deterministic);
* **`exists_path_upperPrefix`**: the bridge followed by the schedule path; the history lies in the closure of its
  points in `ℍ` together with the bridge.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Lf

open Exist Exist.Staged Exist.StagedLaw GW2Schedule GW1P CounterflowRange OwnHistoryPath

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-! ### Interior times of a generating trace -/

/-- **Every time of a stopped generating trace is adherent to its interior times.** -/
theorem mem_closure_times_H {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {S : ℝ≥0} (hST : (S : ℝ≥0∞) ≤ T)
    (hS0 : 0 < S) {t : ℝ≥0} (htS : t ≤ S) : t ∈ closure {s : ℝ≥0 | s ≤ S ∧ η s ∈ H} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set d : ℝ≥0 := min ⟨ε / 2, by linarith⟩ S with hd
  have hd0 : 0 < d := lt_min (by show (0 : ℝ) < ε / 2; linarith) hS0
  have hdε : (d : ℝ) ≤ ε / 2 := by
    have : d ≤ ⟨ε / 2, by linarith⟩ := min_le_left _ _
    exact_mod_cast this
  have hdS : d ≤ S := min_le_right _ _
  rcases htS.lt_or_eq with htS' | rfl
  · obtain ⟨s, ⟨hts, hsb⟩, hsH⟩ := Restart.IsGeneratingTrace.exists_mem_H hη hw hw0 (a := t) (b := min (t + d) S)
      (lt_min (lt_add_of_pos_right t hd0) htS')
      ((ENNReal.coe_le_coe.2 (min_le_right _ _)).trans hST)
    refine ⟨s, ⟨(lt_of_lt_of_le hsb (min_le_right _ _)).le, hsH⟩, ?_⟩
    have h1 : s < t + d := lt_of_lt_of_le hsb (min_le_left _ _)
    have h2 : (t : ℝ) < s := by exact_mod_cast hts
    have h3 : (s : ℝ) < t + d := by exact_mod_cast h1
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  · obtain ⟨s, ⟨hts, hsb⟩, hsH⟩ := Restart.IsGeneratingTrace.exists_mem_H hη hw hw0 (a := t - d) (b := t)
      (tsub_lt_self hS0 hd0) hST
    refine ⟨s, ⟨hsb.le, hsH⟩, ?_⟩
    have h1 : ((t - d : ℝ≥0) : ℝ) = t - d := NNReal.coe_sub hdS
    have h2 : ((t - d : ℝ≥0) : ℝ) < s := by exact_mod_cast hts
    have h3 : (s : ℝ) < t := by exact_mod_cast hsb
    rw [NNReal.dist_eq, abs_of_pos (by linarith)]
    linarith

/-- **The image of a stopped generating trace under a boundary map is adherent to its points in `ℍ`.** -/
theorem mem_closure_image_inter_H {w : ℝ≥0 → ℝ} {T : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w T η)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T}) (hw0 : w 0 = 0) {S : ℝ≥0} (hST : (S : ℝ≥0∞) ≤ T)
    (hS0 : 0 < S) {f : ℂ → ℂ} (hfc : ContinuousOn (fun t => f (η t)) {t : ℝ≥0 | t ≤ S})
    (hfH : MapsTo f H H) {t : ℝ≥0} (htS : t ≤ S) :
    f (η t) ∈ closure ((fun t => f (η t)) '' {t : ℝ≥0 | t ≤ S} ∩ H) := by
  have hcl := mem_closure_times_H hη hw hw0 hST hS0 htS
  have hc : ContinuousWithinAt (fun t => f (η t)) {s : ℝ≥0 | s ≤ S ∧ η s ∈ H} t :=
    (hfc t htS).mono fun s hs => hs.1
  refine closure_minimal ?_ isClosed_closure (hc.mem_closure_image hcl)
  rintro _ ⟨s, hs, rfl⟩
  exact subset_closure ⟨⟨s, hs.1, rfl⟩, hfH hs.2⟩

/-! ### Schedules from any seed -/

/-- The schedule history from the seed `x₀`. -/
abbrev sspec (x₀ : ℝ) (l : List (ℝ × ℝ≥0)) : ExplSpec := (x₀, true, scheduleProgram 0 l)

theorem run_succ_sspec (x₀ : ℝ) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length) :
    ExplState.run κ b jumps (sspec x₀ l) D (k + 1) = ExplState.flowStep κ b true
      (ExplState.run κ b jumps (sspec x₀ l) D k) k (D k) (schedAngle l k) (schedDelta 0 l k) := by
  have hins : (sspec x₀ l).2.2[k]? = some (Sum.inl (schedAngle l k, schedDelta 0 l k)) :=
    isFlowProg_scheduleProgram 0 l k hk
  rw [run_succ, hins]
  rfl

theorem run_succ_sspec_of_le (x₀ : ℝ) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : (scheduleProgram 0 l).length ≤ k) :
    ExplState.run κ b jumps (sspec x₀ l) D (k + 1) = ExplState.run κ b jumps (sspec x₀ l) D k := by
  have hins : (sspec x₀ l).2.2[k]? = none := List.getElem?_eq_none hk
  rw [run_succ, hins]

theorem instrTime_sspec (x₀ : ℝ) (l : List (ℝ × ℝ≥0)) {k : ℕ} (hk : k < (scheduleProgram 0 l).length) :
    instrTime (sspec x₀ l) k = schedDelta 0 l k := by
  unfold instrTime
  rw [isFlowProg_scheduleProgram 0 l k hk]

theorem prefixPhysSet_succ_of_allSucc_sspec (x₀ : ℝ) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k < (scheduleProgram 0 l).length) (hs : AllSucc (schedDelta 0 l) D k) :
    SB.prefixPhysSet κ b jumps (sspec x₀ l) D (k + 1) = SB.prefixPhysSet κ b jumps (sspec x₀ l) D k ∪
      (succChart x₀ (schedDelta 0 l) D k).tipSet
        (fun r : ℝ≥0 => (D k).1 (min (r : ℝ≥0∞) (min (schedDelta 0 l k) (D k).2)).toNNReal)
        (min (schedDelta 0 l k) (D k).2) := by
  have h := run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := sspec x₀ l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D k hk.le
  obtain ⟨hlive, hchart⟩ := h.1 hs
  unfold SB.prefixPhysSet
  simp only []
  rw [run_succ_sspec x₀ l D hk, flowStep_of_isLive _ hlive, pieces_launch, arcs_launch]
  have hc : (ExplState.run κ b jumps (sspec x₀ l) D k).2.2.2.2.1 = succChart x₀ (schedDelta 0 l) D k := hchart
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

theorem prefixPhysSet_succ_of_not_allSucc_sspec (x₀ : ℝ) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    {k : ℕ} (hk : k < (scheduleProgram 0 l).length) (hs : ¬ AllSucc (schedDelta 0 l) D k) :
    SB.prefixPhysSet κ b jumps (sspec x₀ l) D (k + 1) = SB.prefixPhysSet κ b jumps (sspec x₀ l) D k := by
  have h := run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := sspec x₀ l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D k hk.le
  obtain ⟨h1, h2⟩ := pieces_arcs_flowStep_of_isStuck (κ := κ) (b := b) _ (h.2 hs) k (D k) (schedAngle l k)
    (schedDelta 0 l k)
  unfold SB.prefixPhysSet
  simp only []
  rw [run_succ_sspec x₀ l D hk, h1, h2]

/-- **The physical set of a schedule run from the seed `x₀` with regular pieces is the range of a path from `x₀`**,
every point of which off the seed is a limit of its points in `ℍ`. -/
theorem exists_path_schedule_seed (x₀ : ℝ) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (sspec x₀ l) D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime (sspec x₀ l) k) (D k).2)) :
    ∀ k : ℕ, ∃ (x : ℂ) (Γ : Path (x₀ : ℂ) x), range Γ = SB.prefixPhysSet κ b jumps (sspec x₀ l) D k ∧
      (∀ z ∈ range Γ, 0 ≤ z.im) ∧ range Γ ⊆ closure (range Γ ∩ H) ∪ {(x₀ : ℂ)} ∧
      (k ≤ (scheduleProgram 0 l).length → AllSucc (schedDelta 0 l) D k →
        (∀ z ∈ H, (succChart x₀ (schedDelta 0 l) D k).2.1 z ∈ H) ∧
        Tendsto (fun y : ℝ => (succChart x₀ (schedDelta 0 l) D k).2.1 ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 x)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨x₀, Path.refl _, ?_, ?_, ?_, fun _ _ => ⟨fun z hz => ?_, ?_⟩⟩
    · rw [Path.refl_range]
      unfold SB.prefixPhysSet
      simp [ExplState.run, ExplState.init]
    · intro z hz
      rw [Path.refl_range, mem_singleton_iff] at hz
      rw [hz, Complex.ofReal_im]
    · rw [Path.refl_range]
      exact subset_union_right
    · change (Chart.id.recenter x₀).2.1 z ∈ H
      simpa [InteractingSLE.Chart.recenter, InteractingSLE.Chart.id] using
        (Lw.add_real_mem_H_iff x₀).2 hz
    · change Tendsto (fun y : ℝ => (Chart.id.recenter x₀).2.1 ((y : ℂ) * I)) (𝓝[>] 0) (𝓝 (x₀ : ℂ))
      simp only [InteractingSLE.Chart.recenter, InteractingSLE.Chart.id]
      have h := (tendsto_mul_I_nhdsWithin_H.mono_right nhdsWithin_le_nhds).add_const (x₀ : ℂ)
      simpa using h
  | succ k ih =>
  obtain ⟨x, Γ, hrange, him, hcl, hlim⟩ := ih
  by_cases hk : k < (scheduleProgram 0 l).length
  swap
  · refine ⟨x, Γ, ?_, him, hcl, fun hk' => absurd hk' (by omega)⟩
    rw [hrange]
    unfold SB.prefixPhysSet
    simp only []
    rw [run_succ_sspec_of_le x₀ l D (not_lt.1 hk)]
  by_cases hs : AllSucc (schedDelta 0 l) D k
  swap
  · refine ⟨x, Γ, ?_, him, hcl, fun _ hs' => absurd (hs'.mono (Nat.le_succ k)) hs⟩
    rw [hrange, prefixPhysSet_succ_of_not_allSucc_sspec x₀ l D hk hs]
  obtain ⟨hmaps, hx⟩ := hlim hk.le hs
  have hrun := run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := sspec x₀ l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D k hk.le
  have hl := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) (spec := sspec x₀ l) rfl
    (isFlowProg_scheduleProgram 0 l) (schedDelta_ne_top 0 l) D hk).1 hs
  have hr := hreg k _ _ hl
  rw [instrTime_sspec x₀ l hk] at hr
  have hstop := hr.continuous_stoppedReal
  have hSne : min (schedDelta 0 l k) (D k).2 ≠ ⊤ :=
    ne_top_of_le_ne_top (schedDelta_ne_top 0 l k) (min_le_left _ _)
  have h3 : (ExplState.run κ b jumps (sspec x₀ l) D k).2.2.2.2.1 = succChart x₀ (schedDelta 0 l) D k :=
    (hrun.1 hs).2
  have hgood : HasProperBdryExt (succChart x₀ (schedDelta 0 l) D k) := by
    have h1 := (isClosed_pieces_run (κ := κ) (b := b) (jumps := jumps) (sspec x₀ l) D hreg k).1
    rwa [h3] at h1
  have hconf : (succChart x₀ (schedDelta 0 l) D k).IsConformal := by
    have := (GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) (sspec x₀ l) D k
      fun j _ c θ h => hreg j c θ h).1
    rwa [h3] at this
  obtain ⟨f, C, hf, -⟩ := hgood
  obtain ⟨hW0, hWc, α, hα, -⟩ := hr
  set S := min (schedDelta 0 l k) (D k).2 with hSdef
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → α t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S)) hW0 ht
  have hfc : ContinuousOn f Hbar := continuousOn_of_tendsto hf
  have hfeq : EqOn f (succChart x₀ (schedDelta 0 l) D k).2.1 H := eqOn_readout hconf hf
  have hfH : MapsTo f H H := fun z hz => by rw [hfeq hz]; exact hmaps z hz
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
  have hfHbar : ∀ p ∈ Hbar, 0 ≤ (f p).im := fun p hp => by
    have := neBot_nhdsWithin_H hp
    exact ge_of_tendsto ((Complex.continuous_im.tendsto _).comp (hf p hp))
      (eventually_nhdsWithin_of_forall fun z hz => le_of_lt (hmaps z hz))
  -- the new points are adherent to the new interior points (or are the old end point)
  have hγcl : range γ ⊆ closure (range (Γ.trans γ) ∩ H) ∪ {(x₀ : ℂ)} := by
    rw [hγrange]
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have htT : t ≤ T := by rw [← ENNReal.coe_le_coe, hTS]; exact ht
    rcases eq_or_ne T 0 with hT0 | hT0
    · have ht0 : t = 0 := le_antisymm (hT0 ▸ htT) (zero_le (a := t))
      rw [ht0, hα.1, hx0]
      have hxΓ : x ∈ range Γ := ⟨1, Γ.target⟩
      rcases hcl hxΓ with h | h
      · exact Or.inl (closure_mono (inter_subset_inter_left _
          (by rw [Path.trans_range]; exact subset_union_left)) h)
      · exact Or.inr h
    · have hTpos : 0 < T := pos_iff_ne_zero.2 hT0
      have hfαc : ContinuousOn (fun t => f (α t)) {t : ℝ≥0 | t ≤ T} := by
        refine hfc.comp (hα.2.1.mono fun s (hs : s ≤ T) => ?_) fun s (hs : s ≤ T) => hαH s ?_
        · show (s : ℝ≥0∞) ≤ S; rw [← hTS]; exact ENNReal.coe_le_coe.2 hs
        · rw [← hTS]; exact ENNReal.coe_le_coe.2 hs
      have hmem := mem_closure_image_inter_H hα (hWc.mono fun _ (hs : _ < S) => (le_of_lt hs : _ ≤ S))
        hW0 hTS.le hTpos hfαc hfH htT
      refine Or.inl (closure_mono (inter_subset_inter_left _ ?_) hmem)
      rintro _ ⟨s, hs, rfl⟩
      rw [Path.trans_range, hγrange]
      exact Or.inr ⟨α s, ⟨s, show (s : ℝ≥0∞) ≤ S by rw [← hTS]; exact ENNReal.coe_le_coe.2 hs, rfl⟩, rfl⟩
  refine ⟨f (α T), Γ.trans γ, ?_, ?_, ?_, fun _ _ => ⟨fun z hz => ?_, ?_⟩⟩
  · rw [Path.trans_range, hrange, hγrange, ← htip, prefixPhysSet_succ_of_allSucc_sspec x₀ l D hk hs]
  · intro z hz
    rw [Path.trans_range] at hz
    rcases hz with hz | hz
    · exact him z hz
    · rw [hγrange] at hz
      obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := hz
      exact hfHbar _ (hαH t ht)
  · intro z hz
    rw [Path.trans_range] at hz
    rcases hz with hz | hz
    · rcases hcl hz with h | h
      · exact Or.inl (closure_mono (inter_subset_inter_left _
          (by rw [Path.trans_range]; exact subset_union_left)) h)
      · exact Or.inr h
    · exact hγcl hz
  · change (succChart x₀ (schedDelta 0 l) D k).2.1
      (fwdMapInv (stopDrv (schedDelta 0 l k) (D k)) (stopTime (schedDelta 0 l k) (D k)) z) ∈ H
    exact hmaps _ (QuantumZipper.RS.fwdMapInv_mem_H hstop.1 hstop.2 (NNReal.coe_nonneg _) hz)
  · change Tendsto (fun y : ℝ => (succChart x₀ (schedDelta 0 l) D k).2.1
      (fwdMapInv (stopDrv (schedDelta 0 l k) (D k)) (stopTime (schedDelta 0 l k) (D k)) ((y : ℂ) * I)))
      (𝓝[>] 0) (𝓝 (f (α T)))
    exact tendsto_tip_stopped_of_tendsto hα hWc hW0 (t := T) hTS.le (hf _ (hαH T hTS.le))

/-- **The retained upper history is a path from `0`**: the bridge `[u, 0]` run from `0` to `u`, followed by the
schedule path from `u`. Every point of the history off the bridge is a limit of its points in `ℍ`. -/
theorem exists_path_upperPrefix {u : ℝ} (hu : u ≤ 0) (l : List (ℝ × ℝ≥0)) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (sspec u l) D (k + 1)).2.2.2.1 k = some (c, θ) →
      PieceRegular (D k).1 (min (instrTime (sspec u l) k) (D k).2)) (k : ℕ) :
    ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
      p '' Icc 0 1 = SB.prefixPhysSet κ b jumps (sspec u l) D k ∪ ((↑) : ℝ → ℂ) '' Icc u 0 ∧
      SB.prefixPhysSet κ b jumps (sspec u l) D k ⊆
        closure (SB.prefixPhysSet κ b jumps (sspec u l) D k ∩ H) ∪ ((↑) : ℝ → ℂ) '' Icc u 0 := by
  obtain ⟨x, Γ, hrange, him, hcl, -⟩ := exists_path_schedule_seed (κ := κ) (b := b) (jumps := jumps) u l D hreg k
  -- the bridge from `0` to `u`
  let B : Path (0 : ℂ) (u : ℂ) :=
    { toFun := fun s => (((s : ℝ) * u : ℝ) : ℂ)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hBrange : range B = ((↑) : ℝ → ℂ) '' Icc u 0 := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨(s : ℝ) * u, ⟨?_, ?_⟩, rfl⟩
      · nlinarith [s.2.1, s.2.2]
      · nlinarith [s.2.1, s.2.2]
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      rcases hu.lt_or_eq with hu' | rfl
      · refine ⟨⟨y / u, div_nonneg_of_nonpos hy2 hu'.le, ?_⟩, ?_⟩
        · rw [div_le_one_of_neg hu']; exact hy1
        · change (((y / u) * u : ℝ) : ℂ) = (y : ℂ)
          rw [div_mul_cancel₀ _ hu'.ne]
      · have : y = 0 := le_antisymm hy2 hy1
        exact ⟨0, by simp [B, this]⟩
  set P : Path (0 : ℂ) x := B.trans Γ with hP
  have himg : P.extend '' Icc 0 1 = range P := P.image_extend_of_subset subset_rfl
  have hPrange : range P = SB.prefixPhysSet κ b jumps (sspec u l) D k ∪ ((↑) : ℝ → ℂ) '' Icc u 0 := by
    rw [hP, Path.trans_range, hBrange, hrange, union_comm]
  have hu0 : (u : ℂ) ∈ ((↑) : ℝ → ℂ) '' Icc u 0 := ⟨u, ⟨le_rfl, hu⟩, rfl⟩
  refine ⟨P.extend, P.continuous_extend.continuousOn, P.extend_zero, fun s hs => ?_, by rw [himg, hPrange],
    fun z hz => ?_⟩
  · have hz : P.extend s ∈ range P := himg ▸ mem_image_of_mem _ hs
    rw [hPrange] at hz
    rcases hz with hz | ⟨y, -, hy⟩
    · exact him _ (hrange ▸ hz)
    · rw [← hy]; simp
  · rw [← hrange] at hz
    rcases hcl hz with h | h
    · exact Or.inl (hrange ▸ h)
    · rw [mem_singleton_iff] at h
      exact Or.inr (h ▸ hu0)

end InteractingSLE.Theorem14.SB.Lf
