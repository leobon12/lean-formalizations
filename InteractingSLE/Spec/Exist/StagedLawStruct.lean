/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLawStmt

/-!
# The staged conditional law: the structure of a run between two launches

Packet PROVE-STAGEDLAW. Between two launched ordinary pieces a staged history only performs boundary continuations and
unavailable switches, which recentre the chart on the original boundary and never use a driver (GW1, p. 620: "The arc
adds no new field reveal"; GW2a). A launch after the first instruction is therefore preceded by a last launch `ℓ`, whose
piece stopped at a finite time, and the current chart is the chart right after piece `ℓ`, recentred.

## Main results

* `flowStep_trichotomy`, `contStep_cases`: a step keeps the state, kills it, launches, or moves along the boundary;
* `IsTerminal`, `isTerminal_step`: a done or dead history stays so and never launches;
* `eq_launch_of_launches`: a recorded launch is the launch of the current state in the current chart;
* `chart_run_succ_of_noLaunch`: a step without launch recentres the chart;
* **`exists_last_launch`**: the decomposition at the last launch;
* `retained_run_succ_self`: the record of index `k` after step `k`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open Staged

/-! ### Charts -/

theorem Chart.recenter_zero (c : Chart) : c.recenter 0 = c := by
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun z => ?_) rfl)
  · simp [Chart.recenter]
  · simp [Chart.recenter]

theorem Chart.recenter_recenter (c : Chart) (a a' : ℝ) : (c.recenter a).recenter a' = c.recenter (a + a') := by
  refine Prod.ext (funext fun z => ?_) (Prod.ext (funext fun z => ?_) rfl)
  · simp only [Chart.recenter, Complex.ofReal_add]
    ring
  · simp only [Chart.recenter, Complex.ofReal_add]
    ring_nf

/-! ### The kinds of steps -/

/-- The state `s` with status *dead*. -/
def setDead (s : ExplState) : ExplState :=
  (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, .inr (.inr (.inr (.inr (.inr ())))), s.2.2.2.2.2.2)

/-- A done or dead history. -/
def IsTerminal (s : ExplState) : Prop :=
  s.2.2.2.2.2.1 = .inr (.inr (.inr (.inr (.inl ())))) ∨ s.2.2.2.2.2.1 = .inr (.inr (.inr (.inr (.inr ()))))

theorem isTerminal_setDead (s : ExplState) : IsTerminal (setDead s) := Or.inr rfl

section Steps

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A flow step keeps the state, kills it, or launches.** -/
theorem flowStep_trichotomy (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ b gw2 s k D θ t = s ∨ ExplState.flowStep κ b gw2 s k D θ t = setDead s ∨
      ExplState.flowStep κ b gw2 s k D θ t = ExplState.launch s k D θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  rcases status with u | u | o | bb | u | u
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inr rfl)
  · split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
  · split_ifs
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- **A continuation step keeps the state, kills it, moves along the boundary, or follows it to the end.** -/
theorem contStep_cases (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    ExplState.contStep κ b jumps s vStop pref = s ∨ ExplState.contStep κ b jumps s vStop pref = setDead s ∨
      (∃ (right : Bool) (x : ℝ) (atMark : Bool),
        ExplState.contStep κ b jumps s vStop pref = ExplState.moveAlong s right x atMark) ∨
      ∃ right : Bool, ExplState.contStep κ b jumps s vStop pref = ExplState.moveToEnd s right := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.contStep
  dsimp only
  repeat' first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))
    | split

theorem isTerminal_flowStep {gw2 : Bool} {s : ExplState} (hs : IsTerminal s) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞)
    (θ : ℝ) (t : ℝ≥0∞) : ExplState.flowStep κ b gw2 s k D θ t = s := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases hs with hs | hs <;> (change status = _ at hs; subst hs; rfl)

theorem isTerminal_contStep {s : ExplState} (hs : IsTerminal s) (vStop : Option ℝ) (pref : Bool) :
    ExplState.contStep κ b jumps s vStop pref = s ∨ ExplState.contStep κ b jumps s vStop pref = setDead s := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases hs with hs | hs <;> (change status = _ at hs; subst hs)
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **A terminal state stays terminal, keeps its records and its chart.** -/
theorem isTerminal_step {gw2 : Bool} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {s : ExplState} (hs : IsTerminal s) (ik : Instr × ℕ) :
    IsTerminal (ExplState.step κ b jumps gw2 D s ik) ∧
      (ExplState.step κ b jumps gw2 D s ik).2.2.2.1 = s.2.2.2.1 ∧
      (ExplState.step κ b jumps gw2 D s ik).2.2.2.2.1 = s.2.2.2.2.1 := by
  obtain ⟨ins, k⟩ := ik
  unfold ExplState.step
  rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
  · simp only
    rw [isTerminal_flowStep hs]
    exact ⟨hs, rfl, rfl⟩
  · simp only
    rcases isTerminal_contStep (κ := κ) (b := b) (jumps := jumps) hs none pref with h | h <;> rw [h]
    · exact ⟨hs, rfl, rfl⟩
    · exact ⟨isTerminal_setDead s, rfl, rfl⟩
  · simp only
    rcases isTerminal_contStep (κ := κ) (b := b) (jumps := jumps) hs (some v) pref with h | h <;> rw [h]
    · exact ⟨hs, rfl, rfl⟩
    · exact ⟨isTerminal_setDead s, rfl, rfl⟩

/-- A launch for own time `t` whose stop is `⊤` ends the history (*done*). -/
theorem isTerminal_launch_of_top (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞)
    (h : min t D.2 = ⊤) : IsTerminal (ExplState.launch s k D θ t) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  simp only [h, ↓reduceIte]
  exact Or.inl rfl

/-- The chart and the launch record of a launch. -/
theorem chart_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (h : min t D.2 ≠ ⊤) :
    (ExplState.launch s k D θ t).2.2.2.2.1 = s.2.2.2.2.1.loewner
      (fun x : ℝ => D.1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min t D.2)).toNNReal)
      ((min t D.2).toNNReal : ℝ) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  simp only [h, ↓reduceIte]
  repeat' first
    | rfl
    | split

end Steps

/-! ### Runs -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- The own time of instruction `k` (`⊤` if it is not an ordinary piece). -/
def instrTime (spec : ExplSpec) (k : ℕ) : ℝ≥0∞ :=
  match spec.2.2[k]? with
  | some (Sum.inl (_, t)) => t
  | _ => ⊤

/-- **A recorded launch is the launch of the current state, in its chart, for the instruction's own time.** -/
theorem eq_launch_of_launches (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} {c : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)) :
    spec.2.2[k]? = some (Sum.inl (θ, instrTime spec k)) ∧
      ExplState.run κ b jumps spec D (k + 1) =
        ExplState.launch (ExplState.run κ b jumps spec D k) k (D k) θ (instrTime spec k) ∧
      c = (ExplState.run κ b jumps spec D k).2.2.2.2.1 := by
  have h0 := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  rw [run_succ] at h ⊢
  cases hk : spec.2.2[k]? with
  | none => rw [hk] at h; rw [h0] at h; exact absurd h (by simp)
  | some a =>
    rw [hk] at h
    simp only at h ⊢
    rcases a with ⟨θ', t⟩ | pref | ⟨v, pref⟩
    · change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t).2.2.2.1 k =
        some (c, θ) at h
      have ht : instrTime spec k = t := by unfold instrTime; rw [hk]
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t
        with e | e | e
      · rw [e, h0] at h; exact absurd h (by simp)
      · rw [e] at h; change (ExplState.run κ b jumps spec D k).2.2.2.1 k = _ at h
        rw [h0] at h; exact absurd h (by simp)
      · rw [e, launches_launch, Function.update_self] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hc, hθ⟩ := h
        subst hθ
        rw [ht]
        exact ⟨rfl, e, hc.symm⟩
    · change (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) none pref).2.2.2.1 k =
        some (c, θ) at h
      rw [launches_contStep, h0] at h; exact absurd h (by simp)
    · change (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) (some v) pref).2.2.2.1 k =
        some (c, θ) at h
      rw [launches_contStep, h0] at h; exact absurd h (by simp)

/-- **A step without launch recentres the chart.** -/
theorem chart_run_succ_of_noLaunch (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (h : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none) :
    ∃ a : ℝ, (ExplState.run κ b jumps spec D (k + 1)).2.2.2.2.1 =
      (ExplState.run κ b jumps spec D k).2.2.2.2.1.recenter a := by
  rw [run_succ] at h ⊢
  cases hk : spec.2.2[k]? with
  | none => exact ⟨0, (Chart.recenter_zero _).symm⟩
  | some a =>
    rw [hk] at h
    simp only at h ⊢
    rcases a with ⟨θ', t⟩ | pref | ⟨v, pref⟩
    · change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t).2.2.2.1 k = none at h
      change ∃ a : ℝ, (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t).2.2.2.2.1 = _
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t
        with e | e | e
      · rw [e]; exact ⟨0, (Chart.recenter_zero _).symm⟩
      · rw [e]; exact ⟨0, (Chart.recenter_zero _).symm⟩
      · rw [e, launches_launch, Function.update_self] at h; exact absurd h (by simp)
    all_goals
      change ∃ a : ℝ, (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) _ pref).2.2.2.2.1 = _
      rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D k) _ pref
        with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;> rw [e]
      · exact ⟨0, (Chart.recenter_zero _).symm⟩
      · exact ⟨0, (Chart.recenter_zero _).symm⟩
      · exact ⟨_, rfl⟩
      · exact ⟨0, (Chart.recenter_zero _).symm⟩

/-- **Terminal states persist along a run.** -/
theorem isTerminal_run_of_le (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {j : ℕ}
    (hj : IsTerminal (ExplState.run κ b jumps spec D j)) : ∀ n, j ≤ n →
      IsTerminal (ExplState.run κ b jumps spec D n) ∧
        (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n = none := by
  intro n hn
  induction n with
  | zero =>
    have hj0 : j = 0 := Nat.le_zero.1 hn
    subst hj0
    refine ⟨hj, ?_⟩
    rw [run_succ]
    cases spec.2.2[0]? with
    | none => exact launches_run_of_le spec D le_rfl
    | some a =>
      rw [(isTerminal_step hj (a, 0)).2.1]
      exact launches_run_of_le spec D le_rfl
  | succ n ih =>
    have hT : IsTerminal (ExplState.run κ b jumps spec D (n + 1)) := by
      rcases Nat.lt_or_ge j (n + 1) with hlt | hge
      · have := (ih (Nat.lt_succ_iff.1 hlt)).1
        rw [run_succ]
        cases spec.2.2[n]? with
        | none => exact this
        | some a => exact (isTerminal_step this (a, n)).1
      · rw [show n + 1 = j from le_antisymm hge hn]; exact hj
    refine ⟨hT, ?_⟩
    rw [run_succ]
    cases spec.2.2[n + 1]? with
    | none => exact launches_run_of_le spec D le_rfl
    | some a =>
      rw [(isTerminal_step hT (a, n + 1)).2.1]
      exact launches_run_of_le spec D le_rfl

/-- Without any launch, a run is at the root with no instruction yet, or terminal. -/
theorem root_or_terminal_of_noLaunch (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : ∀ j : ℕ,
    (∀ i < j, (ExplState.run κ b jumps spec D (i + 1)).2.2.2.1 i = none) →
    ((ExplState.run κ b jumps spec D j).2.2.2.2.2.1 = .inl () ∧ ∀ i < j, spec.2.2[i]? = none) ∨
      IsTerminal (ExplState.run κ b jumps spec D j)
  | 0, _ => Or.inl ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | j + 1, h => by
    rcases root_or_terminal_of_noLaunch spec D j (fun i hi => h i (Nat.lt_succ_of_lt hi)) with ⟨hr, hn⟩ | hT
    · have hlj := h j (Nat.lt_succ_self j)
      rw [run_succ] at hlj ⊢
      cases hk : spec.2.2[j]? with
      | none =>
        refine Or.inl ⟨hr, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact hn i hi
        · exact hk
      | some a =>
        rw [hk] at hlj
        simp only at hlj ⊢
        right
        set s := ExplState.run κ b jumps spec D j with hs
        obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
        change status = _ at hr
        subst hr
        rcases a with ⟨θ', t⟩ | pref | ⟨v, pref⟩
        · -- a flow at the root launches
          exfalso
          change (ExplState.launch (pieces, arcs, retained, launches, chart, .inl (), pt, angle, recR, recL)
            j (D j) θ' t).2.2.2.1 j = none at hlj
          rw [launches_launch, Function.update_self] at hlj
          exact absurd hlj (by simp)
        · exact Or.inr rfl
        · exact Or.inr rfl
    · right
      rw [run_succ]
      cases spec.2.2[j]? with
      | none => exact hT
      | some a => exact (isTerminal_step hT (a, j)).1

/-- **The decomposition at the last launch.** A launch at `k > 0` is preceded by a last launch `ℓ < k`, whose piece
stopped at a finite time; no instruction strictly between them launches, and the chart at `k` is the chart right after
piece `ℓ`, recentred. -/
theorem exists_last_launch (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} {c : Chart} {θ : ℝ}
    (hk : 0 < k) (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ)) :
    ∃ ℓ < k, (∃ c' θ', (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.1 ℓ = some (c', θ')) ∧
      min (instrTime spec ℓ) (D ℓ).2 ≠ ⊤ ∧
      (∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none) ∧
      ∃ a : ℝ, (ExplState.run κ b jumps spec D k).2.2.2.2.1 =
        (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.2.1.recenter a := by
  classical
  -- a terminal state at `k` cannot launch
  have hnotT : ¬ IsTerminal (ExplState.run κ b jumps spec D k) := fun hT => by
    rw [(isTerminal_run_of_le spec D hT k le_rfl).2] at hl
    exact absurd hl (by simp)
  set S := (Finset.range k).filter fun j => (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none with hS
  have hSne : S.Nonempty := by
    by_contra hne
    have hnone : ∀ i < k, (ExplState.run κ b jumps spec D (i + 1)).2.2.2.1 i = none := fun i hi => by
      by_contra hi'
      exact hne ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, hi'⟩⟩
    rcases root_or_terminal_of_noLaunch spec D k hnone with ⟨-, hn⟩ | hT
    · -- the program is empty
      have h0 := hn 0 hk
      have hk' : spec.2.2[k]? = none := by
        rw [List.getElem?_eq_none_iff] at h0 ⊢
        omega
      rw [run_succ, hk'] at hl
      rw [launches_run_of_le spec D le_rfl] at hl
      exact absurd hl (by simp)
    · exact hnotT hT
  set ℓ := S.max' hSne with hℓ
  have hℓS : ℓ ∈ S := S.max'_mem hSne
  have hℓk : ℓ < k := Finset.mem_range.1 (Finset.mem_filter.1 hℓS).1
  have hℓl : (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.1 ℓ ≠ none := (Finset.mem_filter.1 hℓS).2
  obtain ⟨⟨c', θ'⟩, hc'⟩ := Option.ne_none_iff_exists'.1 hℓl
  have hmax : ∀ j, ℓ < j → j < k → (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = none := by
    intro j hj hjk
    by_contra hj'
    exact absurd (S.le_max' j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hjk, hj'⟩)) (not_le.2 hj)
  refine ⟨ℓ, hℓk, ⟨c', θ', hc'⟩, ?_, hmax, ?_⟩
  · -- a piece stopped at `⊤` ends the history
    intro htop
    obtain ⟨-, hrun, -⟩ := eq_launch_of_launches spec D hc'
    have hT : IsTerminal (ExplState.run κ b jumps spec D (ℓ + 1)) := by
      rw [hrun]; exact isTerminal_launch_of_top _ _ _ _ _ htop
    exact hnotT (isTerminal_run_of_le spec D hT k hℓk).1
  · -- recentrings between the launches
    have key : ∀ n, ℓ + 1 + n ≤ k → ∃ a : ℝ, (ExplState.run κ b jumps spec D (ℓ + 1 + n)).2.2.2.2.1 =
        (ExplState.run κ b jumps spec D (ℓ + 1)).2.2.2.2.1.recenter a := by
      intro n
      induction n with
      | zero => intro _; exact ⟨0, (Chart.recenter_zero _).symm⟩
      | succ n ih =>
        intro hn
        obtain ⟨a, ha⟩ := ih (by omega)
        obtain ⟨a', ha'⟩ := chart_run_succ_of_noLaunch spec D (hmax (ℓ + 1 + n) (by omega) (by omega))
        refine ⟨a + a', ?_⟩
        rw [show ℓ + 1 + (n + 1) = ℓ + 1 + n + 1 by ring, ha', ha, Chart.recenter_recenter]
    obtain ⟨a, ha⟩ := key (k - (ℓ + 1)) (by omega)
    rw [show ℓ + 1 + (k - (ℓ + 1)) = k by omega] at ha
    exact ⟨a, ha⟩

theorem retained_run_of_le (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n k : ℕ} (hnk : n ≤ k) :
    (ExplState.run κ b jumps spec D n).2.2.1 k = (fun _ => 0, 0, false) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ]
    cases spec.2.2[n]? with
    | none => exact ih (Nat.le_of_succ_le hnk)
    | some a =>
      rw [retained_step_of_ne _ _ _ _ (Nat.ne_of_gt (Nat.lt_of_succ_le hnk))]
      exact ih (Nat.le_of_succ_le hnk)

/-- The record of index `k` after step `k`: the launched piece's retained datum, or the initial datum. -/
theorem retained_run_succ_self (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.1 k =
      if (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = none then (fun _ => 0, 0, false)
      else retOf (instrTime spec k) (D k) := by
  have h0 := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  have r0 := retained_run_of_le (κ := κ) (b := b) (jumps := jumps) spec D (le_refl k)
  rw [run_succ]
  cases hk : spec.2.2[k]? with
  | none => simp only [h0, r0, ↓reduceIte]
  | some a =>
    simp only
    rcases a with ⟨θ', t⟩ | pref | ⟨v, pref⟩
    · have ht : instrTime spec k = t := by unfold instrTime; rw [hk]
      change (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t).2.2.1 k =
        if (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t).2.2.2.1 k = none
        then _ else _
      rcases flowStep_trichotomy (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ' t
        with e | e | e <;> rw [e]
      · simp only [h0, r0, ↓reduceIte]
      · change (ExplState.run κ b jumps spec D k).2.2.1 k =
          if (ExplState.run κ b jumps spec D k).2.2.2.1 k = none then _ else _
        simp only [h0, r0, ↓reduceIte]
      · rw [launches_launch, Function.update_self, retained_launch, Function.update_self, ht]
        simp only [reduceCtorEq, ↓reduceIte, retOf]
    all_goals
      change (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) _ pref).2.2.1 k =
        if (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D k) _ pref).2.2.2.1 k = none
        then _ else _
      rw [retained_contStep, launches_contStep, h0, r0]
      simp only [↓reduceIte]

end Run

end StagedLaw

end Exist

end InteractingSLE
