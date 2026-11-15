/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedAssembly

/-!
# The staged conditional law: the run is read from the retained past

Packet PROVE-STAGEDLAW. The state of a staged history after `k` instructions (`ExplState.run`) uses the driver of a
launched piece only through its retained datum: the stopped driver, the stop time and the threshold flag
(`ExplState.launch`). For drivers that are regular at every sample (`IsRegularDriver`), the stopped driver is determined
by its values at rational times. Hence the whole state after `k` instructions is a function of the retained past
`pastMap … k` (GW1, p. 620: "Stage boundaries and marks can be recovered from the oriented curve and the original finite
height word … the successive charts are determined by its range with this orientation and the preceding marked stages").

## Main results

* `canonDrv t D`: the driver with the same retained datum as `D` and lifetime `⊤` unless the threshold was reached;
  **`launch_canonDrv`**: a launch only sees the retained datum;
* `run_canon`: the run is unchanged when every driver is replaced by its canonical driver;
* **`run_eq_of_pastMap_eq`**: for everywhere regular drivers, equal retained pasts give equal states.
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

/-- The canonical driver of a piece run for own time `t`: the stopped driver, with lifetime `⊤` unless the lifetime is
at most `t` (then the lifetime itself). It has the same retained datum as `D` (`ExplState.launch`). -/
def canonDrv (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : (ℝ≥0 → ℝ) × ℝ≥0∞ :=
  (fun r => D.1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal, if D.2 ≤ t then D.2 else ⊤)

theorem min_canonDrv (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : min t (canonDrv t D).2 = min t D.2 := by
  unfold canonDrv
  split_ifs with h
  · rfl
  · rw [min_top_right, min_eq_left (not_le.1 h).le]

theorem stopped_canonDrv (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (r : ℝ≥0) :
    (canonDrv t D).1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal = D.1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal := by
  change D.1 (min ((min (r : ℝ≥0∞) (min t D.2)).toNNReal : ℝ≥0∞) (min t D.2)).toNNReal = _
  by_cases hs : min t D.2 = ⊤
  · rw [hs, min_top_right, min_top_right, ENNReal.toNNReal_coe]
  · have hlt : min (r : ℝ≥0∞) (min t D.2) ≠ ⊤ := ne_top_of_le_ne_top hs (min_le_right _ _)
    rw [ENNReal.coe_toNNReal hlt, min_assoc, min_self]

theorem lt_canonDrv_iff (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : t < (canonDrv t D).2 ↔ t < D.2 := by
  unfold canonDrv
  split_ifs with h
  · rfl
  · have h' : t < D.2 := not_le.1 h
    exact ⟨fun _ => h', fun _ => lt_of_lt_of_le h' le_top⟩

theorem canonDrv_eq_zero_iff (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : (canonDrv t D).2 = 0 ↔ D.2 = 0 := by
  unfold canonDrv
  split_ifs with h
  · rfl
  · have h' : t < D.2 := not_le.1 h
    exact ⟨fun h0 => absurd h0 ENNReal.top_ne_zero, fun h0 => absurd (h0 ▸ h') ENNReal.not_lt_zero⟩

theorem canonDrv_le_iff (t : ℝ≥0∞) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) : (canonDrv t D).2 ≤ t ↔ D.2 ≤ t := by
  unfold canonDrv
  split_ifs with h
  · rfl
  · have h' : t < D.2 := not_le.1 h
    exact ⟨fun h1 => absurd (lt_of_lt_of_le h' le_top) (not_lt.2 h1), fun h1 => absurd h1 h⟩

/-- **A launch only sees the retained datum of its driver.** -/
theorem launch_canonDrv (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.launch s k (canonDrv t D) θ t = ExplState.launch s k D θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  have hs := min_canonDrv t D
  have hW := stopped_canonDrv t D
  have hl := lt_canonDrv_iff t D
  have h0 := canonDrv_eq_zero_iff t D
  have hf : decide ((canonDrv t D).2 ≤ t) = decide (D.2 ≤ t) := decide_eq_decide.2 (canonDrv_le_iff t D)
  unfold ExplState.launch
  simp only [hs, hW, hf]
  by_cases h1 : t < D.2
  · simp only [h1, hl.2 h1, ↓reduceIte]
  · simp only [h1, mt hl.1 h1, ↓reduceIte]
    by_cases h2 : D.2 = 0
    · simp only [h2, h0.2 h2, ↓reduceIte]
    · simp only [h2, mt h0.1 h2, ↓reduceIte]
      split_ifs <;> simp only [hs, hW] at * <;> first | rfl | contradiction

/-- The retained datum of a launch. -/
theorem retained_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k D θ t).2.2.1 = Function.update s.2.2.1 k
      (fun r => D.1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal, min t D.2, decide (D.2 ≤ t)) := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  split_ifs <;> try rfl
  all_goals (rcases status with _ | _ | _ | _ | _ | _ <;> rfl)

/-- **A flow step either ignores its driver or is a launch.** -/
theorem flowStep_cases {κ : ℝ} {b : ℝ → ℝ} (gw2 : Bool) (s : ExplState) (k : ℕ) (θ : ℝ) (t : ℝ≥0∞) :
    (∀ D D' : (ℝ≥0 → ℝ) × ℝ≥0∞, ExplState.flowStep κ b gw2 s k D θ t = ExplState.flowStep κ b gw2 s k D' θ t) ∨
      ∀ D : (ℝ≥0 → ℝ) × ℝ≥0∞, ExplState.flowStep κ b gw2 s k D θ t = ExplState.launch s k D θ t := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  rcases status with u | u | o | bb | u | u
  · exact Or.inr fun D => rfl
  · exact Or.inr fun D => rfl
  · split_ifs with h1 h2
    · exact Or.inl fun D D' => rfl
    · exact Or.inr fun D => rfl
    · exact Or.inl fun D D' => rfl
  · split_ifs with h1 h2
    · exact Or.inl fun D D' => rfl
    · exact Or.inr fun D => rfl
    · exact Or.inl fun D D' => rfl
  · exact Or.inl fun D D' => rfl
  · exact Or.inl fun D D' => rfl

/-- The retained datum read at rational times (an entry of `pastMap`). -/
def readRec (r : (ℝ≥0 → ℝ) × ℝ≥0∞ × Bool) : (ℚ → ℝ) × ℝ≥0∞ × Bool :=
  ((fun q : ℚ => r.1 (q : ℝ).toNNReal), r.2.1, r.2.2)

theorem denseRange_rat_toNNReal : DenseRange fun q : ℚ => (q : ℝ).toNNReal :=
  ((show Function.Surjective Real.toNNReal from fun x => ⟨(x : ℝ), Real.toNNReal_coe⟩).denseRange.comp
    Rat.denseRange_cast continuous_real_toNNReal :)

/-- **For regular drivers, the retained datum read at rational times determines the canonical driver.** -/
theorem canonDrv_eq_of_readRec_eq {t : ℝ≥0∞} {e e' : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (he' : IsRegularDriver e')
    (h : readRec (fun r => e.1 (min (r : ℝ≥0∞) (min t e.2)).toNNReal, min t e.2, decide (e.2 ≤ t)) =
      readRec (fun r => e'.1 (min (r : ℝ≥0∞) (min t e'.2)).toNNReal, min t e'.2, decide (e'.2 ≤ t))) :
    canonDrv t e = canonDrv t e' := by
  simp only [readRec, Prod.mk.injEq] at h
  obtain ⟨hq, hs, hf⟩ := h
  have hf' : (e.2 ≤ t ↔ e'.2 ≤ t) := by simpa using hf
  refine Prod.ext ?_ ?_
  · -- the stopped drivers agree at rational times, hence everywhere
    funext r
    change e.1 (min (r : ℝ≥0∞) (min t e.2)).toNNReal = e'.1 (min (r : ℝ≥0∞) (min t e'.2)).toNNReal
    rw [← hs]
    set stop := min t e.2 with hstop
    by_cases hr : (r : ℝ≥0∞) < stop
    · rw [min_eq_left hr.le, ENNReal.toNNReal_coe]
      -- `e.1 = e'.1` on `{s | s < stop}`
      set U : Set ℝ≥0 := {s | (s : ℝ≥0∞) < stop} with hU
      have hUo : IsOpen U := isOpen_lt ENNReal.continuous_coe continuous_const
      have hcU : ContinuousOn e.1 U := he.1.mono fun s (hs' : (s : ℝ≥0∞) < stop) =>
        show (s : ℝ≥0∞) < e.2 from lt_of_lt_of_le hs' (min_le_right _ _)
      have hcU' : ContinuousOn e'.1 U := he'.1.mono fun s (hs' : (s : ℝ≥0∞) < stop) =>
        show (s : ℝ≥0∞) < e'.2 from lt_of_lt_of_le hs' (hs.trans_le (min_le_right _ _))
      have heq : EqOn e.1 e'.1 (U ∩ range fun q : ℚ => (q : ℝ).toNNReal) := by
        rintro _ ⟨hsU, q, rfl⟩
        have h1 := congrFun hq q
        have hlt : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < stop := hsU
        rw [min_eq_left hlt.le, ENNReal.toNNReal_coe, ← hs, min_eq_left hlt.le, ENNReal.toNNReal_coe] at h1
        exact h1
      exact (heq.of_subset_closure hcU hcU' inter_subset_left
        (denseRange_rat_toNNReal.open_subset_closure_inter hUo)) hr
    · -- at and after the stop: read the value at a rational time beyond the stop
      have hst : stop ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (not_lt.1 hr)
      obtain ⟨n, hn⟩ := exists_nat_ge stop.toReal
      have hqn : stop ≤ ((((n : ℚ) : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity), ← ENNReal.ofReal_toReal hst]
        exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hn)
      have h1 := congrFun hq (n : ℚ)
      rw [min_eq_right hqn, ← hs, min_eq_right hqn] at h1
      rw [min_eq_right (not_lt.1 hr)]
      exact h1
  · change (if e.2 ≤ t then e.2 else ⊤) = if e'.2 ≤ t then e'.2 else ⊤
    by_cases h1 : e.2 ≤ t
    · have h2 := hf'.1 h1
      simp only [h1, h2, ↓reduceIte]
      rw [min_eq_right h1, min_eq_right h2] at hs
      exact hs
    · simp only [h1, mt hf'.2 h1, ↓reduceIte]

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem retained_contStep (s : ExplState) (vStop : Option ℝ) (pref : Bool) :
    (ExplState.contStep κ b jumps s vStop pref).2.2.1 = s.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.contStep
  dsimp only
  repeat' first
    | rfl
    | split

theorem retained_flowStep_of_ne (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (t : ℝ≥0∞) {i : ℕ} (hi : i ≠ k) : (ExplState.flowStep κ b gw2 s k D θ t).2.2.1 i = s.2.2.1 i := by
  rcases flowStep_cases (κ := κ) (b := b) gw2 s k θ t with hc | hc
  · obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
    unfold ExplState.flowStep
    dsimp only
    rcases status with u | u | o | bb | u | u
    · rw [retained_launch, Function.update_of_ne hi]
    · rw [retained_launch, Function.update_of_ne hi]
    · split_ifs
      · rfl
      · rw [retained_launch, Function.update_of_ne hi]
      · rfl
    · split_ifs
      · rfl
      · rw [retained_launch, Function.update_of_ne hi]
      · rfl
    · rfl
    · rfl
  · rw [hc, retained_launch, Function.update_of_ne hi]

theorem retained_step_of_ne (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (s : ExplState) (ins : Instr) {j i : ℕ}
    (hij : i ≠ j) : (ExplState.step κ b jumps gw2 D s (ins, j)).2.2.1 i = s.2.2.1 i := by
  unfold ExplState.step
  rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
  · exact retained_flowStep_of_ne gw2 s j (D j) θ t hij
  · exact congrFun (retained_contStep s none pref) i
  · exact congrFun (retained_contStep s (some v) pref) i

theorem retained_run_succ_of_lt (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {i k : ℕ} (hi : i < k) :
    (ExplState.run κ b jumps spec D (k + 1)).2.2.1 i = (ExplState.run κ b jumps spec D k).2.2.1 i := by
  rw [Staged.run_succ]
  cases spec.2.2[k]? with
  | none => rfl
  | some a => exact retained_step_of_ne _ _ _ _ (Nat.ne_of_lt hi)

/-- **Equal retained pasts give equal states** (drivers regular at every sample). -/
theorem run_eq_of_readRec_eq (spec : ExplSpec) {D D' : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} : ∀ {k : ℕ},
    (∀ j < k, IsRegularDriver (D j)) → (∀ j < k, IsRegularDriver (D' j)) →
    (∀ i < k, readRec ((ExplState.run κ b jumps spec D k).2.2.1 i) =
      readRec ((ExplState.run κ b jumps spec D' k).2.2.1 i)) →
    ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k
  | 0, _, _, _ => rfl
  | k + 1, hD, hD', h => by
    have ih : ExplState.run κ b jumps spec D k = ExplState.run κ b jumps spec D' k :=
      run_eq_of_readRec_eq spec (fun j hj => hD j (by omega)) (fun j hj => hD' j (by omega)) fun i hi => by
        have := h i (by omega)
        rwa [retained_run_succ_of_lt spec D hi, retained_run_succ_of_lt spec D' hi] at this
    have hk := h k (Nat.lt_succ_self k)
    rw [Staged.run_succ, Staged.run_succ] at hk ⊢
    rw [← ih] at hk ⊢
    cases hins : spec.2.2[k]? with
    | none => rfl
    | some ins =>
      rw [hins] at hk
      rcases ins with ⟨θ, t⟩ | pref | ⟨v, pref⟩
      · change ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t =
          ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D' k) θ t
        change readRec ((ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D k) θ t).2.2.1 k) =
          readRec ((ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D k) k (D' k) θ t).2.2.1 k) at hk
        rcases flowStep_cases (κ := κ) (b := b) spec.2.1 (ExplState.run κ b jumps spec D k) k θ t with hc | hc
        · exact hc _ _
        · rw [hc, hc] at hk ⊢
          rw [retained_launch, retained_launch, Function.update_self, Function.update_self] at hk
          rw [← launch_canonDrv _ _ (D k), ← launch_canonDrv _ _ (D' k),
            canonDrv_eq_of_readRec_eq (hD k (Nat.lt_succ_self k)) (hD' k (Nat.lt_succ_self k)) hk]
      · rfl
      · rfl

end Run

end StagedLaw

end Exist

end InteractingSLE
